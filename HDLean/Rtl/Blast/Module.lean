import HDLean.Rtl.Blast.Cell

/-!
# Bit-blasting modules and hierarchies

The state of a module instance is laid out as bits: registers, then memory
entries, then the sub-instances in order (`encode`). `blastWith` turns one
module into gates given a blaster for the modules it instantiates; `blastModule`
ties the knot over the design, exactly as `Design.sem` does.
-/
namespace HDLean.Rtl.Blast
open Std.Sat Std.Sat.AIG Std.Tactic.BVDecide BVExpr.bitblast BVPred

/-! ## State layout -/

def instMods (m : Module) : List Nat := m.cells.toList.filterMap fun c =>
  match c.op with
  | .inst j _ _ => some j
  | _ => none

def regBits (m : Module) : Nat := (m.regs.toList.map Reg.width).sum
def memBits (m : Module) : Nat := (m.mems.toList.map fun mm => 2 ^ mm.addrWidth * mm.width).sum

def stateBits (d : Design) (k : Nat) : Nat :=
  match d.modules[k]? with
  | some m => regBits m + memBits m + ((instMods m).map fun j => if j < k then stateBits d j else 0).sum
  | none => 0
termination_by k

def bitsOf (w n : Nat) : List Bool := List.ofFn fun i : Fin w => n.testBit i

def regsEnc (m : Module) (st : Store) : List Bool :=
  m.regs.toList.zipIdx.flatMap fun p => bitsOf p.1.width (st.regs.getD p.2 0)

def memEnc (mm : Mem) (arr : Array Nat) : List Bool :=
  (List.range (2 ^ mm.addrWidth)).flatMap fun a => bitsOf mm.width (arr.getD a 0)

def memsEnc (m : Module) (st : Store) : List Bool :=
  m.mems.toList.zipIdx.flatMap fun p => memEnc p.1 (st.mems.getD p.2 #[])

/-- The state bits of an instance of module `k`. -/
def encode (d : Design) (k : Nat) (st : Store) : List Bool :=
  match d.modules[k]? with
  | some m => regsEnc m st ++ memsEnc m st ++
      (instMods m).zipIdx.flatMap fun p => if p.1 < k then encode d p.1 (st.subs.getD p.2 default) else []
  | none => []
termination_by k

/-! ## Gates -/

/-- Atoms `start, ..., start + w - 1`. -/
def atomBits (start : Nat) : Nat → AIG Nat → Bits × AIG Nat
  | 0, aig => (#[], aig)
  | w + 1, aig =>
    let (bs, aig) := atomBits start w aig
    let e := aig.mkAtomCached (start + w)
    (bs.push (Fanin.mk e.ref.gate e.ref.invert), e.aig)

def regAtoms (start : Nat) : List Reg → AIG Nat → Array Bits × AIG Nat
  | [], aig => (#[], aig)
  | r :: rs, aig =>
    let p := atomBits start r.width aig
    let q := regAtoms (start + r.width) rs p.2
    (#[p.1] ++ q.1, q.2)

def entryAtoms (start w : Nat) : Nat → AIG Nat → Array Bits × AIG Nat
  | 0, aig => (#[], aig)
  | n + 1, aig =>
    let p := entryAtoms start w n aig
    let q := atomBits (start + n * w) w p.2
    (p.1.push q.1, q.2)

def memAtoms (start : Nat) : List Mem → AIG Nat → Array (Array Bits) × AIG Nat
  | [], aig => (#[], aig)
  | mm :: ms, aig =>
    let p := entryAtoms start mm.width (2 ^ mm.addrWidth) aig
    let q := memAtoms (start + 2 ^ mm.addrWidth * mm.width) ms p.2
    (#[p.1] ++ q.1, q.2)

/-- Packed instance outputs, first output in the low bits. -/
def packBits : List Bits → Bits
  | [] => #[]
  | b :: bs => concatBits (packBits bs) b

/-- A blaster for the modules a module may instantiate: outputs and next-state bits. -/
abbrev ChildBlaster := Nat → AIG Nat → Array Bits → Nat → Option ((Array Bits × Array Fanin) × AIG Nat)

structure BAcc where
  vals : Array Bits
  next : Array Fanin
  cbase : Nat
  aig : AIG Nat

def blastCells (child : ChildBlaster) (fr : BFrame) : List Cell → BAcc → Option BAcc
  | [], acc => some acc
  | c :: cs, acc =>
    match c.op with
    | .inst j args outs =>
      match child j acc.aig (args.toArray.map fun a => acc.vals.getD a #[]) acc.cbase with
      | some ((couts, cnext), aig) =>
        if couts.toList.map Array.size = outs then
          blastCells child fr cs ⟨acc.vals.push (zextBits (packBits couts.toList) c.width), acc.next ++ cnext,
            acc.cbase + cnext.size, aig⟩
        else none
      | none => none
    | op =>
      match blastOp { fr with vals := acc.vals } c.width op acc.aig with
      | some (bits, aig) => blastCells child fr cs ⟨acc.vals.push bits, acc.next, acc.cbase, aig⟩
      | none => none

/-- Next-state bits of the registers (reset is applied by the node graph). -/
def regsNext (vals : Array Bits) : List Reg → Option (Array Fanin)
  | [] => some #[]
  | r :: rs => do
    let b := vals.getD r.next #[]
    if b.size = r.width then
      let rest ← regsNext vals rs
      pure (b ++ rest)
    else none

/-- One memory entry after the write ports, later ports winning. -/
def entryNext (vals : Array Bits) (aw w idx : Nat) : List WritePort → Bits → AIG Nat → Option (Bits × AIG Nat)
  | [], cur, aig => some (cur, aig)
  | p :: ps, cur, aig => do
    let (e, aig) ← bit2 (w := aw) mkEq (vals.getD p.addr #[]) (constBits aw idx) aig
    let (c, aig) ← gate2 mkAndCached (bitOr (vals.getD p.en #[]) 0 false) (e.getD 0 (fconst false)) aig
    let (cur, aig) ← vite c (vals.getD p.data #[]) cur w aig
    entryNext vals aw w idx ps cur aig

def memNext (vals : Array Bits) (mm : Mem) (entries : Array Bits) : Nat → AIG Nat → Option (Array Fanin × AIG Nat)
  | 0, aig => some (#[], aig)
  | n + 1, aig => do
    let (front, aig) ← memNext vals mm entries n aig
    let (b, aig) ← entryNext vals mm.addrWidth mm.width n mm.writes.toList (entries.getD n #[]) aig
    pure (front ++ b, aig)

def memsNext (vals : Array Bits) : List Mem → List (Array Bits) → AIG Nat → Option (Array Fanin × AIG Nat)
  | mm :: ms, es :: ess, aig => do
    let (b, aig) ← memNext vals mm es (2 ^ mm.addrWidth) aig
    let (rest, aig) ← memsNext vals ms ess aig
    pure (b ++ rest, aig)
  | _, _, aig => some (#[], aig)

/-- One module, given a blaster for its children; `IB` is the number of input atoms. -/
def blastWith (IB : Nat) (child : ChildBlaster) (m : Module) (aig : AIG Nat) (ins : Array Bits) (base : Nat) :
    Option ((Array Bits × Array Fanin) × AIG Nat) :=
  let ra := regAtoms (IB + base) m.regs.toList aig
  let ma := memAtoms (IB + base + regBits m) m.mems.toList ra.2
  let fr : BFrame := ⟨ins, ra.1, ma.1, #[]⟩
  match blastCells child fr m.cells.toList ⟨#[], #[], base + regBits m + memBits m, ma.2⟩ with
  | some acc =>
    match regsNext acc.vals m.regs.toList, memsNext acc.vals m.mems.toList ma.1.toList acc.aig with
    | some rn, some (mn, aig) => some ((m.outputs.map fun o => acc.vals.getD o.node #[], rn ++ mn ++ acc.next), aig)
    | _, _ => none
  | none => none

/-- The children of module `k` are the modules before it. -/
def blastModule (d : Design) (IB : Nat) (k : Nat) (aig : AIG Nat) (ins : Array Bits) (base : Nat) :
    Option ((Array Bits × Array Fanin) × AIG Nat) :=
  match d.modules[k]? with
  | some m => blastWith IB (fun j aig ins base => if j < k then blastModule d IB j aig ins base else none) m aig ins base
  | none => none
termination_by k


/-! ## Layout lemmas -/

@[simp] theorem bitsOf_length (w n : Nat) : (bitsOf w n).length = w := by simp [bitsOf]

theorem bitsOf_get (w n i : Nat) (hi : i < (bitsOf w n).length) : (bitsOf w n)[i] = n.testBit i := by
  simp [bitsOf]

theorem stateBits_eq (d : Design) (k : Nat) (m : Module) (h : d.modules[k]? = some m) :
    stateBits d k = regBits m + memBits m + ((instMods m).map fun j => if j < k then stateBits d j else 0).sum := by
  rw [stateBits]; simp [h]

theorem encode_eq (d : Design) (k : Nat) (m : Module) (h : d.modules[k]? = some m) (st : Store) :
    encode d k st = regsEnc m st ++ memsEnc m st ++
      (instMods m).zipIdx.flatMap fun p => if p.1 < k then encode d p.1 (st.subs.getD p.2 default) else [] := by
  rw [encode]; simp [h]

theorem regsEnc_length (m : Module) (st : Store) : (regsEnc m st).length = regBits m := by
  simp only [regsEnc, regBits, List.length_flatMap, bitsOf_length]
  generalize m.regs.toList = rs
  suffices ∀ n, (List.map (fun p : Reg × Nat => p.1.width) (rs.zipIdx n)).sum = (rs.map Reg.width).sum by
    simpa using this 0
  induction rs with
  | nil => simp
  | cons r rs ih => intro n; simp [List.zipIdx_cons, ih]

theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (w : Nat) (h : ∀ x, (f x).length = w) :
    (l.flatMap f).length = l.length * w := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, h, Nat.succ_mul, Nat.add_comm]

@[simp] theorem memEnc_length (mm : Mem) (arr : Array Nat) : (memEnc mm arr).length = 2 ^ mm.addrWidth * mm.width := by
  rw [memEnc, length_flatMap_const _ _ mm.width (fun _ => bitsOf_length _ _), List.length_range]

theorem memsEnc_length (m : Module) (st : Store) : (memsEnc m st).length = memBits m := by
  simp only [memsEnc, memBits, List.length_flatMap, memEnc_length]
  generalize m.mems.toList = ms
  suffices ∀ n, (List.map (fun p : Mem × Nat => 2 ^ p.1.addrWidth * p.1.width) (ms.zipIdx n)).sum =
      (ms.map fun mm => 2 ^ mm.addrWidth * mm.width).sum by
    simpa using this 0
  induction ms with
  | nil => simp
  | cons r rs ih => intro n; simp [List.zipIdx_cons, ih]

theorem encode_length (d : Design) (k : Nat) (st : Store) : (encode d k st).length = stateBits d k := by
  induction k using Nat.strongRecOn generalizing st with
  | ind k ih =>
    cases hm : d.modules[k]? with
    | none => rw [encode, stateBits]; simp [hm]
    | some m =>
      rw [encode_eq d k m hm, stateBits_eq d k m hm]
      simp only [List.length_append, regsEnc_length, memsEnc_length, List.length_flatMap, Nat.add_assoc]
      congr 2
      generalize instMods m = js
      suffices ∀ n, ((js.zipIdx n).map fun p => (if p.1 < k then encode d p.1 (st.subs.getD p.2 default) else []).length).sum
          = (js.map fun j => if j < k then stateBits d j else 0).sum by simpa using this 0
      induction js with
      | nil => simp
      | cons j js ihj =>
        intro n
        simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, ihj]
        congr 1
        split
        · rename_i hj; exact ih j hj _
        · rfl


/-! ## Atoms -/

theorem atomBits_ok (start : Nat) (assign : Nat → Bool) : ∀ (w : Nat) (aig : AIG Nat),
    IsPrefix aig.decls (atomBits start w aig).2.decls ∧ (atomBits start w aig).1.size = w ∧
      ∀ i (hi : i < (atomBits start w aig).1.size),
        BitIs (atomBits start w aig).2 assign (atomBits start w aig).1[i] (assign (start + i))
  | 0, aig => ⟨IsPrefix.refl' aig, rfl, fun i hi => by simp [atomBits] at hi⟩
  | w + 1, aig => by
    obtain ⟨p, hs, hb⟩ := atomBits_ok start assign w aig
    have pe := LawfulOperator.isPrefix_aig (f := mkAtomCached) (atomBits start w aig).2 (start + w)
    refine ⟨IsPrefix.trans' p pe, by simp [atomBits, hs], fun i hi => ?_⟩
    simp only [atomBits, Array.size_push] at hi ⊢
    rw [Array.getElem_push]
    split
    · rename_i hlt
      exact (hb i hlt).mono pe
    · have hiw : i = w := by omega
      obtain ⟨hb', hd⟩ := entry_bit ((atomBits start w aig).2.mkAtomCached (start + w)) assign
      refine ⟨hb', ?_⟩
      rw [hd, mkAtomCached_eval_eq_mkAtom_eval, denote_mkAtom, hiw]

theorem denotes_of_bits {aig : AIG Nat} {assign : Nat → Bool} (bits : Bits) (n : Nat)
    (h : ∀ i (hi : i < bits.size), BitIs aig assign bits[i] (n.testBit i)) :
    RawDen aig assign bits n := by
  refine ⟨⟨⟨bits, rfl⟩, fun {i} hi => (h i hi).1⟩, rfl, fun idx hidx => ?_⟩
  obtain ⟨hb, hd⟩ := h idx hidx
  show ⟦aig, ⟨bits[idx].gate, bits[idx].invert, _⟩, assign⟧ = _
  rw [hd, bv, BitVec.getLsbD_ofNat]
  simp [hidx]

theorem RawDen.empty (aig : AIG Nat) (assign : Nat → Bool) (n : Nat) : RawDen aig assign #[] n :=
  denotes_of_bits #[] n (fun i hi => by simp at hi)

theorem atom_rawden (start w n : Nat) (assign : Nat → Bool) (aig : AIG Nat)
    (ha : ∀ i, i < w → assign (start + i) = n.testBit i) :
    RawDen (atomBits start w aig).2 assign (atomBits start w aig).1 n ∧ (atomBits start w aig).1.size = w := by
  obtain ⟨_, hs, hb⟩ := atomBits_ok start assign w aig
  refine ⟨denotes_of_bits _ n fun i hi => ?_, hs⟩
  have := hb i hi
  rwa [ha i (by omega)] at this

def encRegs (rs : List Reg) (n : Nat) (st : Store) : List Bool :=
  (rs.zipIdx n).flatMap fun p => bitsOf p.1.width (st.regs.getD p.2 0)

theorem getD_cons_zero {α : Type} (b : α) (bs : Array α) (d : α) : (#[b] ++ bs).getD 0 d = b := by
  simp only [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_append_left (by simp)]
  simp

theorem getD_cons_succ {α : Type} (b : α) (bs : Array α) (i : Nat) (d : α) : (#[b] ++ bs).getD (i + 1) d = bs.getD i d := by
  simp only [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_append_right (by simp)]
  simp

theorem regAtoms_ok (assign : Nat → Bool) (st : Store) : ∀ (rs : List Reg) (n start : Nat) (aig : AIG Nat),
    (∀ i (hi : i < (encRegs rs n st).length), assign (start + i) = (encRegs rs n st)[i]) →
    IsPrefix aig.decls (regAtoms start rs aig).2.decls ∧ (regAtoms start rs aig).1.size = rs.length ∧
      ∀ i (hi : i < rs.length), RawDen (regAtoms start rs aig).2 assign ((regAtoms start rs aig).1.getD i #[])
        (st.regs.getD (n + i) 0) ∧ ((regAtoms start rs aig).1.getD i #[]).size = rs[i].width
  | [], _, _, aig, _ => ⟨IsPrefix.refl' aig, rfl, fun i hi => by simp at hi⟩
  | r :: rs, n, start, aig, ha => by
    have hlen : (bitsOf r.width (st.regs.getD n 0)).length = r.width := bitsOf_length _ _
    have hsplit : encRegs (r :: rs) n st = bitsOf r.width (st.regs.getD n 0) ++ encRegs rs (n + 1) st := by
      simp [encRegs, List.zipIdx_cons]
    have htot : (encRegs (r :: rs) n st).length = r.width + (encRegs rs (n + 1) st).length := by
      rw [hsplit, List.length_append, hlen]
    have ha1 : ∀ i, i < r.width → assign (start + i) = (st.regs.getD n 0).testBit i := by
      intro i hi
      rw [ha i (by omega)]
      simp only [hsplit]
      rw [List.getElem_append_left (by rw [hlen]; exact hi), bitsOf_get]
    have ha2 : ∀ i (hi : i < (encRegs rs (n + 1) st).length),
        assign (start + r.width + i) = (encRegs rs (n + 1) st)[i] := by
      intro i hi
      rw [Nat.add_assoc, ha (r.width + i) (by omega)]
      simp only [hsplit]
      rw [List.getElem_append_right (by rw [hlen]; omega)]
      simp [hlen]
    obtain ⟨d1, s1⟩ := atom_rawden start r.width (st.regs.getD n 0) assign aig ha1
    obtain ⟨p1, -, -⟩ := atomBits_ok start assign r.width aig
    obtain ⟨p2, s2, h2⟩ := regAtoms_ok assign st rs (n + 1) (start + r.width) (atomBits start r.width aig).2 ha2
    refine ⟨IsPrefix.trans' p1 p2, by simp [regAtoms, s2]; omega, fun i hi => ?_⟩
    cases i with
    | zero =>
      simp only [regAtoms, getD_cons_zero, Nat.add_zero, List.getElem_cons_zero]
      exact ⟨d1.mono p2, s1⟩
    | succ i =>
      have hi' : i < rs.length := by simpa using hi
      simp only [regAtoms, getD_cons_succ, List.getElem_cons_succ]
      have := h2 i hi'
      rwa [Nat.add_assoc, Nat.add_comm 1 i] at this


theorem getElem_flatMap_const {α β : Type} (f : α → List β) (w : Nat) (hf : ∀ x, (f x).length = w) :
    ∀ (l : List α) (i j : Nat) (hi : i < l.length) (hj : j < w) (h : i * w + j < (l.flatMap f).length),
      (l.flatMap f)[i * w + j] = (f l[i])[j]'(by rw [hf]; exact hj)
  | [], i, _, hi, _, _ => by simp at hi
  | x :: xs, 0, j, _, hj, _ => by
    simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
    rw [List.getElem_append_left (by rw [hf]; exact hj)]
  | x :: xs, i + 1, j, hi, hj, h => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    have hx := hf x
    rw [List.getElem_append_right (by rw [hx]; rw [Nat.succ_mul]; omega)]
    have hi' : i < xs.length := by simpa using hi
    have := getElem_flatMap_const f w hf xs i j hi' hj (by
      rw [length_flatMap_const _ _ w hf]
      have := Nat.mul_le_mul_right w (show i + 1 ≤ xs.length by omega)
      rw [Nat.succ_mul] at this; omega)
    simp only [hx, Nat.succ_mul, show i * w + w + j - w = i * w + j by omega]
    exact this

theorem memEnc_get (mm : Mem) (arr : Array Nat) (a j : Nat) (ha : a < 2 ^ mm.addrWidth) (hj : j < mm.width)
    (h : a * mm.width + j < (memEnc mm arr).length) :
    (memEnc mm arr)[a * mm.width + j] = (arr.getD a 0).testBit j := by
  have h' : a * mm.width + j < ((List.range (2 ^ mm.addrWidth)).flatMap fun a => bitsOf mm.width (arr.getD a 0)).length := h
  have e := getElem_flatMap_const (fun a => bitsOf mm.width (arr.getD a 0)) mm.width (fun _ => bitsOf_length _ _) _ a j
    (by simpa using ha) hj h'
  simp only [List.getElem_range, bitsOf_get] at e
  exact e

theorem entryAtoms_ok (assign : Nat → Bool) (arr : Array Nat) (start w : Nat) : ∀ (n : Nat) (aig : AIG Nat),
    (∀ a j, a < n → j < w → assign (start + a * w + j) = (arr.getD a 0).testBit j) →
    IsPrefix aig.decls (entryAtoms start w n aig).2.decls ∧ (entryAtoms start w n aig).1.size = n ∧
      ∀ a, a < n → RawDen (entryAtoms start w n aig).2 assign ((entryAtoms start w n aig).1.getD a #[]) (arr.getD a 0) ∧
        ((entryAtoms start w n aig).1.getD a #[]).size = w
  | 0, aig, _ => ⟨IsPrefix.refl' aig, rfl, fun a ha => by omega⟩
  | n + 1, aig, ha => by
    obtain ⟨p1, s1, h1⟩ := entryAtoms_ok assign arr start w n aig (fun a j h1 h2 => ha a j (by omega) h2)
    obtain ⟨d2, s2⟩ := atom_rawden (start + n * w) w (arr.getD n 0) assign (entryAtoms start w n aig).2
      (fun j hj => ha n j (by omega) hj)
    obtain ⟨p2, -, -⟩ := atomBits_ok (start + n * w) assign w (entryAtoms start w n aig).2
    refine ⟨IsPrefix.trans' p1 p2, by simp [entryAtoms, s1], fun a ha' => ?_⟩
    simp only [entryAtoms, Array.getD_eq_getD_getElem?, Array.getElem?_push, s1]
    split
    · rename_i han; subst han
      simp only [Option.getD_some]
      rw [← Array.getD_eq_getD_getElem?]; exact ⟨d2, s2⟩
    · have := h1 a (by omega)
      simp only [Array.getD_eq_getD_getElem?] at this
      exact ⟨this.1.mono p2, this.2⟩

def encMems (ms : List Mem) (n : Nat) (st : Store) : List Bool :=
  (ms.zipIdx n).flatMap fun p => memEnc p.1 (st.mems.getD p.2 #[])

theorem memAtoms_ok (assign : Nat → Bool) (st : Store) : ∀ (ms : List Mem) (n start : Nat) (aig : AIG Nat),
    (∀ i (hi : i < (encMems ms n st).length), assign (start + i) = (encMems ms n st)[i]) →
    IsPrefix aig.decls (memAtoms start ms aig).2.decls ∧ (memAtoms start ms aig).1.size = ms.length ∧
      ∀ mi a, mi < ms.length → a < 2 ^ ms[mi]!.addrWidth →
        RawDen (memAtoms start ms aig).2 assign (((memAtoms start ms aig).1.getD mi #[]).getD a #[])
          ((st.mems.getD (n + mi) #[]).getD a 0) ∧
        (((memAtoms start ms aig).1.getD mi #[]).getD a #[]).size = ms[mi]!.width ∧
        ((memAtoms start ms aig).1.getD mi #[]).size = 2 ^ ms[mi]!.addrWidth
  | [], _, _, aig, _ => ⟨IsPrefix.refl' aig, rfl, fun mi a hmi => by simp at hmi⟩
  | mm :: ms, n, start, aig, ha => by
    have hlen : (memEnc mm (st.mems.getD n #[])).length = 2 ^ mm.addrWidth * mm.width := memEnc_length _ _
    have hsplit : encMems (mm :: ms) n st = memEnc mm (st.mems.getD n #[]) ++ encMems ms (n + 1) st := by
      simp [encMems, List.zipIdx_cons]
    have ha1 : ∀ a j, a < 2 ^ mm.addrWidth → j < mm.width →
        assign (start + a * mm.width + j) = ((st.mems.getD n #[]).getD a 0).testBit j := by
      intro a j h1 h2
      have hb : a * mm.width + j < 2 ^ mm.addrWidth * mm.width := by
        have := Nat.mul_le_mul_right mm.width (show a + 1 ≤ 2 ^ mm.addrWidth by omega)
        rw [Nat.succ_mul] at this; omega
      rw [Nat.add_assoc, ha (a * mm.width + j) (by rw [hsplit]; simp only [List.length_append, hlen]; omega)]
      simp only [hsplit]
      rw [List.getElem_append_left (by rw [hlen]; exact hb)]
      exact memEnc_get mm _ a j h1 h2 _
    have ha2 : ∀ i (hi : i < (encMems ms (n + 1) st).length),
        assign (start + 2 ^ mm.addrWidth * mm.width + i) = (encMems ms (n + 1) st)[i] := by
      intro i hi
      rw [Nat.add_assoc, ha (2 ^ mm.addrWidth * mm.width + i) (by rw [hsplit]; simp only [List.length_append, hlen]; omega)]
      simp only [hsplit]
      rw [List.getElem_append_right (by rw [hlen]; omega)]
      simp [hlen]
    obtain ⟨p1, s1, h1⟩ := entryAtoms_ok assign (st.mems.getD n #[]) start mm.width (2 ^ mm.addrWidth) aig ha1
    obtain ⟨p2, s2, h2⟩ := memAtoms_ok assign st ms (n + 1) (start + 2 ^ mm.addrWidth * mm.width)
      (entryAtoms start mm.width (2 ^ mm.addrWidth) aig).2 ha2
    refine ⟨IsPrefix.trans' p1 p2, by simp [memAtoms, s2]; omega, fun mi a hmi ha' => ?_⟩
    cases mi with
    | zero =>
      simp only [memAtoms, getD_cons_zero, Nat.add_zero]
      simp only [List.getElem!_cons_zero] at ha' ⊢
      have := h1 a ha'
      exact ⟨this.1.mono p2, this.2, s1⟩
    | succ mi =>
      have hmi' : mi < ms.length := by simpa using hmi
      simp only [memAtoms, getD_cons_succ]
      simp only [List.getElem!_cons_succ] at ha' ⊢
      have := h2 mi a hmi' ha'
      rwa [Nat.add_assoc, Nat.add_comm 1 mi] at this

end HDLean.Rtl.Blast
