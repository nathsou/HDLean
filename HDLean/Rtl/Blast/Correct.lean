import HDLean.Rtl.Blast.Module

/-!
# Correctness of module bit-blasting

`blastModule` computes, for an instance of a module, gates for its outputs and
for the encoding of its next store (with reset low; reset is applied per bit
by the node graph, see `Reset.lean`). The statements here say that, when the
input bits denote the input words and the state atoms hold the encoding of a
store, the output bits denote the outputs of `Design.sem` and the next-state
bits are the encoding of the next store.
-/
namespace HDLean.Rtl.Blast
open Std.Sat Std.Sat.AIG Std.Tactic.BVDecide BVExpr.bitblast BVPred

/-! ## Bit lists -/

/-- `bs` denotes the bit list `l`. -/
def BitsAre (aig : AIG Nat) (assign : Nat → Bool) (bs : Bits) (l : List Bool) : Prop :=
  bs.size = l.length ∧ ∀ i (hi : i < bs.size), BitIs aig assign bs[i] (l.getD i false)

theorem BitsAre.mono {aig aig' : AIG Nat} {assign : Nat → Bool} {bs : Bits} {l : List Bool}
    (h : BitsAre aig assign bs l) (hp : IsPrefix aig.decls aig'.decls) : BitsAre aig' assign bs l :=
  ⟨h.1, fun i hi => (h.2 i hi).mono hp⟩

theorem BitsAre.nil (aig : AIG Nat) (assign : Nat → Bool) : BitsAre aig assign #[] [] :=
  ⟨rfl, fun i hi => by simp at hi⟩

theorem BitsAre.append {aig : AIG Nat} {assign : Nat → Bool} {a b : Bits} {l1 l2 : List Bool}
    (h1 : BitsAre aig assign a l1) (h2 : BitsAre aig assign b l2) : BitsAre aig assign (a ++ b) (l1 ++ l2) := by
  refine ⟨by simp [h1.1, h2.1], fun i hi => ?_⟩
  rw [Array.getElem_append]
  split
  · rename_i hlt
    have := h1.2 i hlt
    simp only [List.getD_eq_getElem?_getD] at this ⊢
    rwa [List.getElem?_append_left (by rw [← h1.1]; exact hlt)]
  · rename_i hge
    have := h2.2 (i - a.size) (by simp at hi; omega)
    simp only [List.getD_eq_getElem?_getD] at this ⊢
    rwa [List.getElem?_append_right (by rw [← h1.1]; omega), ← h1.1]

/-- The assignment holds `l` from atom `start` on. -/
def Laid (assign : Nat → Bool) (start : Nat) (l : List Bool) : Prop :=
  ∀ i, i < l.length → assign (start + i) = l.getD i false

theorem Laid.left {assign : Nat → Bool} {start : Nat} {l1 l2 : List Bool} (h : Laid assign start (l1 ++ l2)) :
    Laid assign start l1 := by
  intro i hi
  have := h i (by simp; omega)
  simp only [List.getD_eq_getElem?_getD] at this ⊢
  rwa [List.getElem?_append_left hi] at this

theorem Laid.right {assign : Nat → Bool} {start : Nat} {l1 l2 : List Bool} (h : Laid assign start (l1 ++ l2)) :
    Laid assign (start + l1.length) l2 := by
  intro i hi
  have := h (l1.length + i) (by simp; omega)
  simp only [List.getD_eq_getElem?_getD] at this ⊢
  rwa [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, ← Nat.add_assoc] at this

theorem Laid.get {assign : Nat → Bool} {start : Nat} {l : List Bool} (h : Laid assign start l) :
    ∀ i (hi : i < l.length), assign (start + i) = l[i] := by
  intro i hi
  rw [h i hi]
  simp [List.getD_eq_getElem?_getD, hi]

theorem rawden_bitsAre {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {n : Nat} (h : RawDen aig assign a n) :
    BitsAre aig assign a (bitsOf a.size n) := by
  refine ⟨by simp, fun i hi => ?_⟩
  have := testBit_of_denotes h i hi
  simp only [bitOr, dif_pos hi] at this
  simpa [List.getD_eq_getElem?_getD, bitsOf, hi] using this

theorem bitsOf_bv (w x : Nat) : bitsOf w (bv w x).toNat = bitsOf w x := by
  simp [bitsOf, bv, BitVec.toNat_ofNat]

theorem bitsOf_mod (w x : Nat) : bitsOf w (x % 2 ^ w) = bitsOf w x := by
  simp [bitsOf]

/-! ## Words -/

/-- Cell bits denote cell values, reduced to their width. -/
def ValsOk (aig : AIG Nat) (assign : Nat → Bool) (vals : Array Bits) (V : Array Nat) : Prop :=
  vals.size = V.size ∧ ∀ k, RawDen aig assign (vals.getD k #[]) (V.getD k 0) ∧ V.getD k 0 < 2 ^ (vals.getD k #[]).size

theorem ValsOk.mono {aig aig' : AIG Nat} {assign : Nat → Bool} {vals : Array Bits} {V : Array Nat}
    (h : ValsOk aig assign vals V) (hp : IsPrefix aig.decls aig'.decls) : ValsOk aig' assign vals V :=
  ⟨h.1, fun k => ⟨(h.2 k).1.mono hp, (h.2 k).2⟩⟩

theorem ValsOk.empty (aig : AIG Nat) (assign : Nat → Bool) : ValsOk aig assign #[] #[] :=
  ⟨rfl, fun k => ⟨by simpa using RawDen.empty aig assign 0, by simp⟩⟩

theorem ValsOk.push {aig : AIG Nat} {assign : Nat → Bool} {vals : Array Bits} {V : Array Nat}
    (h : ValsOk aig assign vals V) {b : Bits} {x : Nat} (hb : RawDen aig assign b x) (hx : x < 2 ^ b.size) :
    ValsOk aig assign (vals.push b) (V.push x) := by
  refine ⟨by simp [h.1], fun k => ?_⟩
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, h.1]
  split
  · simpa using ⟨hb, hx⟩
  · have := h.2 k
    simp only [Array.getD_eq_getD_getElem?] at this
    exact this

theorem bit0_ok {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {n : Nat} (h : RawDen aig assign a n)
    (hn : n < 2 ^ a.size) : BitIs aig assign (bitOr a 0 false) (n.testBit 0) := by
  have := bit_of_denotes h 0
  rcases Nat.eq_zero_or_pos a.size with hs | hs
  · rw [hs] at hn this
    have : n = 0 := by simpa using hn
    subst this
    simpa using bit_of_denotes h 0 |>.mono (IsPrefix.refl' aig) |> fun h' => by simpa [hs] using h'
  · rwa [if_pos hs, bv, BitVec.getLsbD_ofNat, decide_eq_true hs, Bool.true_and] at this

theorem beq_bv {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) : (bv w a == bv w b) = decide (a = b) := by
  by_cases hab : a = b
  · subst hab; simp
  · have : bv w a ≠ bv w b := by
      intro h
      apply hab
      have := congrArg BitVec.toNat h
      simpa [bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
    simp [this, hab]

theorem toVec_size {aig : AIG Nat} {bits : Bits} {w : Nat} {rv : RefVec aig w} (h : toVec aig bits w = some rv) :
    bits.size = w := by
  unfold toVec at h
  split at h
  · rename_i hh; exact hh.1
  · cases h

theorem bit2_size {w : Nat} {f : (aig : AIG Nat) → BinaryRefVec aig w → Entrypoint Nat} {a b : Bits} {aig : AIG Nat}
    {r : Bits × AIG Nat} (h : bit2 f a b aig = some r) : a.size = w ∧ b.size = w := by
  unfold bit2 at h
  cases ha : toVec aig a w with
  | none => simp [ha] at h
  | some va =>
    cases hb : toVec aig b w with
    | none => simp [ha, hb] at h
    | some vb => exact ⟨toVec_size ha, toVec_size hb⟩

theorem vite_size {s : Fanin} {a b : Bits} {w : Nat} {aig : AIG Nat} {r : Bits × AIG Nat}
    (h : vite s a b w aig = some r) : a.size = w ∧ b.size = w := by
  unfold vite at h
  split at h
  · cases ha : toVec aig a w with
    | none => simp [ha] at h
    | some va =>
      cases hb : toVec aig b w with
      | none => simp [ha, hb] at h
      | some vb => exact ⟨toVec_size ha, toVec_size hb⟩
  · cases h

/-! ## Registers -/

theorem regsNext_ok {aig : AIG Nat} {assign : Nat → Bool} {vals : Array Bits} {V : Array Nat}
    (hv : ValsOk aig assign vals V) :
    ∀ (rs : List Reg) (out : Bits), regsNext vals rs = some out →
      BitsAre aig assign out (rs.flatMap fun r => bitsOf r.width (V.getD r.next 0))
  | [], out, h => by
    simp only [regsNext, Option.some.injEq] at h; subst h; exact BitsAre.nil _ _
  | r :: rs, out, h => by
    simp only [regsNext] at h
    split at h
    · rename_i hs
      cases hr : regsNext vals rs with
      | none => simp [hr] at h
      | some rest =>
        simp only [hr, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
        subst h
        have := rawden_bitsAre (hv.2 r.next).1
        rw [hs] at this
        exact this.append (regsNext_ok hv rs rest hr)
    · cases h

theorem flatMap_zipIdx_congr {α β : Type} (F G : α → Nat → List β) :
    ∀ (l : List α) (n : Nat), (∀ i (hi : i < l.length), F l[i] (n + i) = G l[i] (n + i)) →
      (l.zipIdx n).flatMap (fun p => F p.1 p.2) = (l.zipIdx n).flatMap (fun p => G p.1 p.2)
  | [], _, _ => rfl
  | x :: xs, n, h => by
    simp only [List.zipIdx_cons, List.flatMap_cons]
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    rw [h0, flatMap_zipIdx_congr F G xs (n + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)]

theorem flatMap_zipIdx_fst {α β : Type} (G : α → List β) :
    ∀ (l : List α) (n : Nat), (l.zipIdx n).flatMap (fun p => G p.1) = l.flatMap G
  | [], _ => rfl
  | x :: xs, n => by simp [List.zipIdx_cons, flatMap_zipIdx_fst G xs (n + 1)]

theorem regsEnc_next (m : Module) (f : Reg → Nat) (mems : Array (Array Nat)) (subs : Array Store) :
    regsEnc m (.mk (m.regs.map f) mems subs) = m.regs.toList.flatMap fun r => bitsOf r.width (f r) := by
  unfold regsEnc
  refine (flatMap_zipIdx_congr (fun r i => bitsOf r.width ((Store.mk (m.regs.map f) mems subs).regs.getD i 0))
    (fun r _ => bitsOf r.width (f r)) m.regs.toList 0 (fun i hi => ?_)).trans
    (flatMap_zipIdx_fst (fun r => bitsOf r.width (f r)) m.regs.toList 0)
  simp at hi
  simp [hi]

theorem update_bits (rst : Bool) (v : Nat → Nat) (r : Reg) (hr : rst = false) :
    bitsOf r.width (Reg.update rst v r) = bitsOf r.width (v r.next) := by
  subst hr
  unfold Reg.update
  split <;> simp [bitsOf_mod]

/-! ## Memories -/

/-- One memory entry after a write port. -/
def writeEntry (V : Array Nat) (w idx : Nat) (x : Nat) (p : WritePort) : Nat :=
  if (V.getD p.en 0).testBit 0 ∧ V.getD p.addr 0 = idx then (bv w (V.getD p.data 0)).toNat else x

theorem foldl_writes_size (v : Nat → Nat) (w : Nat) : ∀ (ps : List WritePort) (arr : Array Nat),
    (ps.foldl (fun arr p => if (v p.en).testBit 0 then arr.setIfInBounds (v p.addr) (bv w (v p.data)).toNat else arr)
      arr).size = arr.size
  | [], _ => rfl
  | p :: ps, arr => by
    simp only [List.foldl_cons]
    rw [foldl_writes_size v w ps]
    split <;> simp

theorem foldl_writes_getD (V : Array Nat) (w idx : Nat) : ∀ (ps : List WritePort) (arr : Array Nat), idx < arr.size →
    (ps.foldl (fun arr p => if (V.getD p.en 0).testBit 0 then
        arr.setIfInBounds (V.getD p.addr 0) (bv w (V.getD p.data 0)).toNat else arr) arr).getD idx 0
      = ps.foldl (writeEntry V w idx) (arr.getD idx 0)
  | [], _, _ => rfl
  | p :: ps, arr, h => by
    simp only [List.foldl_cons]
    rw [foldl_writes_getD V w idx ps _ (by split <;> simp [h])]
    congr 1
    unfold writeEntry
    by_cases he : (V.getD p.en 0).testBit 0
    · rw [if_pos he]
      by_cases ha : V.getD p.addr 0 = idx
      · rw [if_pos ⟨he, ha⟩, ha, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt h]; rfl
      · rw [if_neg (fun h' => ha h'.2), Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne ha,
          ← Array.getD_eq_getD_getElem?]
    · rw [if_neg he, if_neg (fun h' => he h'.1)]

theorem Mem.shape_size (mm : Mem) (old : Array Nat) : (mm.shape old).size = 2 ^ mm.addrWidth := by
  unfold Mem.shape; split <;> simp_all

theorem Mem.shape_getD (mm : Mem) (old : Array Nat) (a : Nat) (ha : a < 2 ^ mm.addrWidth) :
    (mm.shape old).getD a 0 = old.getD a 0 := by
  unfold Mem.shape; split
  · rfl
  · simp [ha]

theorem Mem.update_getD (V : Array Nat) (mm : Mem) (old : Array Nat) (a : Nat) (ha : a < 2 ^ mm.addrWidth) :
    (mm.update (V.getD · 0) old).getD a 0 = mm.writes.toList.foldl (writeEntry V mm.width a) (old.getD a 0) := by
  unfold Mem.update
  rw [← Array.foldl_toList, foldl_writes_getD V mm.width a _ _ (by rw [Mem.shape_size]; exact ha),
    Mem.shape_getD mm old a ha]

theorem entryNext_ok {assign : Nat → Bool} {vals : Array Bits} {V : Array Nat} (aw w idx : Nat)
    (hidx : idx < 2 ^ aw) :
    ∀ (ps : List WritePort) (cur : Bits) (x : Nat) (aig : AIG Nat) (out : Bits) (aig' : AIG Nat),
      ValsOk aig assign vals V → RawDen aig assign cur x → cur.size = w →
      entryNext vals aw w idx ps cur aig = some (out, aig') →
      IsPrefix aig.decls aig'.decls ∧ RawDen aig' assign out (ps.foldl (writeEntry V w idx) x) ∧ out.size = w
  | [], cur, x, aig, out, aig', _, hc, hs, h => by
    simp only [entryNext, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨IsPrefix.refl' aig, hc, hs⟩
  | p :: ps, cur, x, aig, out, aig', hv, hc, hs, h => by
    simp only [entryNext] at h
    cases h1 : bit2 (w := aw) mkEq (vals.getD p.addr #[]) (constBits aw idx) aig with
    | none => simp only [h1, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
    | some r1 =>
      obtain ⟨e, aig1⟩ := r1
      have hsa := (bit2_size h1).1
      have da : Denotes aig assign (vals.getD p.addr #[]) (bv aw (V.getD p.addr 0)) := (hv.2 p.addr).1.at hsa
      have hlt : V.getD p.addr 0 < 2 ^ aw := hsa ▸ (hv.2 p.addr).2
      obtain ⟨p1, d1⟩ := (bit2_ok (w := aw) mkEq (fun x y => x == y)
        (fun aig input x y assign hl hr => mkEq_denote_eq aig input assign x y hl hr) da
        (constBits_ok aig assign aw idx)).get h1
      have eb := single_bit d1
      rw [beq_bv hlt hidx] at eb
      have enb := (bit0_ok (hv.2 p.en).1 (hv.2 p.en).2).mono p1
      obtain ⟨c, aig2, h2, p2, d2⟩ := gate2_ok mkAndCached (· && ·) (fun _ _ _ => denote_mkAndCached) enb eb
      simp only [h1, h2, Option.bind_eq_bind, Option.bind_some] at h
      cases h3 : vite c (vals.getD p.data #[]) cur w aig2 with
      | none => simp only [h3, Option.bind_none, reduceCtorEq] at h
      | some r3 =>
        obtain ⟨cur', aig3⟩ := r3
        simp only [h3, Option.bind_some] at h
        have hsd := (vite_size h3).1
        have dd : Denotes aig2 assign (vals.getD p.data #[]) (bv w (V.getD p.data 0)) :=
          ((hv.2 p.data).1.mono (IsPrefix.trans' p1 p2)).at hsd
        have dc : Denotes aig2 assign cur (bv w x) := (hc.mono (IsPrefix.trans' p1 p2)).at hs
        obtain ⟨p3, d3⟩ := (vite_ok d2 dd dc).get h3
        have hp := IsPrefix.trans' (IsPrefix.trans' p1 p2) p3
        have hs3 := d3.size
        have rd : RawDen aig3 assign cur' (writeEntry V w idx x p) := by
          unfold RawDen; rw [hs3]
          unfold writeEntry
          by_cases hc' : (V.getD p.en 0).testBit 0 && decide (V.getD p.addr 0 = idx)
          · have : (V.getD p.en 0).testBit 0 ∧ V.getD p.addr 0 = idx := by simpa using hc'
            rw [if_pos this, bv_ofNat_toNat]; rw [if_pos hc'] at d3; exact d3
          · have : ¬ ((V.getD p.en 0).testBit 0 ∧ V.getD p.addr 0 = idx) := by simpa using hc'
            rw [if_neg this]; rw [if_neg hc'] at d3; exact d3
        obtain ⟨q, r, s⟩ := entryNext_ok aw w idx hidx ps cur' _ aig3 out aig'
          ((hv.mono (IsPrefix.trans' p1 p2)).mono p3) rd hs3 h
        exact ⟨IsPrefix.trans' hp q, by simpa using r, s⟩

theorem memNext_ok {assign : Nat → Bool} {vals : Array Bits} {V : Array Nat} (mm : Mem) (entries : Array Bits)
    (old : Array Nat) :
    ∀ (n : Nat) (aig : AIG Nat) (out : Bits) (aig' : AIG Nat), n ≤ 2 ^ mm.addrWidth →
      ValsOk aig assign vals V →
      (∀ a, a < 2 ^ mm.addrWidth → RawDen aig assign (entries.getD a #[]) (old.getD a 0) ∧
        (entries.getD a #[]).size = mm.width) →
      memNext vals mm entries n aig = some (out, aig') →
      IsPrefix aig.decls aig'.decls ∧ BitsAre aig' assign out
        ((List.range n).flatMap fun a => bitsOf mm.width ((mm.update (V.getD · 0) old).getD a 0))
  | 0, aig, out, aig', _, _, _, h => by
    simp only [memNext, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨IsPrefix.refl' aig, by simpa using BitsAre.nil aig assign⟩
  | n + 1, aig, out, aig', hn, hv, he, h => by
    simp only [memNext] at h
    cases h1 : memNext vals mm entries n aig with
    | none => simp [h1] at h
    | some r1 =>
      obtain ⟨front, aig1⟩ := r1
      obtain ⟨p1, b1⟩ := memNext_ok mm entries old n aig front aig1 (by omega) hv he h1
      simp only [h1, Option.bind_eq_bind, Option.bind_some] at h
      cases h2 : entryNext vals mm.addrWidth mm.width n mm.writes.toList (entries.getD n #[]) aig1 with
      | none => simp only [h2, Option.bind_none, reduceCtorEq] at h
      | some r2 =>
        obtain ⟨b, aig2⟩ := r2
        simp only [h2, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨p2, d2, s2⟩ := entryNext_ok mm.addrWidth mm.width n (by omega) mm.writes.toList _ _ aig1 b aig2
          (hv.mono p1) ((he n (by omega)).1.mono p1) (he n (by omega)).2 h2
        refine ⟨IsPrefix.trans' p1 p2, ?_⟩
        rw [List.range_succ, List.flatMap_append]
        refine (b1.mono p2).append ?_
        have := rawden_bitsAre d2
        rw [s2, ← Mem.update_getD V mm old n (by omega)] at this
        simpa using this

theorem memsNext_ok {assign : Nat → Bool} {vals : Array Bits} {V : Array Nat} (old : Store) :
    ∀ (ms : List Mem) (ess : List (Array Bits)) (n : Nat) (aig : AIG Nat) (out : Bits) (aig' : AIG Nat),
      ess.length = ms.length → ValsOk aig assign vals V →
      (∀ mi (hmi : mi < ms.length) a, a < 2 ^ ms[mi].addrWidth →
        RawDen aig assign ((ess.getD mi #[]).getD a #[]) ((old.mems.getD (n + mi) #[]).getD a 0) ∧
        ((ess.getD mi #[]).getD a #[]).size = ms[mi].width) →
      memsNext vals ms ess aig = some (out, aig') →
      IsPrefix aig.decls aig'.decls ∧ BitsAre aig' assign out
        ((ms.zipIdx n).flatMap fun p => memEnc p.1 (p.1.update (V.getD · 0) (old.mems.getD p.2 #[])))
  | [], ess, n, aig, out, aig', hl, _, _, h => by
    simp only [List.length_nil, List.length_eq_zero_iff] at hl
    subst hl
    simp only [memsNext, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨IsPrefix.refl' aig, by simpa using BitsAre.nil aig assign⟩
  | _ :: _, [], _, _, _, _, hl, _, _, _ => by simp at hl
  | mm :: ms, es :: ess, n, aig, out, aig', hl, hv, he, h => by
    simp only [memsNext] at h
    cases h1 : memNext vals mm es (2 ^ mm.addrWidth) aig with
    | none => simp only [h1, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
    | some r1 =>
      obtain ⟨b, aig1⟩ := r1
      obtain ⟨p1, b1⟩ := memNext_ok mm es (old.mems.getD n #[]) _ aig b aig1 (Nat.le_refl _) hv
        (fun a ha => by
          have := he 0 (by simp) a (by simpa using ha)
          simpa only [List.getD_cons_zero, List.getElem_cons_zero, Nat.add_zero] using this) h1
      simp only [h1, Option.bind_eq_bind, Option.bind_some] at h
      cases h2 : memsNext vals ms ess aig1 with
      | none => simp only [h2, Option.bind_none, reduceCtorEq] at h
      | some r2 =>
        obtain ⟨rest, aig2⟩ := r2
        simp only [h2, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨p2, b2⟩ := memsNext_ok old ms ess (n + 1) aig1 rest aig2 (by simpa using hl) (hv.mono p1)
          (fun mi hmi a ha => by
            have := he (mi + 1) (by simp; omega) a (by simpa using ha)
            simp only [List.getD_cons_succ, List.getElem_cons_succ,
              show n + (mi + 1) = n + 1 + mi by omega] at this
            exact ⟨this.1.mono p1, this.2⟩) h2
        refine ⟨IsPrefix.trans' p1 p2, ?_⟩
        simp only [List.zipIdx_cons, List.flatMap_cons]
        exact (b1.mono p2).append b2

theorem memsEnc_next (m : Module) (regs : Array Nat) (f : Nat → Mem → Array Nat) (subs : Array Store) :
    memsEnc m (.mk regs (m.mems.mapIdx f) subs) = (m.mems.toList.zipIdx).flatMap fun p => memEnc p.1 (f p.2 p.1) := by
  unfold memsEnc
  refine flatMap_zipIdx_congr (fun mm i => memEnc mm ((Store.mk regs (m.mems.mapIdx f) subs).mems.getD i #[]))
    (fun mm i => memEnc mm (f i mm)) m.mems.toList 0 (fun i hi => ?_)
  simp at hi
  simp [hi]

/-! ## Packed instance outputs -/

theorem pack_lt : ∀ (ws vs : List Nat), pack ws vs < 2 ^ ws.sum
  | [], _ => by simp [pack]
  | _ :: _, [] => by simp only [pack]; exact Nat.two_pow_pos _
  | w :: ws, v :: vs => by
    simp only [pack, List.sum_cons, Nat.pow_add]
    have h1 := Nat.mod_lt v (Nat.two_pow_pos w)
    have h2 := pack_lt ws vs
    have h3 : 2 ^ w * (pack ws vs + 1) ≤ 2 ^ w * 2 ^ ws.sum := Nat.mul_le_mul_left _ h2
    rw [Nat.mul_succ] at h3
    omega

theorem rawden_iff {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {n : Nat} :
    RawDen aig assign a n ↔ ∀ i (hi : i < a.size), BitIs aig assign a[i] (n.testBit i) := by
  constructor
  · intro h i hi
    have := testBit_of_denotes h i hi
    simpa only [bitOr, dif_pos hi] using this
  · exact denotes_of_bits a n

theorem packBits_ok {aig : AIG Nat} {assign : Nat → Bool} : ∀ (bs : List Bits) (vs : List Nat),
    bs.length = vs.length → (∀ i (hb : i < bs.length) (hv : i < vs.length), RawDen aig assign bs[i] vs[i]) →
    RawDen aig assign (packBits bs) (pack (bs.map Array.size) vs) ∧ (packBits bs).size = (bs.map Array.size).sum
  | [], [], _, _ => ⟨by simpa [packBits, pack] using RawDen.empty aig assign 0, by simp [packBits]⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | b :: bs, v :: vs, hl, h => by
    obtain ⟨r, s⟩ := packBits_ok bs vs (by simpa using hl) (fun i hb hv => by
      have := h (i + 1) (by simp; omega) (by simp; omega)
      simpa only [List.getElem_cons_succ] using this)
    have h0 := rawden_iff.mp (by simpa using h 0 (by simp) (by simp))
    have r' := rawden_iff.mp r
    have hsz : (packBits (b :: bs)).size = b.size + (packBits bs).size := by
      simp [packBits, concatBits]
    refine ⟨rawden_iff.mpr fun i hi => ?_, by rw [hsz, s]; simp⟩
    simp only [List.map_cons, pack]
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
    simp only [packBits, concatBits, Array.getElem_append]
    split
    · rename_i hlt
      rw [Nat.testBit_mod_two_pow, decide_eq_true hlt, Bool.true_and]
      exact h0 i hlt
    · rename_i hge
      exact r' (i - b.size) (by rw [hsz] at hi; omega)

/-! ## Cells -/

def instModsL (cs : List Cell) : List Nat := cs.filterMap fun c =>
  match c.op with
  | .inst j _ _ => some j
  | _ => none

theorem instMods_eq (m : Module) : instMods m = instModsL m.cells.toList := rfl

/-- Encodings of the instances among `cs`, numbered from `n`. -/
def childEnc (E : Nat → Store → List Bool) (cs : List Cell) (n : Nat) (S : Nat → Store) : List Bool :=
  ((instModsL cs).zipIdx n).flatMap fun p => E p.1 (S p.2)

theorem childEnc_nil (E : Nat → Store → List Bool) (n : Nat) (S : Nat → Store) : childEnc E [] n S = [] := rfl

theorem childEnc_inst (E : Nat → Store → List Bool) (c : Cell) (cs : List Cell) (n : Nat) (S : Nat → Store)
    {j : Nat} {args outs : List Nat} (h : c.op = .inst j args outs) :
    childEnc E (c :: cs) n S = E j (S n) ++ childEnc E cs (n + 1) S := by
  simp [childEnc, instModsL, List.filterMap_cons, h, List.zipIdx_cons]

theorem childEnc_other (E : Nat → Store → List Bool) (c : Cell) (cs : List Cell) (n : Nat) (S : Nat → Store)
    (h : ∀ j args outs, c.op ≠ .inst j args outs) : childEnc E (c :: cs) n S = childEnc E cs n S := by
  have hn : (match c.op with | .inst j _ _ => some j | _ => none : Option Nat) = none := by
    split
    · rename_i j args outs hop; exact absurd hop (h j args outs)
    · rfl
  simp only [childEnc, instModsL, List.filterMap_cons, hn]

theorem stepCell_inst {env : Nat → Sem} {st : Store} {ins : Array Nat} {rst : Bool} {a : Acc} {c : Cell}
    {j : Nat} {args outs : List Nat} (h : c.op = .inst j args outs) :
    stepCell env st ins rst a c =
      let r := env j (st.subs.getD a.subs.size default) (args.toArray.map (a.vals.getD · 0)) rst
      ⟨a.vals.push (bv c.width (pack outs r.1.toList)).toNat, a.subs.push r.2⟩ := by
  unfold stepCell; rw [h]

theorem stepCell_other {env : Nat → Sem} {st : Store} {ins : Array Nat} {rst : Bool} {a : Acc} {c : Cell}
    (h : ∀ j args outs, c.op ≠ .inst j args outs) :
    stepCell env st ins rst a c = ⟨a.vals.push (c.op.evalBV (frame st ins a.vals) c.width).toNat, a.subs⟩ := by
  unfold stepCell
  split
  · rename_i j args outs hop; exact absurd hop (h j args outs)
  · rfl

theorem stepCell_subs_size (env : Nat → Sem) (st : Store) (ins : Array Nat) (rst : Bool) (a : Acc) (c : Cell) :
    a.subs.size ≤ (stepCell env st ins rst a c).subs.size := by
  unfold stepCell; split <;> simp

theorem stepCell_subs (env : Nat → Sem) (st : Store) (ins : Array Nat) (rst : Bool) (a : Acc) (c : Cell)
    (i : Nat) (hi : i < a.subs.size) : (stepCell env st ins rst a c).subs.getD i default = a.subs.getD i default := by
  unfold stepCell
  split
  · simp [Array.getElem?_push, hi, Nat.ne_of_lt hi]
  · rfl

theorem foldl_subs (env : Nat → Sem) (st : Store) (ins : Array Nat) (rst : Bool) :
    ∀ (cs : List Cell) (a : Acc) (i : Nat), i < a.subs.size →
      (cs.foldl (stepCell env st ins rst) a).subs.getD i default = a.subs.getD i default
  | [], _, _, _ => rfl
  | c :: cs, a, i, hi => by
    simp only [List.foldl_cons]
    rw [foldl_subs env st ins rst cs _ i (Nat.lt_of_lt_of_le hi (stepCell_subs_size ..)), stepCell_subs _ _ _ _ _ _ i hi]

/-- Output words of an instance. -/
def OutsOk (aig : AIG Nat) (assign : Nat → Bool) (bs : Array Bits) (vs : Array Nat) : Prop :=
  bs.size = vs.size ∧ ∀ o, RawDen aig assign (bs.getD o #[]) (vs.getD o 0)

/-- What a blaster for the instantiated modules must deliver: given input bits
denoting the input words and state atoms holding the encoding `E j st`, output
bits denoting the outputs and bits holding the encoding of the next store. -/
def ChildOk (IB : Nat) (assign : Nat → Bool) (child : ChildBlaster) (env : Nat → Sem)
    (E : Nat → Store → List Bool) : Prop :=
  ∀ j aig ins base st (insV : Array Nat) couts cnext aig',
    child j aig ins base = some ((couts, cnext), aig') →
    (∀ i, RawDen aig assign (ins.getD i #[]) (insV.getD i 0)) →
    Laid assign (IB + base) (E j st) →
    IsPrefix aig.decls aig'.decls ∧ OutsOk aig' assign couts (env j st insV false).1 ∧
      BitsAre aig' assign cnext (E j (env j st insV false).2) ∧ cnext.size = (E j st).length

/-- Inputs, registers and memory entries. -/
def FixedOk (aig : AIG Nat) (assign : Nat → Bool) (fr : BFrame) (st : Store) (insV : Array Nat) : Prop :=
  (∀ k, RawDen aig assign (fr.ins.getD k #[]) (insV.getD k 0)) ∧
  (∀ k, RawDen aig assign (fr.regs.getD k #[]) (st.regs.getD k 0)) ∧
  (∀ mi a, RawDen aig assign ((fr.mems.getD mi #[]).getD a #[]) ((st.mems.getD mi #[]).getD a 0))

theorem FixedOk.mono {aig aig' : AIG Nat} {assign : Nat → Bool} {fr : BFrame} {st : Store} {insV : Array Nat}
    (h : FixedOk aig assign fr st insV) (hp : IsPrefix aig.decls aig'.decls) : FixedOk aig' assign fr st insV :=
  ⟨fun k => (h.1 k).mono hp, fun k => (h.2.1 k).mono hp, fun mi a => (h.2.2 mi a).mono hp⟩

theorem frameOk_of {aig : AIG Nat} {assign : Nat → Bool} {fr : BFrame} {st : Store} {insV : Array Nat}
    {vals : Array Bits} {V : Array Nat} (hf : FixedOk aig assign fr st insV) (hv : ValsOk aig assign vals V) :
    FrameOk aig assign { fr with vals := vals } (frame st insV V) :=
  ⟨fun k => hv.2 k, fun k => hf.1 k, fun k => hf.2.1 k, fun mi a => hf.2.2 mi a⟩

theorem blastCells_ok {IB : Nat} {assign : Nat → Bool} {child : ChildBlaster} {env : Nat → Sem}
    {E : Nat → Store → List Bool} (hc : ChildOk IB assign child env E) (fr : BFrame) (st : Store)
    (insV : Array Nat) :
    ∀ (cs : List Cell) (b : BAcc) (a : Acc) (b' : BAcc), blastCells child fr cs b = some b' →
      FixedOk b.aig assign fr st insV → ValsOk b.aig assign b.vals a.vals →
      Laid assign (IB + b.cbase) (childEnc E cs a.subs.size (fun i => st.subs.getD i default)) →
      IsPrefix b.aig.decls b'.aig.decls ∧
        ValsOk b'.aig assign b'.vals (cs.foldl (stepCell env st insV false) a).vals ∧
        ∃ X, b'.next = b.next ++ X ∧ BitsAre b'.aig assign X
          (childEnc E cs a.subs.size (fun i => (cs.foldl (stepCell env st insV false) a).subs.getD i default))
  | [], b, a, b', h, _, hv, _ => by
    simp only [blastCells, Option.some.injEq] at h
    subst h
    exact ⟨IsPrefix.refl' _, hv, #[], by simp, by simpa [childEnc_nil] using BitsAre.nil _ assign⟩
  | c :: cs, b, a, b', h, hf, hv, hl => by
    by_cases hi : ∃ j args outs, c.op = .inst j args outs
    · obtain ⟨j, args, outs, hop⟩ := hi
      have hsz1 : (stepCell env st insV false a c).subs.size = a.subs.size + 1 := by
        rw [stepCell_inst hop]; simp
      simp only [blastCells, hop] at h
      cases hch : child j b.aig (args.toArray.map fun a => b.vals.getD a #[]) b.cbase with
      | none => simp only [hch, reduceCtorEq] at h
      | some r =>
        obtain ⟨⟨couts, cnext⟩, aig1⟩ := r
        simp only [hch] at h
        split at h
        · rename_i hsz
          rw [childEnc_inst E c cs _ _ hop] at hl ⊢
          have hins : ∀ i, RawDen b.aig assign ((args.toArray.map fun a => b.vals.getD a #[]).getD i #[])
              ((args.toArray.map (a.vals.getD · 0)).getD i 0) := by
            intro i
            by_cases hi : i < args.length
            · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
                List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
              have := (hv.2 args[i]).1
              simpa only [Array.getD_eq_getD_getElem?] using this
            · have hn : args[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
              simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray, hn,
                Option.map_none, Option.getD_none]
              exact RawDen.empty _ _ _
          obtain ⟨p1, ho, hn, hsn⟩ := hc j b.aig _ b.cbase (st.subs.getD a.subs.size default)
            (args.toArray.map (a.vals.getD · 0)) couts cnext aig1 hch hins hl.left
          generalize hr : env j (st.subs.getD a.subs.size default) (args.toArray.map (a.vals.getD · 0)) false = r
            at ho hn
          have hpk := packBits_ok (aig := aig1) (assign := assign) couts.toList r.1.toList
            (by simpa using ho.1) (fun i hb _ => by
              have := ho.2 i
              simp only [Array.getD_eq_getD_getElem?] at this
              simpa [Array.getElem?_eq_getElem (by simpa using hb),
                Array.getElem?_eq_getElem (show i < r.1.size by rw [← ho.1]; simpa using hb)] using this)
          rw [hsz] at hpk
          have hz := zextBits_ok (aig := aig1) (assign := assign) (pack outs r.1.toList) c.width
            (hpk.1.at rfl) (by rw [hpk.2]; exact pack_lt _ _)
          have hzs : (zextBits (packBits couts.toList) c.width).size = c.width := by simp [zextBits]
          have hz' : RawDen aig1 assign (zextBits (packBits couts.toList) c.width)
              (bv c.width (pack outs r.1.toList)).toNat := by
            unfold RawDen; rw [hzs, bv_ofNat_toNat]; exact hz
          have hv1 := (hv.mono p1).push hz' (by rw [hzs]; exact BitVec.isLt _)
          have hl2 := hl.right
          rw [← hsn, Nat.add_assoc] at hl2
          have hst : stepCell env st insV false a c =
              ⟨a.vals.push (bv c.width (pack outs r.1.toList)).toNat, a.subs.push r.2⟩ := by
            rw [stepCell_inst hop, ← hr]
          have ih := blastCells_ok hc fr st insV cs _ (stepCell env st insV false a c) b' h (hf.mono p1)
            (by rw [hst]; exact hv1) (by rw [hsz1]; exact hl2)
          obtain ⟨p2, hv2, X, hX, bX⟩ := ih
          refine ⟨IsPrefix.trans' p1 p2, hv2, cnext ++ X, by simpa [Array.append_assoc] using hX, ?_⟩
          have hsub : (cs.foldl (stepCell env st insV false) (stepCell env st insV false a c)).subs.getD
              a.subs.size default = r.2 := by
            rw [foldl_subs _ _ _ _ cs _ _ (by rw [hsz1]; omega), hst]
            simp
          simp only [List.foldl_cons]
          rw [hsub]
          rw [hsz1] at bX
          exact (hn.mono p2).append bX
        · cases h
    · have hne : ∀ j args outs, c.op ≠ .inst j args outs := fun j args outs he => hi ⟨j, args, outs, he⟩
      have hb : blastCells child fr (c :: cs) b =
          match blastOp { fr with vals := b.vals } c.width c.op b.aig with
          | some (bits, aig) => blastCells child fr cs ⟨b.vals.push bits, b.next, b.cbase, aig⟩
          | none => none := by
        simp only [blastCells]
        cases hc : c.op <;> first | (exfalso; exact hne _ _ _ hc) | rfl
      rw [hb] at h
      cases hop : blastOp { fr with vals := b.vals } c.width c.op b.aig with
      | none => simp only [hop, reduceCtorEq] at h
      | some r =>
        obtain ⟨bits, aig1⟩ := r
        simp only [hop] at h
        obtain ⟨p1, d1⟩ := blastOp_ok (frameOk_of hf hv) c.width c.op hop
        have hs1 := d1.size
        have rd : RawDen aig1 assign bits (c.op.evalBV (frame st insV a.vals) c.width).toNat := by
          unfold RawDen; rw [hs1]; simpa using d1
        have hv1 := (hv.mono p1).push rd (by rw [hs1]; exact BitVec.isLt _)
        rw [childEnc_other E c cs _ _ hne] at hl ⊢
        have ih := blastCells_ok hc fr st insV cs _ (stepCell env st insV false a c) b' h (hf.mono p1)
          (by rw [stepCell_other hne]; exact hv1) (by rw [stepCell_other hne]; exact hl)
        obtain ⟨p2, hv2, X, hX, bX⟩ := ih
        have hsz0 : (stepCell env st insV false a c).subs.size = a.subs.size := by rw [stepCell_other hne]
        rw [hsz0] at bX
        exact ⟨IsPrefix.trans' p1 p2, hv2, X, hX, bX⟩

/-! ## Modules -/

theorem regsEnc_eq (m : Module) (st : Store) : regsEnc m st = encRegs m.regs.toList 0 st := rfl
theorem memsEnc_eq (m : Module) (st : Store) : memsEnc m st = encMems m.mems.toList 0 st := rfl

theorem getD_size_le {α : Type} (arr : Array α) (i : Nat) (d : α) (h : arr.size ≤ i) : arr.getD i d = d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

theorem blastWith_ok {IB : Nat} {assign : Nat → Bool} {child : ChildBlaster} {env : Nat → Sem}
    {E : Nat → Store → List Bool} (hc : ChildOk IB assign child env E) (m : Module)
    (aig : AIG Nat) (ins : Array Bits) (base : Nat) (st : Store) (insV : Array Nat)
    (outs : Array Bits) (next : Bits) (aig' : AIG Nat)
    (h : blastWith IB child m aig ins base = some ((outs, next), aig'))
    (hins : ∀ i, RawDen aig assign (ins.getD i #[]) (insV.getD i 0))
    (hst : Laid assign (IB + base)
      (regsEnc m st ++ memsEnc m st ++ childEnc E m.cells.toList 0 (fun i => st.subs.getD i default))) :
    IsPrefix aig.decls aig'.decls ∧ OutsOk aig' assign outs (m.evalWith env st insV false).1 ∧
      BitsAre aig' assign next (regsEnc m (m.evalWith env st insV false).2 ++
        memsEnc m (m.evalWith env st insV false).2 ++
        childEnc E m.cells.toList 0 (fun i => (m.evalWith env st insV false).2.subs.getD i default)) := by
  -- atoms for the registers and memories
  have hr := hst.left.left
  rw [regsEnc_eq] at hr
  obtain ⟨pr, sr, dr⟩ := regAtoms_ok assign st m.regs.toList 0 (IB + base) aig hr.get
  have hm := hst.left.right
  rw [regsEnc_length, memsEnc_eq] at hm
  obtain ⟨pm, sm, dm⟩ := memAtoms_ok assign st m.mems.toList 0 (IB + base + regBits m)
    (regAtoms (IB + base) m.regs.toList aig).2 hm.get
  have hch := hst.right
  rw [List.length_append, regsEnc_length, memsEnc_length] at hch
  generalize hra : regAtoms (IB + base) m.regs.toList aig = ra at pr sr dr pm sm dm
  generalize hma : memAtoms (IB + base + regBits m) m.mems.toList ra.2 = ma at pm sm dm
  have p0 := IsPrefix.trans' pr pm
  have hfix : FixedOk ma.2 assign ⟨ins, ra.1, ma.1, #[]⟩ st insV := by
    refine ⟨fun k => (hins k).mono p0, fun k => ?_, fun mi a => ?_⟩
    · by_cases hk : k < m.regs.toList.length
      · simpa using ((dr k hk).1).mono pm
      · rw [getD_size_le _ _ _ (by rw [sr]; omega)]; exact RawDen.empty _ _ _
    · by_cases hmi : mi < m.mems.toList.length
      · by_cases ha : a < 2 ^ m.mems.toList[mi]!.addrWidth
        · simpa using (dm mi a hmi ha).1
        · show RawDen _ _ ((ma.1.getD mi #[]).getD a #[]) _
          rw [getD_size_le (ma.1.getD mi #[]) _ _ (by rw [(dm mi 0 hmi (Nat.two_pow_pos _)).2.2]; omega)]
          exact RawDen.empty _ _ _
      · show RawDen _ _ ((ma.1.getD mi #[]).getD a #[]) _
        rw [getD_size_le ma.1 _ _ (by rw [sm]; omega)]
        simpa using RawDen.empty ma.2 assign ((st.mems.getD mi #[]).getD a 0)
  simp only [blastWith, hra, hma] at h
  cases hb : blastCells child ⟨ins, ra.1, ma.1, #[]⟩ m.cells.toList
      ⟨#[], #[], base + regBits m + memBits m, ma.2⟩ with
  | none => simp only [hb, reduceCtorEq] at h
  | some acc =>
    simp only [hb] at h
    obtain ⟨pc, hvc, X, hX, bX⟩ := blastCells_ok hc ⟨ins, ra.1, ma.1, #[]⟩ st insV m.cells.toList _ ⟨#[], #[]⟩ acc hb
      hfix (ValsOk.empty _ _) (by simpa [Nat.add_assoc] using hch)
    simp only [Array.empty_append] at hX
    subst hX
    cases hrn : regsNext acc.vals m.regs.toList with
    | none => simp [hrn] at h
    | some rn =>
      cases hmn : memsNext acc.vals m.mems.toList ma.1.toList acc.aig with
      | none => simp [hrn, hmn] at h
      | some r =>
        obtain ⟨mn, aig2⟩ := r
        simp only [hrn, hmn, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        have hvals : Module.values env m st insV false = m.cells.toList.foldl (stepCell env st insV false) ⟨#[], #[]⟩ := by
          unfold Module.values; rw [Array.foldl_toList]
        generalize hV : m.cells.toList.foldl (stepCell env st insV false) ⟨#[], #[]⟩ = acc' at hvc bX hvals
        have brn := regsNext_ok hvc m.regs.toList rn hrn
        obtain ⟨pmn, bmn⟩ := memsNext_ok (vals := acc.vals) (V := acc'.vals) st m.mems.toList ma.1.toList 0 acc.aig mn aig2
          (by simp [sm]) hvc (fun mi hmi a ha => by
            have e : m.mems.toList[mi]! = m.mems.toList[mi] := getElem!_pos m.mems.toList mi hmi
            have := dm mi a hmi (by rw [e]; exact ha)
            rw [e] at this
            simp only [Array.getD_eq_getD_getElem?] at this ⊢
            simp only [List.getD_eq_getElem?_getD, Array.getElem?_toList, Nat.zero_add] at this ⊢
            exact ⟨this.1.mono pc, this.2.1⟩) hmn
        refine ⟨IsPrefix.trans' p0 (IsPrefix.trans' pc pmn), ⟨by simp [Module.evalWith], fun o => ?_⟩, ?_⟩
        · simp only [Module.evalWith, hvals, Array.getD_eq_getD_getElem?, Array.getElem?_map]
          cases m.outputs[o]? with
          | none => simpa using RawDen.empty aig2 assign 0
          | some op =>
            have := (hvc.2 op.node).1.mono pmn
            simpa only [Array.getD_eq_getD_getElem?, Option.map_some, Option.getD_some] using this
        · simp only [Module.evalWith, hvals, Store.subs_mk]
          rw [regsEnc_next, memsEnc_next]
          have e1 : (m.regs.toList.flatMap fun r => bitsOf r.width (Reg.update false (acc'.vals.getD · 0) r)) =
              m.regs.toList.flatMap fun r => bitsOf r.width (acc'.vals.getD r.next 0) := by
            congr 1; funext r; exact update_bits false _ r rfl
          rw [e1]
          simp only [show ({ vals := #[], subs := #[] } : Acc).subs.size = 0 from rfl] at bX
          exact ((brn.mono pmn).append bmn).append (bX.mono pmn)

/-- The encoding of the instances of module `k`. -/
def childE (d : Design) (k : Nat) : Nat → Store → List Bool := fun j s => if j < k then encode d j s else []

theorem encode_split (d : Design) (k : Nat) (m : Module) (h : d.modules[k]? = some m) (st : Store) :
    encode d k st = regsEnc m st ++ memsEnc m st ++
      childEnc (childE d k) m.cells.toList 0 (fun i => st.subs.getD i default) := by
  rw [encode_eq d k m h]; rfl

/-- Bit-blasting a module of the design is correct. -/
theorem blastModule_ok (d : Design) (IB : Nat) (assign : Nat → Bool) (k : Nat) :
    ∀ (aig : AIG Nat) (ins : Array Bits) (base : Nat) (st : Store) (insV : Array Nat)
      (outs : Array Bits) (next : Bits) (aig' : AIG Nat),
      blastModule d IB k aig ins base = some ((outs, next), aig') →
      (∀ i, RawDen aig assign (ins.getD i #[]) (insV.getD i 0)) →
      Laid assign (IB + base) (encode d k st) →
      IsPrefix aig.decls aig'.decls ∧ OutsOk aig' assign outs (d.sem k st insV false).1 ∧
        BitsAre aig' assign next (encode d k (d.sem k st insV false).2) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro aig ins base st insV outs next aig' h hins hst
    cases hm : d.modules[k]? with
    | none => rw [blastModule] at h; simp [hm] at h
    | some m =>
      rw [blastModule] at h
      simp only [hm] at h
      have hc : ChildOk IB assign (fun j aig ins base => if j < k then blastModule d IB j aig ins base else none)
          (d.env k) (childE d k) := by
        intro j aig ins base st insV couts cnext aig' hj hi hl
        by_cases hjk : j < k
        · simp only [hjk, ite_true] at hj
          simp only [childE, hjk, ite_true] at hl ⊢
          have henv : d.env k j = d.sem j := by simp [Design.env, hjk]
          rw [henv]
          obtain ⟨p, o, b⟩ := ih j hjk aig ins base st insV couts cnext aig' hj hi hl
          exact ⟨p, o, b, by rw [b.1, encode_length, encode_length]⟩
        · simp [hjk] at hj
      rw [encode_split d k m hm] at hst
      rw [Design.sem_eq d k m hm, encode_split d k m hm]
      exact blastWith_ok hc m aig ins base st insV outs next aig' h hins hst

end HDLean.Rtl.Blast
