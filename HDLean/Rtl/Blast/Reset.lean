import HDLean.Rtl.Blast.Correct

/-!
# Reset, bit by bit

Reset only affects registers declared with a synchronous reset value; memory
contents and free-running registers ignore it, and outputs never depend on it.
So the encoding of the next store under any reset level is obtained from the
encoding under reset-low by a per-bit reset kind (`kinds`), which is what the
node graph's `resetValue` applies.
-/
namespace HDLean.Rtl.Blast

open HDLean (ResetKind)

/-- Per-bit reset behaviour. -/
def applyReset : List ResetKind → List Bool → List Bool → Bool → List Bool
  | k :: ks, o :: os, n :: ns, rst => Dag.resetValue k o n rst :: applyReset ks os ns rst
  | _, _, _, _ => []

theorem applyReset_append (rst : Bool) : ∀ (ks1 ks2 : List ResetKind) (os1 os2 ns1 ns2 : List Bool),
    ks1.length = os1.length → os1.length = ns1.length →
    applyReset (ks1 ++ ks2) (os1 ++ os2) (ns1 ++ ns2) rst = applyReset ks1 os1 ns1 rst ++ applyReset ks2 os2 ns2 rst
  | [], _, [], _, [], _, _, _ => rfl
  | k :: ks1, ks2, o :: os1, os2, n :: ns1, ns2, h1, h2 => by
    simp only [List.cons_append, applyReset, List.cons.injEq, true_and]
    exact applyReset_append rst ks1 ks2 os1 os2 ns1 ns2 (by simpa using h1) (by simpa using h2)
  | [], _, _ :: _, _, _, _, h1, _ => by simp at h1
  | _ :: _, _, [], _, _, _, h1, _ => by simp at h1
  | _, _, [], _, _ :: _, _, _, h2 => by simp at h2
  | _, _, _ :: _, _, [], _, _, h2 => by simp at h2

theorem applyReset_length : ∀ (ks : List ResetKind) (os ns : List Bool) (rst : Bool),
    ks.length = os.length → os.length = ns.length → (applyReset ks os ns rst).length = ks.length
  | [], _, _, _, _, _ => by simp [applyReset]
  | _ :: _, [], _, _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, h => by simp at h
  | _ :: ks, _ :: os, _ :: ns, rst, h1, h2 => by
    simp only [applyReset, List.length_cons]
    rw [applyReset_length ks os ns rst (by simpa using h1) (by simpa using h2)]

theorem applyReset_getD : ∀ (ks : List ResetKind) (os ns : List Bool) (rst : Bool) (i : Nat),
    i < ks.length → ks.length = os.length → os.length = ns.length →
    (applyReset ks os ns rst).getD i false =
      Dag.resetValue (ks.getD i .unreset) (os.getD i false) (ns.getD i false) rst
  | [], _, _, _, _, hi, _, _ => by simp at hi
  | _ :: _, [], _, _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, _ :: _, _, 0, _, _, _ => rfl
  | _ :: ks, _ :: os, _ :: ns, rst, i + 1, hi, h1, h2 => by
    simp only [applyReset, List.getD_cons_succ]
    exact applyReset_getD ks os ns rst i (by simpa using hi) (by simpa using h1) (by simpa using h2)

theorem resetValue_false (k : ResetKind) (o n : Bool) : Dag.resetValue k o n false = n := by
  cases k <;> rfl

theorem applyReset_false : ∀ (ks : List ResetKind) (os ns : List Bool),
    ks.length = os.length → os.length = ns.length → applyReset ks os ns false = ns
  | [], [], [], _, _ => rfl
  | k :: ks, o :: os, n :: ns, h1, h2 => by
    simp only [applyReset, resetValue_false, List.cons.injEq, true_and]
    exact applyReset_false ks os ns (by simpa using h1) (by simpa using h2)
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | _, [], _ :: _, _, h => by simp at h
  | _, _ :: _, [], _, h => by simp at h

theorem applyReset_unreset (rst : Bool) : ∀ (os ns : List Bool),
    os.length = ns.length → applyReset (List.replicate os.length .unreset) os ns rst = ns
  | [], [], _ => rfl
  | o :: os, n :: ns, h => by
    simp only [List.length_cons, List.replicate_succ, applyReset, List.cons.injEq]
    exact ⟨rfl, applyReset_unreset rst os ns (by simpa using h)⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem applyReset_unreset' (rst : Bool) (n : Nat) (os ns : List Bool) (h1 : os.length = n) (h2 : ns.length = n) :
    applyReset (List.replicate n .unreset) os ns rst = ns := by
  subst h1; exact applyReset_unreset rst os ns h2.symm

theorem applyReset_flatMap {β : Type} (rst : Bool) (K : β → List ResetKind) (O N : β → List Bool)
    (hK : ∀ x, (K x).length = (O x).length) (hO : ∀ x, (O x).length = (N x).length) :
    ∀ l : List β, applyReset (l.flatMap K) (l.flatMap O) (l.flatMap N) rst =
      l.flatMap fun x => applyReset (K x) (O x) (N x) rst
  | [] => rfl
  | x :: xs => by
    simp only [List.flatMap_cons]
    rw [applyReset_append rst _ _ _ _ _ _ (hK x) (hO x), applyReset_flatMap rst K O N hK hO xs]

/-! ## Kinds -/

def regKinds (r : Reg) : List ResetKind :=
  match r.reset with
  | .none => List.replicate r.width .unreset
  | .sync x => List.ofFn fun i : Fin r.width => .synchronous (x.testBit i)

/-- The reset kind of each state bit of an instance of module `k`, in `encode` order. -/
def kinds (d : Design) (k : Nat) : List ResetKind :=
  match d.modules[k]? with
  | some m => m.regs.toList.flatMap regKinds ++ List.replicate (memBits m) .unreset ++
      (instMods m).flatMap fun j => if j < k then kinds d j else []
  | none => []
termination_by k

theorem kinds_eq (d : Design) (k : Nat) (m : Module) (h : d.modules[k]? = some m) :
    kinds d k = m.regs.toList.flatMap regKinds ++ List.replicate (memBits m) .unreset ++
      (instMods m).flatMap fun j => if j < k then kinds d j else [] := by
  rw [kinds]; simp [h]

@[simp] theorem regKinds_length (r : Reg) : (regKinds r).length = r.width := by
  unfold regKinds; split <;> simp

theorem kinds_length (d : Design) (k : Nat) : (kinds d k).length = stateBits d k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases hm : d.modules[k]? with
    | none => rw [kinds, stateBits]; simp [hm]
    | some m =>
      rw [kinds_eq d k m hm, stateBits_eq d k m hm]
      have hmap : (instMods m).map (fun j => (if j < k then kinds d j else []).length) =
          (instMods m).map (fun j => if j < k then stateBits d j else 0) := by
        apply List.map_congr_left
        intro j _
        split
        · rename_i hj; exact ih j hj
        · rfl
      simp only [List.length_append, List.length_flatMap, regKinds_length, List.length_replicate, hmap]
      rfl

theorem reg_reset (r : Reg) (o : Nat) (v : Nat → Nat) (rst : Bool) :
    bitsOf r.width (Reg.update rst v r) =
      applyReset (regKinds r) (bitsOf r.width o) (bitsOf r.width (Reg.update false v r)) rst := by
  cases rst
  · rw [applyReset_false _ _ _ (by simp) (by simp)]
  · apply List.ext_getElem
    · rw [applyReset_length _ _ _ _ (by simp) (by simp)]; simp
    · intro i h1 h2
      have hi : i < r.width := by simpa using h1
      have e := applyReset_getD (regKinds r) (bitsOf r.width o) (bitsOf r.width (Reg.update false v r)) true i
        (by simpa using hi) (by simp) (by simp)
      simp only [List.getD_eq_getElem?_getD] at e
      rw [List.getElem?_eq_getElem h2] at e
      simp only [Option.getD_some] at e
      rw [e]
      cases hr : r.reset with
      | none => simp [regKinds, Reg.update, hr, bitsOf, Dag.resetValue, hi]
      | sync x => simp [regKinds, Reg.update, hr, bitsOf, Dag.resetValue, hi]

/-! ## Semantics under reset -/

theorem foldl_rst {env : Nat → Sem} (henv : ∀ j s x rst, (env j s x rst).1 = (env j s x false).1)
    (st : Store) (ins : Array Nat) (rst : Bool) :
    ∀ (cs : List Cell) (a a' : Acc), a.vals = a'.vals → a.subs.size = a'.subs.size →
      (cs.foldl (stepCell env st ins rst) a).vals = (cs.foldl (stepCell env st ins false) a').vals ∧
      (cs.foldl (stepCell env st ins rst) a).subs.size = (cs.foldl (stepCell env st ins false) a').subs.size
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | c :: cs, a, a', h1, h2 => by
    simp only [List.foldl_cons]
    apply foldl_rst henv st ins rst cs
    · by_cases hi : ∃ j args outs, c.op = .inst j args outs
      · obtain ⟨j, args, outs, hop⟩ := hi
        rw [stepCell_inst hop, stepCell_inst hop]
        simp only [h1, h2, henv]
      · have hne : ∀ j args outs, c.op ≠ .inst j args outs := fun j args outs he => hi ⟨j, args, outs, he⟩
        rw [stepCell_other hne, stepCell_other hne, h1]
    · by_cases hi : ∃ j args outs, c.op = .inst j args outs
      · obtain ⟨j, args, outs, hop⟩ := hi
        rw [stepCell_inst hop, stepCell_inst hop]
        simp [h2]
      · have hne : ∀ j args outs, c.op ≠ .inst j args outs := fun j args outs he => hi ⟨j, args, outs, he⟩
        rw [stepCell_other hne, stepCell_other hne]
        exact h2

theorem childEnc_rst {env : Nat → Sem} {E : Nat → Store → List Bool} {K : Nat → List ResetKind}
    (henv : ∀ j s x rst, (env j s x rst).1 = (env j s x false).1)
    (hE : ∀ j s x rst, E j (env j s x rst).2 = applyReset (K j) (E j s) (E j (env j s x false).2) rst)
    (hK : ∀ j s, (K j).length = (E j s).length) (hL : ∀ j s s', (E j s).length = (E j s').length)
    (st : Store) (ins : Array Nat) (rst : Bool) :
    ∀ (cs : List Cell) (a a' : Acc), a.vals = a'.vals → a.subs.size = a'.subs.size →
      childEnc E cs a.subs.size (fun i => (cs.foldl (stepCell env st ins rst) a).subs.getD i default) =
        applyReset ((instModsL cs).flatMap K) (childEnc E cs a.subs.size (fun i => st.subs.getD i default))
          (childEnc E cs a.subs.size (fun i => (cs.foldl (stepCell env st ins false) a').subs.getD i default)) rst
  | [], _, _, _, _ => rfl
  | c :: cs, a, a', h1, h2 => by
    by_cases hi : ∃ j args outs, c.op = .inst j args outs
    · obtain ⟨j, args, outs, hop⟩ := hi
      have hsz : (stepCell env st ins rst a c).subs.size = a.subs.size + 1 := by rw [stepCell_inst hop]; simp
      have hsz' : (stepCell env st ins false a' c).subs.size = a.subs.size + 1 := by
        rw [stepCell_inst hop]; simp [h2]
      have hv : (stepCell env st ins rst a c).vals = (stepCell env st ins false a' c).vals := by
        rw [stepCell_inst hop, stepCell_inst hop]; simp only [h1, h2, henv]
      have ih := childEnc_rst henv hE hK hL st ins rst cs _ _ hv (by rw [hsz, hsz'])
      rw [hsz] at ih
      simp only [List.foldl_cons]
      have e1 : (cs.foldl (stepCell env st ins rst) (stepCell env st ins rst a c)).subs.getD a.subs.size default
          = (env j (st.subs.getD a.subs.size default) (args.toArray.map (a.vals.getD · 0)) rst).2 := by
        rw [foldl_subs _ _ _ _ cs _ _ (by rw [hsz]; omega), stepCell_inst hop]; simp
      have e2 : (cs.foldl (stepCell env st ins false) (stepCell env st ins false a' c)).subs.getD a.subs.size default
          = (env j (st.subs.getD a.subs.size default) (args.toArray.map (a.vals.getD · 0)) false).2 := by
        rw [foldl_subs _ _ _ _ cs _ _ (by rw [hsz']; omega), stepCell_inst hop]; simp [h1, h2]
      have hi' : instModsL (c :: cs) = j :: instModsL cs := by
        simp [instModsL, List.filterMap_cons, hop]
      rw [childEnc_inst E c cs _ _ hop, childEnc_inst E c cs _ _ hop, childEnc_inst E c cs _ _ hop, ih, hi',
        List.flatMap_cons]
      rw [e1, e2, hE, applyReset_append _ _ _ _ _ _ _ (hK j _) (hL j _ _)]
    · have hne : ∀ j args outs, c.op ≠ .inst j args outs := fun j args outs he => hi ⟨j, args, outs, he⟩
      have hv : (stepCell env st ins rst a c).vals = (stepCell env st ins false a' c).vals := by
        rw [stepCell_other hne, stepCell_other hne, h1]
      have hs : (stepCell env st ins rst a c).subs = a.subs := by rw [stepCell_other hne]
      have hs' : (stepCell env st ins false a' c).subs = a'.subs := by rw [stepCell_other hne]
      have ih := childEnc_rst henv hE hK hL st ins rst cs _ _ hv (by rw [hs, hs', h2])
      rw [hs] at ih
      have hi' : instModsL (c :: cs) = instModsL cs := by
        unfold instModsL
        rw [List.filterMap_cons]
        have hn : (match c.op with | .inst j _ _ => some j | _ => none : Option Nat) = none := by
          split
          · rename_i j args outs hop; exact absurd hop (hne j args outs)
          · rfl
        simp only [hn]
      simp only [List.foldl_cons]
      rw [childEnc_other E c cs _ _ hne, childEnc_other E c cs _ _ hne, childEnc_other E c cs _ _ hne, hi', ih]

theorem childE_length (d : Design) (k j : Nat) (s s' : Store) :
    (childE d k j s).length = (childE d k j s').length := by
  unfold childE; split
  · rw [encode_length, encode_length]
  · rfl

/-- Outputs ignore reset, and reset acts on the encoded state bit by bit. -/
theorem sem_reset (d : Design) (k : Nat) : ∀ (st : Store) (ins : Array Nat) (rst : Bool),
    (d.sem k st ins rst).1 = (d.sem k st ins false).1 ∧
    encode d k (d.sem k st ins rst).2 =
      applyReset (kinds d k) (encode d k st) (encode d k (d.sem k st ins false).2) rst := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st ins rst
    cases hm : d.modules[k]? with
    | none =>
      rw [Design.sem]; simp only [hm]
      rw [encode, kinds]; simp [hm, nullSem, applyReset]
    | some m =>
      have henv : ∀ j s x rst, (d.env k j s x rst).1 = (d.env k j s x false).1 := by
        intro j s x rst
        unfold Design.env; split
        · rename_i hj; exact (ih j hj s x rst).1
        · rfl
      let K : Nat → List ResetKind := fun j => if j < k then kinds d j else []
      have hE : ∀ j s x rst, childE d k j (d.env k j s x rst).2 =
          applyReset (K j) (childE d k j s) (childE d k j (d.env k j s x false).2) rst := by
        intro j s x rst
        unfold childE Design.env
        by_cases hj : j < k
        · simp only [K, hj, ite_true]; exact (ih j hj s x rst).2
        · simp [K, hj, applyReset]
      have hK : ∀ j s, (K j).length = (childE d k j s).length := by
        intro j s; unfold childE; by_cases hj : j < k
        · simp [K, hj, kinds_length, encode_length]
        · simp [K, hj]
      rw [Design.sem_eq d k m hm]
      have hf := foldl_rst henv st ins rst m.cells.toList ⟨#[], #[]⟩ ⟨#[], #[]⟩ rfl rfl
      have hvals : ∀ r, Module.values (d.env k) m st ins r =
          m.cells.toList.foldl (stepCell (d.env k) st ins r) ⟨#[], #[]⟩ := by
        intro r; unfold Module.values; rw [Array.foldl_toList]
      refine ⟨by simp only [Module.evalWith, hvals, hf.1], ?_⟩
      rw [encode_split d k m hm, encode_split d k m hm, encode_split d k m hm, kinds_eq d k m hm]
      simp only [Module.evalWith, hvals, hf.1, Store.subs_mk]
      have hc := childEnc_rst henv hE hK (childE_length d k) st ins rst m.cells.toList ⟨#[], #[]⟩ ⟨#[], #[]⟩ rfl rfl
      simp only [show ({ vals := #[], subs := #[] } : Acc).subs.size = 0 from rfl] at hc
      rw [hc, ← instMods_eq]
      rw [applyReset_append _ _ _ _ _ _ _ (by simp [regsEnc_length, memsEnc_length, regBits, memBits])
        (by simp [regsEnc_length, memsEnc_length])]
      rw [applyReset_append _ _ _ _ _ _ _ (by simp [regsEnc_length, regBits]) (by simp [regsEnc_length])]
      congr 2
      · rw [regsEnc_next, regsEnc_next, regsEnc, ← flatMap_zipIdx_fst regKinds m.regs.toList 0,
          ← flatMap_zipIdx_fst (fun r => bitsOf r.width (Reg.update rst _ r)) m.regs.toList 0,
          ← flatMap_zipIdx_fst (fun r => bitsOf r.width (Reg.update false _ r)) m.regs.toList 0]
        rw [applyReset_flatMap rst (fun p : Reg × Nat => regKinds p.1)
          (fun p => bitsOf p.1.width (st.regs.getD p.2 0))
          (fun p => bitsOf p.1.width (Reg.update false _ p.1)) (by simp) (by simp)]
        congr 1
        funext p
        exact reg_reset p.1 _ _ rst
      · rw [applyReset_unreset' _ _ _ _ (memsEnc_length _ _) (memsEnc_length _ _)]
        rfl

end HDLean.Rtl.Blast
