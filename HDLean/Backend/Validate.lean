import HDLean.Netlist.Optimize
import HDLean.Rtl.Blast.Vec
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Sat.AIG.CNF

/-!
# Translation validation of external optimisers

An external optimiser (ABC, Yosys) returns a graph `h` for our graph `g`. It is
not trusted. `Validate.select g h cert` keeps `h`'s logic, with `g`'s ports and
names, only if

* `h` is well formed, and
* `cert` is an LRAT refutation of the miter of `g` and `h`: one AIG over shared
  atoms for the inputs and latches, the XOR of each pair of next-state and
  output literals, all ORed together. The CNF is Lean's verified Tseitin
  encoding (`AIG.toCNF`), the certificate is checked by Lean's verified LRAT
  checker (`LRAT.check`).

Otherwise it returns `g`. `select_eval`: the result has `g`'s next state and
outputs for every input and state. The optimiser, the SAT solver that produced
`cert` and the AIGER reader are all outside the trusted base; the trust is the
compiled checker, as for the read-back of emitted files.
-/
namespace HDLean.Backend.Validate
open Std.Sat Std.Sat.AIG Std.Tactic.BVDecide HDLean.Rtl.Blast HDLean.Dag

/-- The fanin of an old literal; out of range, the constant (as `litValue` reads it). -/
def litFanin (fs : Array Fanin) (l : Nat) : Fanin := (fs.getD (l / 2) (fconst false)).flip (l % 2 == 1)

/-- Variable 0 is the constant, variable `v ≥ 1` is atom `v - 1`. -/
def baseFanins : Nat → AIG Nat → Array Fanin × AIG Nat
  | 0, aig => (#[fconst false], aig)
  | n + 1, aig =>
    let p := baseFanins n aig
    let e := p.2.mkAtomCached n
    (p.1.push (Fanin.mk e.ref.gate e.ref.invert), e.aig)

/-- A graph's gates over existing fanins. -/
def gatesFanins : List Gate → Array Fanin → AIG Nat → Option (Array Fanin × AIG Nat)
  | [], fs, aig => some (fs, aig)
  | gt :: gs, fs, aig =>
    match gate2 mkAndCached (litFanin fs gt.a) (litFanin fs gt.b) aig with
    | some (r, aig') => gatesFanins gs (fs.push r) aig'
    | none => none

/-- OR of the XORs of literal pairs `k ∈ ks`. -/
def orFold (fg fh : Array Fanin) (ga ha : Array Nat) : List Nat → Fanin → AIG Nat → Option (Fanin × AIG Nat)
  | [], acc, aig => some (acc, aig)
  | k :: ks, acc, aig =>
    match gate2 mkXorCached (litFanin fg (ga.getD k 0)) (litFanin fh (ha.getD k 0)) aig with
    | some (x, aig1) =>
      match gate2 mkOrCached acc x aig1 with
      | some (acc', aig2) => orFold fg fh ga ha ks acc' aig2
      | none => none
    | none => none

/-- The miter of two graphs with the same ports. -/
def miter (g h : Graph) : Option (Entrypoint Nat) :=
  let base := baseFanins (g.inputs + g.latches) AIG.empty
  match gatesFanins g.gates.toList base.1 base.2 with
  | none => none
  | some (fg, aig1) =>
    match gatesFanins h.gates.toList base.1 aig1 with
    | none => none
    | some (fh, aig2) =>
      if g.next.size = h.next.size ∧ g.outputs.size = h.outputs.size then
        match orFold fg fh (g.next ++ g.outputs) (h.next ++ h.outputs)
            (List.range (g.next ++ g.outputs).size) (fconst false) aig2 with
        | some (r, aig3) => if hr : r.gate < aig3.decls.size then some ⟨aig3, ⟨r.gate, r.invert, hr⟩⟩ else none
        | none => none
      else none

/-- `cert` refutes the miter of `g` and `h`. -/
def check (g h : Graph) (cert : Array LRAT.IntAction) : Bool :=
  match miter g h with
  | some e => LRAT.check cert (AIG.toCNF e)
  | none => false

/-- `h`'s logic under `g`'s ports and names. -/
def adopt (g h : Graph) : Graph := { g with gates := h.gates, next := h.next, outputs := h.outputs }

/-- The external graph if validated, else ours. -/
def select (g h : Graph) (cert : Array LRAT.IntAction) : Graph :=
  if (adopt g h).wellFormed && check g (adopt g h) cert then adopt g h else g

/-! ## Soundness -/

/-- Fanins denote the values of the variables. -/
def FansOk (aig : AIG Nat) (assign : Nat → Bool) (fs : Array Fanin) (V : Array Bool) : Prop :=
  fs.size = V.size ∧ ∀ v (hv : v < fs.size), BitIs aig assign fs[v] (Dag.read V v)

theorem FansOk.mono {aig aig' : AIG Nat} {assign : Nat → Bool} {fs : Array Fanin} {V : Array Bool}
    (h : FansOk aig assign fs V) (hp : IsPrefix aig.decls aig'.decls) : FansOk aig' assign fs V :=
  ⟨h.1, fun v hv => BitIs.mono (h.2 v hv) hp⟩

theorem bitIs_flip {aig : AIG Nat} {assign : Nat → Bool} {f : Fanin} {c : Bool} (h : BitIs aig assign f c)
    (b : Bool) : BitIs aig assign (f.flip b) (c ^^ b) := by
  obtain ⟨hb, hd⟩ := h
  refine ⟨by rw [Fanin.gate_flip]; exact hb, ?_⟩
  simp only [Fanin.gate_flip, Fanin.invert_flip]
  rw [denote_inv] at hd ⊢
  rw [← hd]
  cases f.invert <;> cases b <;> simp

theorem const_bitIs (aig : AIG Nat) (assign : Nat → Bool) (b : Bool) : BitIs aig assign (fconst b) b := by
  obtain ⟨hb, hd⟩ := const_bit aig assign b
  exact ⟨hb, hd⟩

theorem litFanin_ok {aig : AIG Nat} {assign : Nat → Bool} {fs : Array Fanin} {V : Array Bool}
    (h : FansOk aig assign fs V) (l : Nat) : BitIs aig assign (litFanin fs l) (litValue V l) := by
  unfold litFanin
  rw [litValue_eq_read]
  by_cases hl : l / 2 < fs.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl, Option.getD_some]
    exact bitIs_flip (h.2 _ hl) _
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
    have : Dag.read V (l / 2) = false := by
      simp [Dag.read, Array.getElem?_eq_none (show V.size ≤ l / 2 by rw [← h.1]; omega)]
    rw [this]
    exact bitIs_flip (const_bitIs aig assign false) _

theorem baseFanins_size : ∀ (n : Nat) (aig : AIG Nat), (baseFanins n aig).1.size = n + 1
  | 0, _ => rfl
  | n + 1, aig => by simp [baseFanins, baseFanins_size n aig]

theorem read_extract (B : Array Bool) (m j : Nat) (hj : j < m) : Dag.read (B.extract 0 m) j = Dag.read B j := by
  unfold Dag.read
  rw [Array.getElem?_extract]
  split
  · simp
  · rename_i h
    rw [Array.getElem?_eq_none (by omega)]

theorem baseFanins_ok (B : Array Bool) (hB0 : Dag.read B 0 = false) :
    ∀ (n : Nat) (aig : AIG Nat), n + 1 ≤ B.size →
      IsPrefix aig.decls (baseFanins n aig).2.decls ∧
      FansOk (baseFanins n aig).2 (fun k => Dag.read B (k + 1)) (baseFanins n aig).1 (B.extract 0 (n + 1))
  | 0, aig, hn => by
    refine ⟨IsPrefix.refl' aig, by rw [baseFanins_size, Array.size_extract]; omega, fun v hv => ?_⟩
    rw [baseFanins_size] at hv
    have : v = 0 := by omega
    subst this
    rw [read_extract _ _ _ (by omega), hB0]
    exact const_bitIs _ _ false
  | n + 1, aig, hn => by
    obtain ⟨p, hs, hb⟩ := baseFanins_ok B hB0 n aig (by omega)
    have pe := LawfulOperator.isPrefix_aig (f := mkAtomCached) (baseFanins n aig).2 n
    have sz := baseFanins_size n aig
    refine ⟨IsPrefix.trans' p pe, by rw [baseFanins_size, Array.size_extract]; omega, fun v hv => ?_⟩
    rw [baseFanins_size] at hv
    simp only [baseFanins]
    rw [Array.getElem_push]
    split
    · rename_i hlt
      rw [sz] at hlt
      rw [read_extract _ _ _ (by omega), ← read_extract B (n + 1) v hlt]
      exact BitIs.mono (hb v (by rw [sz]; exact hlt)) pe
    · have hv' : v = n + 1 := by
        rename_i hge; rw [sz] at hge; omega
      obtain ⟨hb', hd⟩ := entry_bit ((baseFanins n aig).2.mkAtomCached n) (fun k => Dag.read B (k + 1))
      refine ⟨hb', ?_⟩
      rw [hd, mkAtomCached_eval_eq_mkAtom_eval, denote_mkAtom, hv', read_extract _ _ _ (by omega)]

theorem gatesFanins_ok {assign : Nat → Bool} :
    ∀ (gs : List Gate) (fs : Array Fanin) (V : Array Bool) (aig : AIG Nat) (fs' : Array Fanin) (aig' : AIG Nat),
      FansOk aig assign fs V → gatesFanins gs fs aig = some (fs', aig') →
      IsPrefix aig.decls aig'.decls ∧ FansOk aig' assign fs' (run gs V)
  | [], fs, V, aig, fs', aig', h, he => by
    simp only [gatesFanins, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨IsPrefix.refl' _, h⟩
  | gt :: gs, fs, V, aig, fs', aig', h, he => by
    obtain ⟨r, aig1, hg, hp, hr⟩ := gate2_ok mkAndCached (· && ·) (fun _ _ _ => denote_mkAndCached)
      (litFanin_ok h gt.a) (litFanin_ok h gt.b)
    simp only [gatesFanins, hg] at he
    have hnext : FansOk aig1 assign (fs.push r) (V.push (litValue V gt.a && litValue V gt.b)) := by
      refine ⟨by simp [h.1], fun v hv => ?_⟩
      simp only [Array.size_push] at hv
      rw [Array.getElem_push]
      split
      · rename_i hlt
        have : Dag.read (V.push (litValue V gt.a && litValue V gt.b)) v = Dag.read V v := by
          simp [Dag.read, Array.getElem?_push, show v ≠ V.size by rw [← h.1]; omega]
        rw [this]; exact BitIs.mono (h.2 v hlt) hp
      · have hv' : v = V.size := by rw [← h.1]; omega
        have : Dag.read (V.push (litValue V gt.a && litValue V gt.b)) v = (litValue V gt.a && litValue V gt.b) := by
          simp [Dag.read, hv']
        rw [this]; exact hr
    obtain ⟨hp', hok⟩ := gatesFanins_ok gs _ _ aig1 fs' aig' hnext he
    exact ⟨IsPrefix.trans' hp hp', by simpa [run] using hok⟩

theorem orFold_ok {assign : Nat → Bool} (fg fh : Array Fanin) (Vg Vh : Array Bool) (ga ha : Array Nat) :
    ∀ (ks : List Nat) (acc : Fanin) (c : Bool) (aig : AIG Nat) (r : Fanin) (aig' : AIG Nat),
      FansOk aig assign fg Vg → FansOk aig assign fh Vh → BitIs aig assign acc c →
      orFold fg fh ga ha ks acc aig = some (r, aig') →
      ∃ c', BitIs aig' assign r c' ∧
        (c' = false → c = false ∧ ∀ k ∈ ks, litValue Vg (ga.getD k 0) = litValue Vh (ha.getD k 0))
  | [], acc, c, aig, r, aig', _, _, hacc, he => by
    simp only [orFold, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨c, hacc, fun h => ⟨h, by simp⟩⟩
  | k :: ks, acc, c, aig, r, aig', hg, hh, hacc, he => by
    obtain ⟨x, aig1, hx, hp1, hxb⟩ := gate2_ok mkXorCached (· ^^ ·) (fun _ _ _ => denote_mkXorCached)
      (litFanin_ok hg (ga.getD k 0)) (litFanin_ok hh (ha.getD k 0))
    obtain ⟨acc', aig2, ho, hp2, hob⟩ := gate2_ok mkOrCached (· || ·) (fun _ _ _ => denote_mkOrCached)
      (BitIs.mono hacc hp1) hxb
    simp only [orFold, hx, ho] at he
    have hp := IsPrefix.trans' hp1 hp2
    obtain ⟨c', hr, himp⟩ := orFold_ok fg fh Vg Vh ga ha ks acc' _ aig2 r aig' (hg.mono hp) (hh.mono hp) hob he
    refine ⟨c', hr, fun hc => ?_⟩
    obtain ⟨h1, h2⟩ := himp hc
    simp only [Bool.or_eq_false_iff] at h1
    refine ⟨h1.1, fun j hj => ?_⟩
    rcases List.mem_cons.mp hj with rfl | hj
    · have := h1.2
      revert this
      cases litValue Vg (ga.getD j 0) <;> cases litValue Vh (ha.getD j 0) <;> simp
    · exact h2 j hj

theorem miter_sound (g h : Graph) (e : Entrypoint Nat) (hm : miter g h = some e) (hu : e.Unsat)
    (inputs state : Array Bool) (hi : inputs.size = g.inputs) (hs : state.size = g.latches) :
    g.eval inputs state = h.eval inputs state := by
  let B := #[false] ++ inputs ++ state
  have hn : B.size = g.inputs + g.latches + 1 := by simp [B, hi, hs]; omega
  have hB0 : Dag.read B 0 = false := by simp [B, Dag.read, Array.getElem?_append]
  let assign := fun k => Dag.read B (k + 1)
  obtain ⟨-, hbase⟩ := baseFanins_ok B hB0 (g.inputs + g.latches) AIG.empty (by omega)
  have hBx : B.extract 0 (g.inputs + g.latches + 1) = B := by
    rw [← hn]; exact Array.extract_size
  rw [hBx] at hbase
  unfold miter at hm
  simp only at hm
  split at hm
  · cases hm
  rename_i fg aig1 h1
  split at hm
  · cases hm
  rename_i fh aig2 h2
  split at hm
  · rename_i hsz
    split at hm
    · rename_i r aig3 h3
      split at hm
      · rename_i hr
        cases hm
        obtain ⟨p1, ok1⟩ := gatesFanins_ok (assign := assign) _ _ _ _ _ _ hbase h1
        obtain ⟨p2, ok2⟩ := gatesFanins_ok (assign := assign) _ _ _ _ _ _ (hbase.mono p1) h2
        obtain ⟨c', hr', himp⟩ := orFold_ok fg fh (run g.gates.toList B) (run h.gates.toList B) _ _ _ _ false
          aig2 r aig3 (ok1.mono p2) ok2 (const_bitIs _ _ false) h3
        have hc : c' = false := by
          obtain ⟨hb, hd⟩ := hr'
          rw [← hd]; exact hu assign
        have heq := (himp hc).2
        have pt : ∀ k (hk : k < (g.next ++ g.outputs).size),
            litValue (run g.gates.toList B) (g.next ++ g.outputs)[k] =
              litValue (run h.gates.toList B) ((h.next ++ h.outputs)[k]'(by simp at hk ⊢; omega)) := by
          intro k hk
          have := heq k (List.mem_range.mpr hk)
          rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some,
            Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simp at hk ⊢; omega), Option.getD_some] at this
        simp only [Graph.eval, Graph.values_run]
        apply Prod.ext
        · apply Array.ext (by simp [hsz.1])
          intro k h1' h2'
          simp only [Array.getElem_map]
          have hk : k < g.next.size := by simpa using h1'
          have := pt k (by simp; omega)
          rwa [Array.getElem_append_left hk, Array.getElem_append_left (by omega)] at this
        · apply Array.ext (by simp [hsz.2])
          intro k h1' h2'
          simp only [Array.getElem_map]
          have hk : k < g.outputs.size := by simpa using h1'
          have := heq (g.next.size + k) (List.mem_range.mpr (by simp; omega))
          rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
            Array.getElem?_append_right (by omega), Array.getElem?_append_right (by omega), hsz.1,
            Nat.add_sub_cancel_left, Array.getElem?_eq_getElem hk,
            Array.getElem?_eq_getElem (show k < h.outputs.size by omega)] at this
          exact this
      · cases hm
    · cases hm
  · cases hm

theorem check_sound (g h : Graph) (cert : Array LRAT.IntAction) (hc : check g h cert = true)
    (inputs state : Array Bool) (hi : inputs.size = g.inputs) (hs : state.size = g.latches) :
    g.eval inputs state = h.eval inputs state := by
  unfold check at hc
  split at hc
  · rename_i e he
    exact miter_sound g h e he ((toCNF_equisat e).mp (LRAT.check_sound cert _ hc)) inputs state hi hs
  · cases hc

/-- The selected graph computes what `g` computes. -/
theorem select_eval (g h : Graph) (cert : Array LRAT.IntAction) (inputs state : Array Bool)
    (hi : inputs.size = g.inputs) (hs : state.size = g.latches) :
    (select g h cert).eval inputs state = g.eval inputs state := by
  unfold select
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact (check_sound g (adopt g h) cert hc.2 inputs state hi hs).symm
  · rfl

theorem select_wellFormed (g h : Graph) (cert : Array LRAT.IntAction) (hg : g.wellFormed = true) :
    (select g h cert).wellFormed = true := by
  unfold select
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact hc.1
  · exact hg

@[simp] theorem select_inputs (g h : Graph) (cert : Array LRAT.IntAction) : (select g h cert).inputs = g.inputs := by
  unfold select; split <;> rfl

@[simp] theorem select_latches (g h : Graph) (cert : Array LRAT.IntAction) : (select g h cert).latches = g.latches := by
  unfold select; split <;> rfl

end HDLean.Backend.Validate
