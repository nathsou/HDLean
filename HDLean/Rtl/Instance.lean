import HDLean.Rtl.Design

/-!
# Instances

`instantiate j ins outs args` places module `j` (with input widths `ins` and
output widths `outs`) inside the module under construction and returns its
outputs as typed handles. `instantiate_ensures` states their values through the
semantics `e.sem j` of the child on its own store slot, which `Design.env_lt`
identifies with the child's `Design.sem`: the parent's proof uses the child's
theorem as a black box.
-/
namespace HDLean.Rtl

theorem pack_slice : ∀ (ws vs : List Nat) (k : Nat) (hk : k < ws.length),
    (pack ws vs >>> (ws.take k).sum) % 2 ^ ws[k] = vs.getD k 0 % 2 ^ ws[k]
  | w :: ws, v :: vs, 0, _ => by
    simp only [pack, List.take_zero, List.sum_nil, Nat.shiftRight_zero, List.getElem_cons_zero,
      List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  | w :: ws, v :: vs, k + 1, hk => by
    simp only [pack, List.take_succ_cons, List.sum_cons, List.getElem_cons_succ, List.getD_cons_succ]
    rw [Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (v % 2 ^ w + _) w]
    rw [show (v % 2 ^ w + 2 ^ w * pack ws vs) / 2 ^ w = pack ws vs by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos w)),
        Nat.zero_add]]
    exact pack_slice ws vs k (by simpa using hk)
  | w :: ws, [], k, hk => by simp [pack]
  | [], _, _, hk => by simp at hk

namespace Build

def sliceAll (x : Sig W) : (ws : List Nat) → Nat → M c (HVec Sig ws)
  | [], _ => pure .nil
  | w :: ws, lo => do
    let y ← slice x lo w
    let ys ← sliceAll x ws (lo + w)
    pure (.cons y ys)

/-- An instance of module `j`; returns its outputs. -/
def instantiate (j : Nat) (ins outs : List Nat) (args : HVec Sig ins) : M c (HVec Sig outs) := do
  let x ← inst j (args.toList Sig.ref) outs
  sliceAll x outs 0

/-- Values of an instance's outputs, given its packed value. -/
def unpack (outs : List Nat) (vs : List Nat) : HVec BitVec outs := HVec.decode outs 0 (vs.getD · 0)

theorem extract_bv (P W lo w : Nat) (h : lo + w ≤ W) :
    (bv W P).extractLsb' lo w = bv w (P >>> lo) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', bv, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
    Nat.testBit_shiftRight]
  have : lo + i < W := by omega
  simp [this]

theorem sliceAll_ensures {x : Sig W} {f : Env → List Nat} (outs : List Nat) (hW : outs.sum ≤ W)
    (hpos : ∀ w ∈ outs, 0 < w) :
    ∀ (ws pre : List Nat) (s : State c), outs = pre ++ ws → Refines s x (fun e => bv W (pack outs (f e))) →
      Ensures s (sliceAll x ws pre.sum)
        (fun v t => HRefines t v (fun e => HVec.decode ws pre.length ((f e).getD · 0)))
  | [], _, s, _, _ => ensures_pure _ _ trivial
  | w :: ws, pre, s, hsplit, hx => by
    have hlen : pre.length < outs.length := by rw [hsplit]; simp
    have hw : outs[pre.length] = w := by simp [hsplit]
    have htake : outs.take pre.length = pre := by simp [hsplit]
    have hfit : pre.sum + w ≤ W := by
      have hsum : outs.sum = pre.sum + w + ws.sum := by rw [hsplit]; simp; omega
      omega
    unfold sliceAll
    rtl_let y, hy ← slice_ensures pre.sum w hx (hpos w (by rw [hsplit]; simp)) hfit
    have hrec := sliceAll_ensures outs hW hpos ws (pre ++ [w]) _ (by simp [hsplit]) hx
    rw [show (pre ++ [w]).sum = pre.sum + w by simp] at hrec
    apply ensures_bind hrec
    intro ys t ext hys
    rw [List.length_append, List.length_singleton] at hys
    refine ensures_pure _ _ ⟨?_, hys⟩
    refine ⟨(hy.mono ext).1, fun e => ?_⟩
    show t.val e y.ref = _
    rw [(hy.mono ext).2 e]
    dsimp only
    rw [extract_bv _ _ _ _ hfit]
    simp only [HVec.decode, HVec.head_cons]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have := pack_slice outs (f e) pre.length hlen
    rw [htake, hw] at this
    simp [bv, this]

/-- An instance of module `j`, whose signature in the scope is `(ins, outs)`. Its
outputs carry the child's outputs, computed from the argument values on the
child's store slot. -/
theorem HRefines.vals {s : State c} (e : Env) :
    ∀ {ws : List Nat} {v : HVec Sig ws} {f}, HRefines s v f →
      (v.toList Sig.ref).map (s.val e) = (f e).toList (fun x => x.toNat)
  | [], .nil, f, _ => by cases f e; rfl
  | _ :: _, .cons x xs, f, h => by
    simp only [HVec.toList, List.map_cons]
    rw [HVec.eta (f e)]
    simp only [HVec.toList]
    have h1 : s.val e x.ref = (f e).head.toNat := h.1.2 e
    have h2 : (xs.toList Sig.ref).map (s.val e) = ((f e).tail).toList (fun x => x.toNat) := HRefines.vals e h.2
    rw [h1, h2]

theorem HRefines.widths_map {s : State c} :
    ∀ {ws : List Nat} {v : HVec Sig ws} {f}, HRefines s v f →
      (v.toList Sig.ref).map (s.widths[·]?) = ws.map some
  | [], .nil, _, _ => rfl
  | _ :: _, .cons x xs, _, h => by
    simp only [HVec.toList, List.map_cons]
    have h1 : s.widths[x.ref]? = some _ := h.1.1
    have h2 : (xs.toList Sig.ref).map (s.widths[·]?) = _ := HRefines.widths_map h.2
    rw [h1, h2]

theorem instantiate_ensures {s : State c} (j : Nat) (ins outs : List Nat) {args : HVec Sig ins}
    {fa : Env → HVec BitVec ins} (ha : HRefines s args fa) (hsub : c.subs[j]? = some (ins, outs))
    (hpos : ∀ w ∈ outs, 0 < w) (hne : 0 < outs.sum) :
    Ensures s (instantiate j ins outs args) (fun v t => HRefines t v (fun e =>
      Build.unpack outs (e.sem j (e.st.subs.getD (slots s.cells) default)
        (((fa e).toList (fun x => x.toNat)).toArray) e.rst).1.toList)) := by
  have hv : (Op.inst j (args.toList Sig.ref) outs).valid c.scope s.widths outs.sum = true := by
    simp only [Op.valid, Ctx.scope, hsub, HRefines.widths_map ha, beq_self_eq_true, Bool.and_self]
  unfold instantiate
  apply ensures_bind (inst_ensures s j (args.toList Sig.ref) outs hne hv)
  intro x t ext hx
  have hargs : ∀ e : Env, (args.toList Sig.ref).toArray.map (s.val e ·) =
      ((fa e).toList (fun x => x.toNat)).toArray := by
    intro e
    rw [← HRefines.vals e ha]
    apply Array.ext'
    simp
  have hx' : Refines t x (fun e => bv outs.sum (pack outs (e.sem j (e.st.subs.getD (slots s.cells) default)
      (((fa e).toList (fun x => x.toNat)).toArray) e.rst).1.toList)) :=
    ⟨hx.1, fun e => by rw [hx.2 e, hargs e]⟩
  have := sliceAll_ensures (f := fun e => (e.sem j (e.st.subs.getD (slots s.cells) default)
      (((fa e).toList (fun x => x.toNat)).toArray) e.rst).1.toList) outs (Nat.le_refl _) hpos outs [] t rfl hx'
  exact this

end Build
end HDLean.Rtl
