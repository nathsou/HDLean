import HDLean.Netlist.DagLower
set_option backward.isDefEq.respectTransparency false

namespace HDLean.Backend

/-- Explicit old-state observation ports, used to wire typed synchronizers across
module boundaries. There is no new register or hidden power-up assumption. -/
def Graph.withStatePorts (g : Graph) : Graph :=
  { g with outputs := g.outputs ++ (Array.range g.latches).map (fun k => 2*(g.inputs+1+k))
           outputNames := g.outputNames ++ (Array.range g.latches).map (fun k => s!"state_{k}") }

theorem Graph.values_register (g : Graph) (inputs state : Array Bool)
    (hi : inputs.size = g.inputs) (k : Nat) (hk : k < state.size) :
    litValue (g.values inputs state) (2*(g.inputs+1+k)) = state[k] := by
  have he : g.values inputs state = Dag.run g.gates.toList (#[false] ++ inputs ++ state) := by
    simp [Graph.values,Dag.run,Array.foldl_toList]
  have hp := Dag.run_extends g.gates.toList (#[false] ++ inputs ++ state)
  have hb : g.inputs+1+k < (#[false] ++ inputs ++ state).size := by simp; omega
  change litValue (g.values inputs state) (Dag.Wire.mk (g.inputs+1+k) false).encode = _
  rw [Dag.Wire.litValue]
  simp only [Dag.Wire.value,Bool.xor_false]
  change Dag.read (g.values inputs state) (g.inputs+1+k) = _
  rw [he,hp.2 _ hb]
  simp [Dag.read,Array.getElem?_append,hi,show ¬g.inputs+1+k < 1+g.inputs by omega,
    show g.inputs+1+k-(1+g.inputs) = k by omega,hk]

/-- Adding state ports leaves every existing next-state/output equation intact. -/
theorem Graph.withStatePorts_eval (g : Graph) (inputs state : Array Bool)
    (hi : inputs.size = g.inputs) (hs : state.size = g.latches) :
    g.withStatePorts.eval inputs state =
      ((g.eval inputs state).1,(g.eval inputs state).2 ++ state) := by
  simp only [Graph.eval,Graph.withStatePorts,Array.map_append,Array.map_map]
  congr 2
  apply Array.ext
  · simp [hs]
  · intro k hk hk'
    have hkl : k < g.latches := by simpa using hk
    simp only [Array.getElem_map,Array.getElem_range]
    exact g.values_register inputs state hi k (by omega)

end HDLean.Backend

namespace HDLean.Backend
private theorem gateScan_cases (gs : List Gate) (start : Nat) :
    forIn gs (none,start) Dag.wfStep = (pure (none,start+gs.length) : Id (Option Bool × Nat)) ∨
    ∃ stop, forIn gs (none,start) Dag.wfStep = (pure (some false,stop) : Id (Option Bool × Nat)) := by
  induction gs generalizing start with
  | nil => exact Or.inl rfl
  | cons g gs ih =>
    simp only [List.forIn_cons,Dag.wfStep]
    split
    · exact Or.inr ⟨start,rfl⟩
    · simp only [pure_bind]
      have h := ih (start+1)
      rcases h with h | ⟨stop,h⟩
      · left
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
      · exact Or.inr ⟨stop,h⟩
end HDLean.Backend

namespace HDLean.Backend
 theorem Graph.withStatePorts_wellFormed (g : Graph) (hg : g.wellFormed = true) :
    g.withStatePorts.wellFormed = true := by
  unfold Graph.wellFormed at hg ⊢
  dsimp only [Graph.withStatePorts] at *
  simp only [Array.size_append,Array.size_map,Array.size_range] at *
  split at hg
  · contradiction
  · rename_i hd
    simp only [hd,Bool.false_eq_true,↓reduceIte]
    split at hg
    · contradiction
    · rename_i hm
      have hn : g.outputNames.size = g.outputs.size := by
        have hf := Bool.eq_false_iff.mpr hm
        have hlast := (Bool.or_eq_false_iff.mp hf).2
        simpa using hlast
      simp only [hn,bne_self_eq_false,Bool.or_false] at hm ⊢
      simp only [hm,Bool.false_eq_true,↓reduceIte]
      rcases gateScan_cases g.gates.toList (g.inputs+g.latches+1) with hs | ⟨stop,hs⟩
      · unfold Dag.wfStep at hs
        rw [hs] at hg ⊢
        dsimp only [Bind.bind,Id.instMonad,Pure.pure,Id.run] at hg ⊢
        simp only [Array.toList_append,List.all_append,Bool.and_eq_true] at hg ⊢
        refine ⟨hg.1,hg.2,?_⟩
        simp only [Array.toList_map,Array.toList_range,List.all_map,List.all_eq_true]
        intro k hk
        have hk' : k < g.latches := List.mem_range.mp hk
        simp only [Function.comp_apply,decide_eq_true_eq]
        rw [Nat.mul_div_cancel_left _ (by decide)]
        calc
          g.inputs+1+k < g.inputs+1+g.latches := Nat.add_lt_add_left hk' _
          _ = g.inputs+g.latches+1 := by simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          _ ≤ g.inputs+g.latches+1+g.gates.toList.length := Nat.le_add_right _ _
      · unfold Dag.wfStep at hs
        rw [hs] at hg
        contradiction
end HDLean.Backend
