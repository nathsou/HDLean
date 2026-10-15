import HDLean.Semantics.Composition
namespace HDLean

/-- Feedback wiring reads only pre-edge Moore outputs; all component state updates are simultaneous. -/
def Machine.network (count : Nat) (m : Fin count → Machine σ ι ο)
    (wire : κ → (Fin count → ο) → Fin count → ι) : Machine (Fin count → σ) κ (Fin count → ο) where
  init k := (m k).init
  out s k := (m k).out (s k)
  next s i k := (m k).next (s k) (wire i (fun j => (m j).out (s j)) k)

/-- Local simulation relations compose across an arbitrary Moore feedback network. -/
theorem network_refines (count : Nat) (a : Fin count → Machine σ ι ο) (b : Fin count → Machine τ ι ο)
    (wire : κ → (Fin count → ο) → Fin count → ι)
    (R : Fin count → σ → τ → Prop)
    (hinit : ∀ k, R k (a k).init (b k).init)
    (hnext : ∀ k s q i, R k s q → R k ((a k).next s i) ((b k).next q i))
    (hout : ∀ k s q, R k s q → (a k).out s = (b k).out q) :
    Refines (Machine.network count a wire) (Machine.network count b wire) id := by
  apply Machine.refines_of_simulation _ _ _ (fun s q => ∀ k, R k (s k) (q k))
  · exact hinit
  · intro s q i h k
    have ho : (fun j => (a j).out (s j)) = (fun j => (b j).out (q j)) := by
      funext j
      exact hout j _ _ (h j)
    simp only [Machine.network]
    rw [ho]
    exact hnext k _ _ _ (h k)
  · intro s q h
    funext k
    exact hout k _ _ (h k)
end HDLean
