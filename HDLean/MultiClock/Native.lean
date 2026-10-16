import HDLean.MultiClock.Dag
import HDLean.Backend.StatePorts
import HDLean.Backend.DagEmit

namespace HDLean.MultiClock.Shared.MultiDag
variable (c : MultiDag nd)

/-- Per-domain modules expose registered source bits as ordinary output pins.
Synchronizers connect those pins; no local expression reads foreign storage. -/
def nativeLower : c.Graph :=
  { c.lower with modules := fun d => (c.logic d).lower.withStatePorts }

theorem nativeLower_correct (s : c.State) (e : c.Event) :
    c.nativeLower.eval s e = (c.next s e,c.output s e) := by
  have ht (d : Fin nd) := Backend.Graph.withStatePorts_eval (c.logic d).lower
    ((Vector.ofFn (c.localInput s e d)).toArray.push (e.reset d))
    (Vector.ofFn (s.registers d)).toArray (by simp) (by simp)
  have hl (d : Fin nd) := Dag.lower_correct (c.logic d)
    (Vector.ofFn (c.localInput s e d)) (Vector.ofFn (s.registers d)) (e.reset d)
  have hfn (d : Fin nd) : (fun k => (Vector.ofFn (s.registers d))[k]) = s.registers d := by funext k; simp
  have hfi (d : Fin nd) : (fun k => (Vector.ofFn (c.localInput s e d))[k]) = c.localInput s e d := by funext k; simp
  simp only [hfn,hfi] at hl
  unfold nativeLower lower Graph.eval
  simp only [ht,hl,Array.getElem?_append,Vector.size_toArray,Vector.getElem?_toArray,
    Vector.getElem?_ofFn,Fin.isLt,↓reduceDIte,Option.getD_some]
  rfl

theorem nativeLower_wellFormed (d : Fin nd) : (c.nativeLower.modules d).wellFormed = true :=
  Backend.Graph.withStatePorts_wellFormed _ (Dag.lower_wellFormed _)

end HDLean.MultiClock.Shared.MultiDag
