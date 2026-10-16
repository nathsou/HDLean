import Tests.Dag
import HDLean.Backend.DagEmit

namespace HDLean.Backend.Proved.Tests

/-- The same theorem covers every format and every initial state/reset value. -/
example (format : Format) (xs : Vector Bool 1) (s : Vector Bool 3) (rst : Bool) :
    format.meaning (format.emit Dag.Tests.exampleDag) (xs.toArray.push rst) s.toArray = some
      ((Vector.ofFn (Dag.Tests.exampleDag.nextState (fun k => s[k]) ((fun k => xs[k]),rst))).toArray,
       (Vector.ofFn (Dag.Tests.exampleDag.evalOutput (fun k => s[k]) (fun k => xs[k]))).toArray) :=
  emit_correct format Dag.Tests.exampleDag xs s rst

#print axioms HDLean.Backend.Proved.emit_correct
end HDLean.Backend.Proved.Tests
