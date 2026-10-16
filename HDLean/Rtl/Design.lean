import HDLean.Rtl.Record

/-!
# Designs: assembling modules

A design is a list of modules in dependency order. `Design.sem_eq` and
`Design.env_lt` are the composition principle: module `k` evaluates with the
semantics of the modules before it, so a parent's proof uses its children's
theorems as black boxes.
-/
namespace HDLean.Rtl

namespace Design

theorem env_lt (d : Design) {k j : Nat} (h : j < k) : d.env k j = d.sem j := by
  simp [env, h]

theorem env_zero (d : Design) (j : Nat) : d.env 0 j = nullSem := by simp [env]

/-- The cycle of the top module. -/
theorem step_eq (d : Design) (m : Module) (h : d.modules[d.top]? = some m) (st : Store) (x : Array Nat × Bool) :
    d.step st x = (m.evalWith (d.env d.top) st x.1 x.2).2 := by
  simp [step, sem_eq d d.top m h]

theorem output_eq (d : Design) (m : Module) (h : d.modules[d.top]? = some m) (st : Store) (ins : Array Nat) :
    d.output st ins = (m.evalWith (d.env d.top) st ins false).1 := by
  simp [output, sem_eq d d.top m h]

/-- Signatures available to module `k`. -/
def subsBefore (d : Design) (k : Nat) : Array (List Nat × List Nat) := d.signatures.extract 0 k

end Design


end HDLean.Rtl
