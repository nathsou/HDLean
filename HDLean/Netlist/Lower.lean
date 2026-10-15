import HDLean.Netlist.Basic
namespace HDLean

def lowerExpr : Expr d i r → Netlist.Node d i r
  | .lit b => .lit b
  | .input k => .input k
  | .reg k => .reg k
  | .inv a => .inv (lowerExpr a)
  | .and a b => .and (lowerExpr a) (lowerExpr b)
  | .xor a b => .and (.inv (.and (lowerExpr a) (lowerExpr b)))
      (.inv (.and (.inv (lowerExpr a)) (.inv (lowerExpr b))))
  | .mux c a b => .inv (.and (.inv (.and (lowerExpr c) (lowerExpr a)))
      (.inv (.and (.inv (lowerExpr c)) (lowerExpr b))))

theorem lowerExpr_correct (e : Expr d i r) (xs s) :
    (lowerExpr e).eval xs s = e.eval xs s := by
  induction e with
  | lit b => rfl
  | input k => rfl
  | reg k => rfl
  | inv a ih => simp [lowerExpr, Netlist.Node.eval, Expr.eval, ih]
  | and a b ha hb => simp [lowerExpr, Netlist.Node.eval, Expr.eval, ha, hb]
  | xor a b ha hb =>
    simp only [lowerExpr, Netlist.Node.eval, Expr.eval, ha, hb]
    cases a.eval xs s <;> cases b.eval xs s <;> rfl
  | mux c a b hc ha hb =>
    simp only [lowerExpr, Netlist.Node.eval, Expr.eval, hc, ha, hb]
    cases c.eval xs s <;> cases a.eval xs s <;> cases b.eval xs s <;> rfl

def lower (c : Circuit d i r o) : Netlist.Module d i r o where
  name := c.name
  state := c.state.map fun reg => ⟨reg.name, reg.reset, lowerExpr reg.next, reg.source⟩
  output := c.output.map lowerExpr
  inputNames := c.inputNames
  outputNames := c.outputNames

/-- All state transitions, including synchronous reset, survive lowering. -/
theorem lower_next (c : Circuit d i r o) (s xs) : (lower c).next s xs = c.next s xs := by
  funext k
  simp [Netlist.Module.next, lower, Circuit.next, lowerExpr_correct] <;> rfl

/-- The same proved term supplies every emitted output. -/
theorem lower_output (c : Circuit d i r o) (s xs) :
    (lower c).evalOutput s xs = c.evalOutput s xs := by
  funext k
  simp [Netlist.Module.evalOutput, lower, Circuit.evalOutput, lowerExpr_correct]

@[simp] theorem lower_ffBits (c : Circuit d i r o) : (lower c).ffBits = r := rfl
end HDLean
