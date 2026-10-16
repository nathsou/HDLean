import HDLean.Core.Circuit
import HDLean.Core.Word
import HDLean.Core.Allocate
import Lean

namespace HDLean

class HardwareEq (α : Type) (result : outParam Type) where
  equal : α → α → result

instance (priority := 100) [BEq α] : HardwareEq α Bool := ⟨BEq.beq⟩
instance (priority := 1000) : HardwareEq (Expr d i r) (Expr d i r) :=
  ⟨fun a b => .inv (.xor a b)⟩
instance (priority := 1000) : HardwareEq (WordExpr d i r w) (Expr d i r) := ⟨WordExpr.equal⟩

class HardwareMux (condition α : Type) where
  select : condition → α → α → α

instance : HardwareMux Bool α := ⟨fun condition a b => if condition then a else b⟩
instance : HardwareMux (Expr d i r) (Expr d i r) := ⟨Expr.mux⟩
instance : HardwareMux (Expr d i r) (WordExpr d i r w) := ⟨WordExpr.mux⟩

class HardwareLogic (α : Type) where
  conjunction : α → α → α
  disjunction : α → α → α
  negate : α → α

instance : HardwareLogic Bool := ⟨(· && ·), (· || ·), (! ·)⟩
instance : HardwareLogic (Expr d i r) := ⟨Expr.and, Expr.or, Expr.inv⟩

private def asTerm (stx : Lean.Syntax) : Lean.TSyntax `term := ⟨stx⟩

/-- Syntax expansion only constructs ordinary typed AST builders. The generated
term and every subsequent semantic proof are checked by the kernel. -/
private partial def hardwareSyntax (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  match stx with
  | `(term| if $c then $a else $b) =>
    `(HardwareMux.select $(asTerm (← hardwareSyntax c)) $(asTerm (← hardwareSyntax a)) $(asTerm (← hardwareSyntax b)))
  | `(term| $a == $b) => `(HardwareEq.equal $(asTerm (← hardwareSyntax a)) $(asTerm (← hardwareSyntax b)))
  | `(term| $a && $b) => `(HardwareLogic.conjunction $(asTerm (← hardwareSyntax a)) $(asTerm (← hardwareSyntax b)))
  | `(term| $a || $b) => `(HardwareLogic.disjunction $(asTerm (← hardwareSyntax a)) $(asTerm (← hardwareSyntax b)))
  | `(term| !$a) => `(HardwareLogic.negate $(asTerm (← hardwareSyntax a)))
  | _ =>
    match stx with
    | .node info kind args => return .node info kind (← args.mapM hardwareSyntax)
    | other => return other

/-- `if`, equality and Boolean operators inside `circuit do` construct hardware.
Widths, clock domains and every register driver remain explicit in the result type.
Static propositions can use ordinary dependent `if h : proposition then ...`. -/
syntax "treeCircuit" " do " doSeq : term
macro_rules | `(treeCircuit do $body) => do
  let expanded : Lean.TSyntax ``Lean.Parser.Term.doSeq := ⟨← hardwareSyntax body⟩
  `(Id.run do $expanded)

/-- Each monadic binding allocates shared nodes or storage. Register handles
supply the physical index, and finalization rejects missing or duplicate drivers. -/
syntax "circuit" " do " doSeq : term
syntax "circuit" str " do " doSeq : term
macro_rules
  | `(circuit do $body) => `(Dag.Allocate.run "circuit" do $body)
  | `(circuit $name:str do $body) => `(Dag.Allocate.run $name do $body)

end HDLean
