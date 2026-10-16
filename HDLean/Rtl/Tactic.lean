import HDLean.Rtl.Hoare
import Lean.Elab.Tactic

/-!
# Tactics for builder proofs

`rtl_let x, hx ← lemma` runs one builder step: it applies `ensures_bind` with the
primitive lemma, names the returned handle `x` and its specification `hx`, and
transports every `Refines` fact about the previous state to the new state.
-/
namespace HDLean.Rtl.Build

open Lean Elab Tactic Meta

/-- Transport every hypothesis `h : F .. s ..` that has a lemma `F.mono h ext`
along `ext : Extends s t` (`Refines`, `HRefines`, `BRefines`, ...). -/
elab "rtl_mono " ext:ident : tactic => withMainContext do
  let some extDecl := (← getLCtx).findFromUserName? ext.getId
    | throwError "rtl_mono: unknown hypothesis {ext.getId}"
  let extTy ← instantiateMVars extDecl.type
  unless extTy.isAppOfArity ``Extends 3 do
    throwError "rtl_mono: {ext.getId} is not an `Extends` fact"
  let src := extTy.getArg! 1
  let env ← getEnv
  let mut names : Array Name := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail || decl.userName.hasMacroScopes then continue
    let ty ← instantiateMVars decl.type
    let some head := ty.getAppFn.constName? | continue
    unless env.contains (head ++ `mono) do continue
    if ty.getAppArgs.any (· == src) then
      names := names.push decl.userName
  for n in names do
    try
      evalTactic (← `(tactic| replace $(mkIdent n):ident := $(mkIdent n).mono $ext))
    catch _ => pure ()

/-- One builder step: `rtl_let x, hx ← lemma`. -/
syntax "rtl_let " ident ", " ident " ← " term : tactic
macro_rules
  | `(tactic| rtl_let $x, $hx ← $lem) =>
    `(tactic| (apply ensures_bind ($lem); intro $x _ rtl_ext $hx; rtl_mono rtl_ext; clear rtl_ext))

end HDLean.Rtl.Build
