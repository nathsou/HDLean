import HDLean.Semantics.Synth
import Lean.Elab.Deriving.Util
import Lean.Elab.Deriving.Basic

open Lean Meta Elab Command Deriving Parser Term

namespace HDLean

private def deriveSynthCommands (name : Name) : TermElabM (TSyntax `command) := do
  let info ← getConstInfoInduct name
  if info.isRec || info.numIndices != 0 then
    throwError "Synth requires a fixed finite layout; recursive/indexed inductives need an explicit encoding"
  let args ← mkInductArgNames info
  let implicitBinders ← mkImplicitBinders args
  let instanceBinders ← mkInstImplicitBinders ``Synth info args
  let binders : Array (TSyntax ``Parser.Term.bracketedBinder) :=
    (implicitBinders.map (·.raw) ++ instanceBinders).map (fun s => ⟨s⟩)
  let type ← mkInductiveApp info args
  let instName := mkIdent (← mkInstName ``Synth name)
  if let some structInfo := getStructureInfo? (← getEnv) name then
    let a := mkIdent `value
    let p := mkIdent `bits
    let mut packed ← `(())
    for field in structInfo.fieldNames.reverse do
      packed ← `(($a.$(mkIdent field):ident, $packed))
    let mut decoded := #[]
    let mut rest : TSyntax `term := p
    for _ in structInfo.fieldNames do
      decoded := decoded.push (← `(($rest).1))
      rest ← `(($rest).2)
    let ctor ← `($(mkCIdent info.ctors.head!) $decoded*)
    `(instance $instName:ident $binders:bracketedBinder* : HDLean.Synth $type :=
      HDLean.Synth.transport (fun $a : $type => $packed) (fun $p => $ctor)
        (by intro value; cases value; rfl))
  else
    if info.ctors.isEmpty then throwError "an empty type has no total hardware decoder"
    for ctor in info.ctors do
      let ctorInfo ← getConstInfoCtor ctor
      if ctorInfo.numFields != 0 then
        throwError "Synth derives structures and nullary enums; provide an explicit layout for sum payloads"
    let size := Syntax.mkNumLit (toString info.ctors.length)
    let mut encodeAlts : Array (TSyntax ``Parser.Term.matchAlt) := #[]
    let mut decodeAlts : Array (TSyntax ``Parser.Term.matchAlt) := #[]
    for ctor in info.ctors, k in [:info.ctors.length] do
      let tag := Syntax.mkNumLit (toString k)
      encodeAlts := encodeAlts.push (← `(matchAltExpr| | $(mkCIdent ctor) => (⟨$tag, by decide⟩ : Fin $size)))
      if k + 1 < info.ctors.length then
        decodeAlts := decodeAlts.push (← `(matchAltExpr| | $tag => $(mkCIdent ctor)))
    decodeAlts := decodeAlts.push (← `(matchAltExpr| | _ => $(mkCIdent info.ctors.getLast!)))
    let encode ← `(fun value : $type => match value with $encodeAlts:matchAlt*)
    let decode ← `(fun tag : Fin $size => match tag.val with $decodeAlts:matchAlt*)
    `(instance $instName:ident $binders:bracketedBinder* : HDLean.Synth $type :=
      HDLean.Synth.transport $encode $decode (by intro value; cases value <;> rfl))

private def deriveSynth (names : Array Name) : CommandElabM Bool := do
  for name in names do
    let command ← liftTermElabM (deriveSynthCommands name)
    elabCommand command
  return true

initialize registerDerivingHandler ``Synth deriveSynth

end HDLean
