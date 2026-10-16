import HDLean.Rtl.Mealy

/-!
# `hdl_record`: declaring a record of words

```
hdl_record CpuRegs where
  pc : 8
  acc : 16
```

declares `structure CpuRegs (F : Nat → Type)` with fields `pc : F 8`, `acc : F 16`,
and its `Bundle` instance. Parameters are allowed: `hdl_record RamIn (a w : Nat) where ...`.
-/
namespace HDLean.Rtl

open Lean Elab Command

declare_syntax_cat hdlField
syntax ident " : " term:max : hdlField

syntax (docComment)? "hdl_record " ident (ppSpace bracketedBinder)* " where" (ppLine hdlField)+ : command

private def fieldParts (stx : TSyntax `hdlField) : MacroM (TSyntax `ident × Term) :=
  match stx with
  | `(hdlField| $n:ident : $w) => pure (n, w)
  | _ => Macro.throwUnsupported

macro_rules
  | `($[$doc:docComment]? hdl_record $name:ident $binders:bracketedBinder* where $fields:hdlField*) => do
    let parts ← fields.mapM fieldParts
    let fNames := parts.map (·.1)
    let fWidths := parts.map (·.2)
    let F := mkIdent `F
    let structFields ← (parts.mapM fun (n, w) => `(Lean.Parser.Command.structSimpleBinder| $n:ident : $F $w))
    let binderNames : Array Term ← binders.foldlM (init := #[]) fun acc b => do
      match b with
      | `(bracketedBinder| ($ns:ident* : $_)) => pure (acc ++ ns.map fun n => (n : Term))
      | `(bracketedBinder| {$ns:ident* : $_}) => pure acc
      | _ => pure acc
    let applied : Term ← `($name $binderNames*)
    let r := mkIdent `r
    let v := mkIdent `v
    -- fields list
    let fieldList ← parts.mapM fun (n, w) => `(($(Lean.quote n.getId.toString), $w))
    -- toVec r := .cons r.f1 (.cons r.f2 .nil)
    let toVec ← fNames.foldrM (init := ← `(HVec.nil)) fun n acc => `(HVec.cons ($r).$n:ident $acc)
    -- ofVec v := ⟨v.head, v.tail.head, ...⟩
    let mut access : Array Term := #[]
    let mut cur : Term ← `($v)
    for _ in fNames do
      access := access.push (← `(HVec.head $cur))
      cur ← `(HVec.tail $cur)
    let ofVec ← `(⟨$access,*⟩)
    -- pattern .cons _ (.cons _ .nil)
    let pat ← fNames.foldrM (init := ← `(HVec.nil)) fun _ acc => `(HVec.cons _ $acc)
    `($[$doc:docComment]? structure $name:ident $binders:bracketedBinder* ($F : Nat → Type) where
        $structFields:structSimpleBinder*
      instance $binders:bracketedBinder* : Bundle ($applied) where
        fields := [$fieldList,*]
        toVec := fun $r => $toVec
        ofVec := fun $v => $ofVec
        ofVec_toVec := fun _ => rfl
        toVec_ofVec := fun $v => match $v:ident with | $pat => rfl)

end HDLean.Rtl
