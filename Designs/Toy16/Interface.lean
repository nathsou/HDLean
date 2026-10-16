import Designs.Toy16.Spec
import HDLean.Core.WordBank

namespace HDLean.Toy16

/-- A two-stage fetch/execute core. Serialization avoids forwarding and branch-flush hazards. -/
structure CoreState where
  arch : ArchState
  fetched : Word
  execute : Bool

namespace Physical
open WordExpr

/-- Uniform 16-bit bank: PC, halted, execute, fetched instruction, eight registers,
and 256 data words. Narrow controls use their low bits. -/
abbrev W (n : Nat) := WordExpr 0 0 (268*16) n
abbrev E := Expr 0 0 (268*16)

def word (j : Fin 268) : W 16 := bankWord j

def pc : W 8 := extract (word ⟨0, by decide⟩) 0 8 (by decide)
def halted : E := (word ⟨1, by decide⟩)[0]
def execute : E := (word ⟨2, by decide⟩)[0]
def fetched : W 16 := word ⟨3, by decide⟩

def regWord (j : Fin 8) : W 16 := word ⟨4+j.val, by omega⟩
def memWord (j : Fin 256) : W 16 := word ⟨12+j.val, by omega⟩
def decode (s : Fin (268*16) → Bool) : CoreState :=
  { arch := { pc := pc.eval Fin.elim0 s
              halted := halted.eval Fin.elim0 s
              regs := fun r => (regWord r.toFin).eval Fin.elim0 s
              dmem := fun a => (memWord a.toFin).eval Fin.elim0 s }
    fetched := fetched.eval Fin.elim0 s
    execute := execute.eval Fin.elim0 s }

/-- Decode the emitted retirement bus; invalid fields are intentionally ignored. -/
def readOutput (bits : Fin 79 → Bool) (offset width : Nat) (h : offset+width ≤ 79) : BitVec width :=
  (WordExpr.inputs offset h : WordExpr 0 79 0 width).eval bits Fin.elim0

def observe (bits : Fin 79 → Bool) : Option Retire :=
  if bits 0 then some
    { pc := readOutput bits 1 8 (by decide)
      instr := readOutput bits 9 16 (by decide)
      nextPc := readOutput bits 25 8 (by decide)
      wb := if bits 33 then some (readOutput bits 34 3 (by decide), readOutput bits 37 16 (by decide)) else none
      store := if bits 53 then some (readOutput bits 54 8 (by decide), readOutput bits 62 16 (by decide)) else none
      halt := bits 78 } else none

end Physical
end HDLean.Toy16
