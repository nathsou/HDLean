import HDLean.Semantics.Machine
namespace HDLean

/-- Single-port synchronous RAM request; write arbitration must happen before this interface. -/
structure RAMRequest (depth width : Nat) where
  address : Fin depth
  write : Option (BitVec width)

/-- Contents and registered read data both have arbitrary power-up values. -/
structure RAMState (depth width : Nat) where
  cells : Vector (BitVec width) depth
  readData : BitVec width

/-- Read-before-write synchronous memory. Simultaneous read/write returns the old value. -/
def ram (depth width : Nat) : PMachine (RAMState depth width) (RAMRequest depth width) (BitVec width) where
  out := (·.readData)
  next s i := ⟨match i.write with | none => s.cells | some v => s.cells.set i.address v,
    s.cells[i.address]⟩

theorem ram_read_before_write (s : RAMState d w) (i : RAMRequest d w) :
    (ram d w).out ((ram d w).next s i) = s.cells[i.address] := rfl

theorem ram_write (s : RAMState d w) (a : Fin d) (v : BitVec w) :
    ((ram d w).next s ⟨a, some v⟩).cells[a] = v := by simp [ram]

theorem ram_no_write (s : RAMState d w) (a : Fin d) :
    ((ram d w).next s ⟨a, none⟩).cells = s.cells := rfl

def RAMState.memBits (_ : RAMState d w) : Nat := d * w
end HDLean
