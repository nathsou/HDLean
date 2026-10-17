import Designs.Euler

/-!
# The UART reporter, end to end

The reporter is simulated (four clock cycles per bit) with an answer and a cycle
count; the serial line is decoded back into characters.
-/
namespace HDLean.Tests.Euler
open HDLean.Rtl HDLean.Euler

/-- Run the reporter for `n` cycles; the transmit line, cycle by cycle. -/
def txTrace (answer cycles n : Nat) : Array Nat := Id.run do
  let d := Report.design 4
  let mut st : Store := d.step default (#[0, answer, cycles], true)
  let mut out := #[]
  for _ in [:n] do
    let ins := #[1, answer, cycles]
    out := out.push ((d.output st ins).getD 0 1)
    st := d.step st (ins, false)
  return out

/-- Decode 8N1 frames, `bit` cycles per bit, sampling mid-bit. -/
def decode (line : Array Nat) (bit : Nat) : String := Id.run do
  let mut i := 0
  let mut s := ""
  while i + 10 * bit < line.size do
    if line[i]! == 0 then
      let mut c := 0
      for b in [0:8] do
        c := c + line[i + (b + 1) * bit + bit / 2]! * 2 ^ b
      s := s.push (Char.ofNat c)
      i := i + 10 * bit
    else
      i := i + 1
  return s

#guard (decode (txTrace 8739992577 1000 3000) 4).startsWith "8739992577 1000\r\n"
#guard (decode (txTrace 0 7 3000) 4).startsWith "0 7\r\n"

/-! ## Rejected solvers are explained

A small solver with one deliberate mistake each: the builder names the failing
operation, the widths involved and the enclosing scopes. -/

section Rejections
open HDLean.Rtl.Build

hdl_record Toy where
  a : 8 := 0
  b : 4

def toyCtx : Ctx := solverCtx "toy" 8 Toy Toy.resets #[ms "m" 4 8]

def rejection (p : M toyCtx Wiring) : String :=
  match runE toyCtx p with
  | .ok _ => "accepted"
  | .error e => e.render

def toyWrites (r : Toy Sig) : M toyCtx (Array (Array WritePort)) := do
  writePorts [("m", #[port (← lit 1 0) r.b r.a])]

-- a narrowing zero extension, inside a scope
#guard rejection (solver "toy" Toy fun r => do
    let x ← scope "low half" (zx r.a 4)
    finish (← bit x 0) r.a { r with b := x } (← toyWrites r)) ==
  "toy > low half: zero extension from 8 to 4 bits (narrower: use a slice) (after 3 cells)"
-- a slice past the top, located by `here%`
#guard (rejection (solver "toy" Toy fun r => do
    let x ← scope here% (slice r.a 6 4)
    finish (← bit x 0) r.a { r with b := x } (← toyWrites r))).startsWith "toy > Tests/Euler.lean:"
#guard (rejection (solver "toy" Toy fun r => do
    let x ← scope here% (slice r.a 6 4)
    finish (← bit x 0) r.a { r with b := x } (← toyWrites r))).endsWith
  ": slice: bits 6 … 9 of an 8-bit value (after 3 cells)"
-- memories by name
#guard rejection (solver "toy" Toy fun r => do
    let x ← readMem "mem" 8 r.b
    finish (← bit x 0) x r (← toyWrites r)) ==
  "toy: no memory named mem (after 3 cells)"
#guard rejection (solver "toy" Toy fun r => do
    let x ← readMem "m" 8 r.a
    finish (← bit x 0) x r (← toyWrites r)) ==
  "toy > memory m: memory 0 (4-bit address, 8-bit words): read as 8 bits at an 8-bit address (after 3 cells)"
-- wiring
#guard rejection (solver "toy" Toy fun r => do finish (← bit r.a 0) r.a r) ==
  "write ports for 0 memories, 1 declared (m) (after 4 cells)"
#guard rejection (solver "toy" Toy fun r => do finish (← bit r.a 0) (← zx r.a 16) r (← toyWrites r)) ==
  "output answer (8 bits) is wired to a 16-bit value (after 6 cells)"
#guard rejection (solver "toy" Toy fun r => do finish (← bit r.a 0) r.a r (← toyWrites r)) == "accepted"

end Rejections

end HDLean.Tests.Euler
