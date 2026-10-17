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

end HDLean.Tests.Euler
