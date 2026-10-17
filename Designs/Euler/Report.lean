import Designs.Euler.Kit

/-!
# Reporting an answer over the board's UART

Two small modules around a solver. `CycleCount` runs on the solver's clock and
counts cycles from reset release until `done` (four 16-bit chunks, each carry
registered a cycle ahead, so it never limits the clock). The reporter runs on a slow clock of its own: once it sees `done`, it
converts the answer and then the cycle count (both held by then) to decimal,
one after the other in one BCD register (serial double dabble, 64 steps), and
sends `<answer> <cycles>\r\n` over the UART, again and again with a pause
between messages, so a terminal opened late still sees it. Leading zeros are
not sent. The eight LEDs show the low byte of the answer.
-/
namespace HDLean.Euler.Report
open HDLean.Rtl HDLean.Rtl.Build

def sWait := 0
def sLoad := 1
def sConv := 2
def sSend := 3
def sGap := 4

/-- Characters per number: twenty digits (leading zeros not sent) and a separator. -/
def digits : Nat := 20

hdl_record RepIn where
  done : 1
  answer : 64
  cycles : 64

hdl_record RepOut where
  tx : 1
  led : 8

hdl_record RepRegs where
  state : 3 := sWait
  which : 1 := 0
  val : 64
  bcd : 80
  steps : 7
  ptr : 5
  started : 1
  crlf : 2
  sr : 10 := 1023
  bits : 4
  baud : 16
  busy : 1 := 0
  gap : 26
  led : 8 := 0

def ctx : Ctx := Ctx.mealy "report" RepIn RepOut RepRegs RepRegs.resets

/-- Double dabble adjustment: add 3 to every BCD digit that is at least 5. -/
def adjust (x : Sig 80) : M ctx (Sig 80) := do
  let mut acc ← lit 80 0
  for i in [0:20] do
    let n ← slice x (4 * i) 4
    let n' ← ite' (← geK n 5) (← addK n 3) n
    acc ← or acc (← shlK (← zx n' 80) (4 * i))
  pure acc

/-- The answer and the cycle count (both held once `done` is seen) are converted
one after the other, each read straight from the inputs, and sent from the BCD
register itself. -/
def body (divisor : Nat) : M ctx Wiring := mealy RepIn RepOut RepRegs fun i r => do
  let doneIn := i.done
  let answerIn := i.answer
  let cycles := i.cycles
  let st := r.state
  let which := r.which
  let val := r.val
  let bcd := r.bcd
  let steps := r.steps
  let ptr := r.ptr
  let started := r.started
  let crlf := r.crlf
  let sr := r.sr
  let bits := r.bits
  let baud := r.baud
  let busy := r.busy
  let gap := r.gap
  let led := r.led
  let isWait ← eqK st sWait
  let isLoad ← eqK st sLoad
  let isConv ← eqK st sConv
  let isSend ← eqK st sSend
  let isGap ← eqK st sGap
  let latch ← and1 isWait doneIn
  -- conversion: 64 double-dabble steps
  let convLast ← eqK steps 63
  let bcd1 ← or (← shlK (← adjust bcd) 1) (← zx (← bit val 63) 80)
  -- sending: 20 digits from the top of the BCD register, then a space (after the
  -- answer) or CR LF (after the cycle count)
  let inDigits ← ltK ptr digits
  let dig ← slice bcd 76 4
  let lastDigit ← eqK ptr (digits - 1)
  let vis ← or1 started (← or1 (← neK dig 0) lastDigit)
  let isSecond ← eqK crlf 1
  let sepChar ← ite' which (← ite' isSecond (← lit 8 10) (← lit 8 13)) (← lit 8 32)
  let ch ← ite' inDigits (← add (← zx dig 8) (← lit 8 48)) sepChar
  let visible ← ite' inDigits vis (← lit 1 1)
  let idle ← not1 busy
  let take ← and1 isSend idle
  let load ← and1 take visible
  let frame ← or (← shlK (← zx ch 10) 1) (← lit 10 512)
  -- the end of a number: after its separator(s)
  let sepDone ← ite' which isSecond (← lit 1 1)
  let numberEnd ← and1 take (← and1 (← not1 inDigits) sepDone)
  -- UART
  let baud0 ← eqK baud 0
  let tick ← and1 busy baud0
  let srShift ← or (← shrK sr 1) (← lit 10 512)
  let bits1 ← eqK bits 1
  let sr' ← ite' load frame (← ite' tick srShift sr)
  let bits' ← ite' load (← lit 4 10) (← ite' tick (← subK bits 1) bits)
  let baud' ← ite' load (← lit 16 (divisor - 1)) (← ite' tick (← lit 16 (divisor - 1)) (← ite' busy (← subK baud 1) baud))
  let busy' ← ite' load (← lit 1 1) (← ite' (← and1 tick bits1) (← lit 1 0) busy)
  -- pointer, digit shifting, separators
  let takeDigit ← and1 take inDigits
  let ptr' ← ite' isLoad (← lit 5 0) (← ite' takeDigit (← addK ptr 1) ptr)
  let started' ← ite' isLoad (← lit 1 0) (← ite' takeDigit (← or1 started vis) started)
  let crlf' ← ite' isLoad (← lit 2 0) (← ite' (← and1 take (← not1 inDigits)) (← addK crlf 1) crlf)
  -- pause after each full message
  let gapDone ← eqK gap 0
  let toGap ← and1 numberEnd which
  let gap' ← ite' toGap (← lit 26 ((1 <<< 26) - 1)) (← ite' isGap (← subK gap 1) gap)
  -- state
  let nextNumber ← and1 numberEnd (← not1 which)
  let st' ← ite' latch (← lit 3 sLoad)
    (← ite' isLoad (← lit 3 sConv)
    (← ite' (← and1 isConv convLast) (← lit 3 sSend)
    (← ite' nextNumber (← lit 3 sLoad)
    (← ite' toGap (← lit 3 sGap)
    (← ite' (← and1 isGap gapDone) (← lit 3 sLoad) st)))))
  let which' ← ite' latch (← lit 1 0) (← ite' nextNumber (← lit 1 1) (← ite' toGap (← lit 1 0) which))
  let val' ← ite' isLoad (← ite' which cycles answerIn) (← ite' isConv (← shlK val 1) val)
  let bcd' ← ite' isLoad (← lit 80 0) (← ite' isConv bcd1 (← ite' takeDigit (← shlK bcd 4) bcd))
  let steps' ← ite' isLoad (← lit 7 0) (← ite' isConv (← addK steps 1) steps)
  let led' ← ite' latch (← slice answerIn 0 8) led
  let tx ← bit sr 0
  pure { out := ⟨tx, led⟩,
         next := { state := st', which := which', val := val', bcd := bcd', steps := steps', ptr := ptr',
                   started := started', crlf := crlf', sr := sr', bits := bits', baud := baud', busy := busy',
                   gap := gap', led := led' } }

def design (divisor : Nat) : Design := ⟨#[ctx.module (body divisor)]⟩

/-! ## Counting cycles on the solver's clock -/

/-- Four 16-bit chunks. Chunk 0 counts every cycle; the wrap of chunk 0 is
predicted a cycle ahead (`w0`), and the "all ones" flags of chunks 1 and 2 are
registered (they are stable whenever `w0` is set, 65536 cycles apart), so every
path is one LUT and one 16-bit carry chain. -/
hdl_record CountIn where
  done : 1

hdl_record CountOut where
  cycles : 64

hdl_record CountRegs where
  c0 : 16 := 0
  c1 : 16 := 0
  c2 : 16 := 0
  c3 : 16 := 0
  w0 : 1 := 0
  a1 : 1 := 0
  a2 : 1 := 0

def countCtx : Ctx := Ctx.mealy "cyclecount" CountIn CountOut CountRegs CountRegs.resets

def countBody : M countCtx Wiring := mealy CountIn CountOut CountRegs fun i r => do
  let run ← not1 i.done
  let c0' ← ite' run (← addK r.c0 1) r.c0
  let w0' ← and1 run (← eqK r.c0 0xFFFE)
  let inc2 ← and1 r.w0 r.a1
  let inc3 ← and1 inc2 r.a2
  let c1' ← ite' r.w0 (← addK r.c1 1) r.c1
  let c2' ← ite' inc2 (← addK r.c2 1) r.c2
  let c3' ← ite' inc3 (← addK r.c3 1) r.c3
  let a1' ← eqK r.c1 0xFFFF
  let a2' ← eqK r.c2 0xFFFF
  let cycles ← concat (← concat r.c3 r.c2) (← concat r.c1 r.c0)
  pure { out := ⟨cycles⟩, next := { c0 := c0', c1 := c1', c2 := c2', c3 := c3', w0 := w0', a1 := a1', a2 := a2' } }

def countDesign : Design := ⟨#[countCtx.module countBody]⟩

end HDLean.Euler.Report
