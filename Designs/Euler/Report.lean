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

def regs : Array RegSpec := #[
  rs "state" 3 (.sync sWait), rs "which" 1 (.sync 0), rs "val" 64, rs "bcd" 80, rs "steps" 7,
  rs "ptr" 5, rs "started" 1, rs "crlf" 2, rs "sr" 10 (.sync 1023), rs "bits" 4, rs "baud" 16,
  rs "busy" 1 (.sync 0), rs "gap" 26, rs "led" 8 (.sync 0)]

def ctx : Ctx :=
  { name := Ident.ofString "report",
    inputs := #[⟨Ident.ofString "done", 1⟩, ⟨Ident.ofString "answer", 64⟩, ⟨Ident.ofString "cycles", 64⟩],
    outputs := #[⟨Ident.ofString "tx", 1⟩, ⟨Ident.ofString "led", 8⟩], regs }

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
def body (divisor : Nat) : M ctx Wiring := do
  let doneIn ← input 0 1
  let answerIn ← input 1 64
  let cycles ← input 2 64
  let st ← rd 0 3
  let which ← rd 1 1
  let val ← rd 2 64
  let bcd ← rd 3 80
  let steps ← rd 4 7
  let ptr ← rd 5 5
  let started ← rd 6 1
  let crlf ← rd 7 2
  let sr ← rd 8 10
  let bits ← rd 9 4
  let baud ← rd 10 16
  let busy ← rd 11 1
  let gap ← rd 12 26
  let led ← rd 13 8
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
  pure ⟨#[tx.ref, led.ref], #[st'.ref, which'.ref, val'.ref, bcd'.ref, steps'.ref, ptr'.ref, started'.ref,
    crlf'.ref, sr'.ref, bits'.ref, baud'.ref, busy'.ref, gap'.ref, led'.ref], #[]⟩

def design (divisor : Nat) : Design := ⟨#[ctx.module (body divisor)]⟩

/-! ## Counting cycles on the solver's clock -/

/-- Four 16-bit chunks. Chunk 0 counts every cycle; the wrap of chunk 0 is
predicted a cycle ahead (`w0`), and the "all ones" flags of chunks 1 and 2 are
registered (they are stable whenever `w0` is set, 65536 cycles apart), so every
path is one LUT and one 16-bit carry chain. -/
def countRegs : Array RegSpec := #[rs "c0" 16 (.sync 0), rs "c1" 16 (.sync 0), rs "c2" 16 (.sync 0),
  rs "c3" 16 (.sync 0), rs "w0" 1 (.sync 0), rs "a1" 1 (.sync 0), rs "a2" 1 (.sync 0)]

def countCtx : Ctx :=
  { name := Ident.ofString "cyclecount", inputs := #[⟨Ident.ofString "done", 1⟩],
    outputs := #[⟨Ident.ofString "cycles", 64⟩], regs := countRegs }

def countBody : M countCtx Wiring := do
  let done ← input 0 1
  let c0 ← rd 0 16
  let c1 ← rd 1 16
  let c2 ← rd 2 16
  let c3 ← rd 3 16
  let w0 ← rd 4 1
  let a1 ← rd 5 1
  let a2 ← rd 6 1
  let run ← not1 done
  let c0' ← ite' run (← addK c0 1) c0
  let w0' ← and1 run (← eqK c0 0xFFFE)
  let inc2 ← and1 w0 a1
  let inc3 ← and1 inc2 a2
  let c1' ← ite' w0 (← addK c1 1) c1
  let c2' ← ite' inc2 (← addK c2 1) c2
  let c3' ← ite' inc3 (← addK c3 1) c3
  let a1' ← eqK c1 0xFFFF
  let a2' ← eqK c2 0xFFFF
  let cycles ← concat (← concat c3 c2) (← concat c1 c0)
  pure ⟨#[cycles.ref], #[c0'.ref, c1'.ref, c2'.ref, c3'.ref, w0'.ref, a1'.ref, a2'.ref], #[]⟩

def countDesign : Design := ⟨#[countCtx.module countBody]⟩

end HDLean.Euler.Report
