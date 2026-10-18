# HDLean

HDLean is a Lean 4 embedded hardware language with executable semantics,
kernel-checked refinement proofs, and SystemVerilog, AIGER and Yosys RTLIL output.

Designs are written in a word-level RTL: typed records of words, memories, module
instances, arithmetic and comparison operators, and several clock domains joined
by two-flop synchronizers and shared memories ([design](docs/Design.md) 3.1). The
word level prints as SystemVerilog and RTLIL with proved round trips, and reaches
AIGER, RTLIL and bit-level SystemVerilog through a proved bit-blaster.

The examples are a decade counter, a two-entry FIFO, a general-depth FIFO on a
memory, a three-stage elastic pipeline, a single-port RAM, the Toy16 CPU and a
dual-clock FIFO. [Review.md](docs/Review.md) lists every proved guarantee;
[coverage and limitations](docs/Status.md) state exactly what is proved.

## Build and run

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake build
lake exe tests
lake exe hdlean --help
lake exe hdlean emit fifo sv build/fifo.sv 8          # bit-blasted by the proved Design.toDag
lake exe hdlean emit fifo aiger build/fifo.aag 8
lake exe hdlean emit ring rtlil build/ring.il 8
lake exe hdlean rtl-emit toy16 build/toy16.sv          # word-level SystemVerilog, read back
lake exe hdlean rtl-emit async build/async.il 8        # dual-clock FIFO, word-level RTLIL
lake exe hdlean rtl-trace ram build/ram.json 8 100 1
lake exe hdlean rtl-metrics toy16
lake exe hdlean metrics pipeline 8
lake exe hdlean check fifo 8 200 42
lake exe hdlean abc-emit toy16 aiger build/toy16_abc.aag  # ABC-optimised, LRAT-validated
lake exe hdlean toy16 48
lake env .lake/build/bin/hdlean review docs/Review.md     # reviewer document
```

The toolchain is pinned to **Lean 4.35.0**; all proofs are checked by its official
kernel. No Mathlib or third-party Lean packages are required. The width argument
is the payload width of `fifo`, `pipeline`, `ring`, `ram` and `async` (default 8);
`ring` and `async` hold 16 words, `ram` has 16 addresses.

The example Toy16 program starts with garbage register and memory contents, sums
5+4+3+2+1, stores 15 at address zero, and halts on the 23rd retirement.

## Project Euler on a board

[Euler.md](docs/Euler.md) describes ten Project Euler solvers written in HDLean
for the Alchitry Cu (iCE40-HX8K): sieves, Collatz lanes with memoised tails,
Miller–Rabin in Montgomery form, systolic and streamed dynamic programmes, BCD
bignums. Each is checked against a plain-Lean reference, placed and routed with
timing closed, and reports its answer and cycle count over the board's serial
port (`scripts/euler.py`).

## A design is a Lean program

```lean
hdl_record Regs where
  count : 4

def ctx : Ctx := Ctx.mealy "counter" In Out Regs ⟨.sync 0⟩ #[]

def body (i : In Sig) (r : Regs Sig) : M ctx (Step Out Regs) := do
  let nine ← const 4 9
  let one ← const 4 1
  let zero ← const 4 0
  let atNine ← eq r.count nine
  let inc ← add r.count one
  let wrapped ← mux atNine zero inc
  let nxt ← mux i.en wrapped r.count
  pure { out := ⟨r.count⟩, next := ⟨nxt⟩ }

def design : Design := ⟨#[ctx.module (mealy In Out Regs body)]⟩
```

This is the whole decade counter ([Designs/Counter/Word.lean](Designs/Counter/Word.lean)).
Each `let` emits one cell, checked for widths and references as it is built, so
the module the kernel reasons about is exactly the one emitted. The proof walks
the same program with one lemma per operator (`rtl_let`), giving the next
registers and the outputs as functions of the decoded records; the challenge is
then a simulation proof against the reviewed `Counter.spec`. Ports and registers
are records (`hdl_record`); registers declare their reset; memories have no
reset; power-up contents are always arbitrary.

## What to review

- [Review.md](docs/Review.md): every challenge statement, its axioms, the definitions it
  uses, interfaces and scenarios, generated from the checked environment.
- Each design directory holds its frozen `Spec.lean` (where it has its own
  reference), `Interface.lean` (ports and how the reference reads them) and
  `Challenge.lean` (the theorems): [Counter](Designs/Counter), [Fifo](Designs/Fifo)
  (also the ports of the general-depth FIFO), [CircularFifo](Designs/CircularFifo),
  [SkidBuffer](Designs/SkidBuffer) (the pipeline), [RAM](Designs/RAM),
  [Toy16](Designs/Toy16) and [AsyncFifo](Designs/AsyncFifo).
- The implementation holes in [verification/frozen.json](verification/frozen.json).

The FIFO spec fixes every ready/valid cycle and masks invalid data with `Option`.
A full FIFO rejects enqueue even when it dequeues in the same cycle. Payload
registers and memories are unreset; the proofs quantify over every power-up store.
Budgets bound state bits (`Blast.stateBits`, registers plus memory words).

Reference models use lists and natural numbers; they are distinct from the
designs that are emitted. The manifest freezes the framework, review interfaces,
specifications, challenges and checker sources. Its initial status is
**review-required**: generating a manifest is not human approval.

## Verification

```sh
# Clean build (official kernel), fresh kernel replay, challenge audit, simulation
# suite, and emission of every design in every format with proved read-back.
python3 scripts/verify.py

# Also cross-check with Icarus Verilog and Yosys (must be on PATH).
python3 scripts/verify.py --backends

# Check against the reviewer-approved manifest digest, as CI does.
python3 scripts/verify.py --manifest-sha256 <reviewed-digest> --backends
```

The report is `build/signoff.json`: audited theorems with their axioms, artifact
hashes, structural metrics, toolchain and commit. Each design's guarantees are the
theorems in its frozen `Challenge.lean`; [Trust.md](docs/Trust.md) explains what the
audit enforces and what remains trusted.

Word-level text is printed and parsed back with proved round trips
(`Design.parse_systemVerilog`, `Design.parse_rtlil`, and the same for multi-clock
designs). Bit-level text comes from one proved path: the bit-blaster
(`Design.toDag_nextState`, `toDag_evalOutput`), the proved lowering, and printers
whose parse-after-print round trips are proved (`Proved.emit_correct`). The CLI
decodes every file it writes with the proved parser.

## Pins, waveforms, and metrics

```sh
lake exe hdlean trace fifo build/trace.json 8 60 42
python3 scripts/waveform.py build/trace.json --format table
python3 scripts/waveform.py build/trace.json --format vcd --output build/trace.vcd

# Reviewer/maintainer operation: creates a candidate, never an approval.
python3 scripts/freeze.py --write

# Requires a real Liberty library, Yosys and ABC; no built-in PDK is claimed.
python3 scripts/synthesize.py fifo --width 8 --liberty /path/to/cells.lib
```

Trace rows contain inputs, old state, pre-edge outputs and next state of the
bit-blasted netlist. Inputs and words are LSB first. The final input bit is
synchronous reset; SystemVerilog and RTLIL also have a `clk` port. No
initialization is inserted into generated designs.

Graph metrics count the emitted AND gates, flip-flops and Boolean depth, including
reset logic. They are not physical timing or area predictions. For FPGA placement
and routing, use the [pinned physical flow](docs/Physical.md). No board timing or
power measurement is claimed.

## Repository

`HDLean/Semantics` has machines, reset, clock-crossing primitives (sampling, Gray
code), composition and retirement; `HDLean/Lib` has the RAM model and Moore
networks. `HDLean/Rtl` is the word-level language: syntax and semantics, the
builder and its Hoare-style lemmas, records, memories, instances, multi-clock
designs, the word-level passes, the text printers and parsers, and the
bit-blaster. `HDLean/Core/Dag.lean` is the bit-level node graph,
`HDLean/Netlist` its proved lowering and AIG pass, `HDLean/Backend` the gate graph
and the proved bit-level printers and parsers. `Designs` contains specs,
interfaces, challenges, implementations and proofs. `Tests` contains the audit,
behavioral regressions and rejection tests.

The [design document](docs/Design.md), [decision log](docs/Decisions.md) and
[current status](docs/Status.md) distinguish the original goals from what is
implemented. MIT licensed.
