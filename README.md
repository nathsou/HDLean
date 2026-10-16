# HDLean

HDLean is a Lean 4 embedded hardware language with executable circuit semantics,
kernel-checked refinement proofs, and SystemVerilog, AIGER, and Yosys RTLIL output.

The library includes physical counter, FIFO, circular FIFO, elastic pipeline,
register-array RAM, Toy16 CPU and dual-clock FIFO implementations. Generic proofs
cover reset, queue ordering, retirement, progress, lowering and parsed backend
semantics. [Coverage and limitations](docs/Status.md) state the exact guarantees.

## Build and run

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake build
lake exe tests
lake exe hdlean --help
lake exe hdlean emit fifo sv build/fifo.sv 8
lake exe hdlean emit fifo aiger build/fifo.aag 8
lake exe hdlean emit fifo rtlil build/fifo.il 8
lake exe hdlean metrics fifo 8
lake exe hdlean check fifo 8 200 42
lake exe hdlean toy16 48
lake exe hdlean emit ring rtlil build/ring.il 8
lake exe hdlean emit ram sv build/ram.sv 8
lake exe hdlean emit toy16 sv build/toy16.sv
lake exe hdlean emit-async rtlil build/async.il 8 4
```

The toolchain is pinned to **Lean 4.35.0**; all proofs are checked by its official
kernel. No Mathlib or third-party Lean packages
are required. `fifo` currently means the proved two-entry skid buffer; its width
argument is the payload width, not queue depth. `counter` is a four-bit decade
counter; it ignores the width argument. Widths 0–64 are accepted for the FIFO.

The example Toy16 program starts with garbage register/memory contents, sums
5+4+3+2+1, stores 15 at address zero, and halts on the 23rd retirement (cycle 45 of
the serialized two-stage core).

## A circuit is data

```lean
import HDLean
open HDLean

def enabledToggle : Circuit 0 1 1 1 := treeCircuit do
  let q : Expr 0 1 1 := .reg 0
  return {
    name := "enabled_toggle"
    state := #v[⟨"q", .synchronous false, .mux (.input 0) (.inv q) q, "example"⟩]
    output := #v[q] }
```

`Circuit domain inputs registers outputs` fixes all dimensions. Expressions cannot
read an out-of-range wire or cross a clock domain. Each register has one next-state
expression and an explicit reset kind. Width-indexed `WordExpr` provides literal,
input, register, mux, Boolean, equality and ripple-add builders. Arithmetic does
not implicitly extend or narrow. The surface syntax is ordinary Lean do-notation
and reifies conditionals, equality, Boolean logic and typed word arithmetic.

`Circuit.step` exposes Mealy outputs explicitly. `Circuit.denote` requires an
`IsMoore` proof, so input-dependent outputs cannot silently become Moore outputs.
All transitions sample old register values. There are no HDL initial blocks;
power-up contents are supplied by the environment.

`Synth` has checked encodings for Booleans, bit vectors, products, nonempty `Fin`,
and vectors. `Synth.transport` builds structure/enum layouts from a proved
representation map. `deriving Synth` handles structures and nullary enums,
including generic structure parameters. Finite indices use compact binary layouts.
Tagged unions with payloads use explicit layouts.

## What to review

- [FIFO specification](Designs/Fifo/Spec.lean), [interface](Designs/Fifo/Interface.lean),
  and [challenge](Designs/Fifo/Challenge.lean).
- [Counter specification](Designs/Counter/Spec.lean), [interface](Designs/Counter/Interface.lean),
  and [challenge](Designs/Counter/Challenge.lean).
- [Toy16 ISA](Designs/Toy16/Spec.lean), [interface](Designs/Toy16/Interface.lean)
  and [challenge](Designs/Toy16/Challenge.lean).
- General-depth FIFO [interface](Designs/CircularFifo/Interface.lean) and
  [challenge](Designs/CircularFifo/Challenge.lean); [RAM challenge](Designs/RAM/Challenge.lean).
- Dual-clock FIFO [model](Designs/AsyncFifo/Model.lean), [queue spec](Designs/AsyncFifo/Spec.lean),
  [interface](Designs/AsyncFifo/Interface.lean) and [challenge](Designs/AsyncFifo/Challenge.lean).
- The implementation holes in [verification/frozen.json](verification/frozen.json).

The FIFO spec fixes every ready/valid cycle and masks invalid data with `Option`.
A full FIFO rejects enqueue even when it dequeues in the same cycle. Capacity two
supports full rate with an always-ready consumer. Payload registers are unreset;
the proof quantifies over every initial bit pattern. The physical budget is
`2 * width + 2` flip-flops for this shift-register implementation.

Reference models use lists and natural numbers. They are distinct from the finite
AST that is lowered. The development manifest freezes the framework, review
interfaces, specifications, challenges, and checker sources. Its initial status
is **review-required**: generating a manifest is not human approval.

## Verification

```sh
# Clean build (official kernel), fresh kernel replay, challenge audit, simulation
# suite, and emission of every design in every format with proved read-back.
python3 scripts/verify.py

# Also cross-check with Icarus Verilog and Yosys (must be on PATH).
python3 scripts/verify.py --backends
python3 Tests/test_workflow.py

# Check against the reviewer-approved manifest digest, as CI does.
python3 scripts/verify.py --manifest-sha256 <reviewed-digest> --backends
```

The report is `build/signoff.json`: audited theorems with their axioms, artifact
hashes, structural metrics, toolchain and commit. Each design's guarantees are the
theorems in its frozen `Challenge.lean`; [Trust.md](docs/Trust.md) explains what the
audit enforces and what remains trusted.

Every design is emitted by one proved path: a node graph (`Dag`), the proved
lowering, and printers whose parse-after-print round trips are proved, giving
`Proved.emit_correct` for every design. Expression-tree circuits reach it through
the proved `Circuit.toDag`. The CLI decodes every file it writes with the proved
parser and requires the lowered graph back.

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

Trace rows contain inputs, old state, pre-edge outputs and next state. Testbench
initialization is used only to compare the same arbitrary power-up assignment;
no initialization is inserted into generated designs. Inputs and payload words
are LSB first. The final input bit is synchronous reset; SystemVerilog/RTLIL also
have a `clk` port. Numeric wire names remain stable; original names and source
paths remain in the internal graph.

Graph metrics count the emitted AND gates, flip-flops and Boolean depth, including
reset logic; the proved lowering does not optimize, so synthesis tools will shrink them. They are not physical timing or area predictions. The
optional synthesis script records the Liberty hash and actual tool statistics.
For actual FPGA placement and routing, use the [pinned physical flow](docs/Physical.md).
The complete Toy16 CPU met a 12 MHz target on ECP5-25K with a measured tool-model
Fmax of 47.0 MHz, using the previous emitter; re-run the flow for the current one.
No board timing or power measurement is claimed.

## Repository

`HDLean/Semantics` contains machines, reset, clocks, composition, and retirement.
`HDLean/Core` contains the expression-tree circuits, the node graph `Dag`, its
builder and allocator, and the proved `Circuit.toDag`. `HDLean/Lib` contains
memory, stream contracts, causal latency contracts, finite delay/retiming proofs,
and Moore networks. `HDLean/MultiClock` has multi-domain node graphs with typed
synchronizers and native SV/RTLIL emission, plus the legacy model still used by the
dual-clock FIFO. `HDLean/Netlist/DagLower.lean` is the proved lowering;
`HDLean/Backend` has the gate graph and the proved printers and parsers. `Designs`
contains specs, interfaces, challenges, implementations and proofs. `Tests`
contains the audit, behavioral regressions and rejection tests.

The [renamed design proposal](docs/Design.md), [decision log](docs/Decisions.md),
and [current status](docs/Status.md) distinguish the original goals from what is
implemented. MIT licensed.

The shared allocator supports resettable and arbitrary-power-up storage without
manual register offsets:

```lean
open HDLean.Dag.Allocate

def toggle : Option (HDLean.Dag 0 1 1 1) := circuit "toggle" do
  let enable ← input 0
  let count ← regR
  let next ← xor count.value enable
  drive count next
  pure #v[count.value]
```

Each binding allocates the explicitly requested nodes or register handles.
Finalization rejects missing or duplicate drivers and invalid node references.
The older expression-tree syntax is named `treeCircuit do`.
