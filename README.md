# HDLean

HDLean is a Lean 4 embedded hardware language with executable circuit semantics,
kernel-checked refinement proofs, and SystemVerilog, AIGER, and Yosys RTLIL output.

**Status: an experimental v0.1 implementation, not the completed v1 design.**
The two-entry FIFO and decade counter are proved against reference models on their
actual circuit ASTs. The Toy16 transition-system core has a reset, retirement, and
bounded-progress proof. Generic graph sharing/printer verification, synthesizable
Toy16 and asynchronous FIFO implementations, and L2/L3 sign-off remain unfinished.
See [the coverage table](docs/Status.md) before relying on a guarantee.

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
```

The toolchain is pinned to **Lean 4.34.0**. No Mathlib or third-party Lean packages
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

def enabledToggle : Circuit 0 1 1 1 := circuit do
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
with explicit expression builders; automatic reification of Lean `if` and `+` is
not implemented.

`Circuit.step` exposes Mealy outputs explicitly. `Circuit.denote` requires an
`IsMoore` proof, so input-dependent outputs cannot silently become Moore outputs.
All transitions sample old register values. There are no HDL initial blocks;
power-up contents are supplied by the environment.

`Synth` has checked encodings for Booleans, bit vectors, products, nonempty `Fin`,
and vectors. `Synth.transport` builds structure/enum layouts from a proved
representation map. There is no automatic `deriving Synth` yet. The conservative
`Fin (n+1)` encoding uses `n+1` bits; it is not a compact binary layout.

## What to review

- [FIFO specification](Designs/Fifo/Spec.lean), [interface](Designs/Fifo/Interface.lean),
  and [challenge](Designs/Fifo/Challenge.lean).
- [Counter specification](Designs/Counter/Spec.lean), [interface](Designs/Counter/Interface.lean),
  and [challenge](Designs/Counter/Challenge.lean).
- [Toy16 ISA](Designs/Toy16/Spec.lean) and [challenge](Designs/Toy16/Challenge.lean).

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
# Builds, runs regressions, replays proofs in a fresh kernel, audits axioms,
# emits artifacts and records their hashes and structural metrics.
python3 scripts/verify.py

# Also requires Icarus Verilog and Yosys on PATH.
python3 scripts/verify.py --backends
python3 Tests/test_workflow.py

# Independent trust anchor supplied by a reviewer/CI, rather than the submission.
python3 scripts/verify.py --manifest-sha256 <reviewed-digest> --backends
```

The report is `build/signoff.json`. A successful run is labeled
`L1 / development-checks-passed`, not tape-out sign-off. It includes per-theorem
axioms, source and artifact hashes, toolchain identity, dirty-tree status,
structural metrics, physical assumptions, and unimplemented checks. L2/L3 requests
fail with an explicit error. `leanchecker --fresh` replays declarations using
Lean's own kernel; it is not the independent nanoda checker.

The core suite checks 9,600 AST/shared-graph cycles, 8,400 FIFO-reference cycles,
1,200 counter-reference cycles, 7,500 circular-buffer cycles, and 15,000 async
oracle steps. The external suite checks AIGER evaluation, 500 Icarus cycles, and
Yosys RTLIL/SystemVerilog equivalence across five instances. These tests do not
turn unproved generic compiler passes into theorems.

`Tests/Certificates.lean` additionally proves shared-graph equivalence for the
counter and width-one FIFO by kernel reduction, without native-evaluation axioms.
The generic typed-AST-to-AND/inverter-tree lowering is proved for every expression,
state transition, and output. Generic sharing and textual printer proofs remain
open; see [Trust.md](docs/Trust.md).

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

Graph metrics count actual shared AND gates, flip-flops, and Boolean depth,
including reset logic. They are not physical timing or area predictions. The
optional synthesis script records the Liberty hash and actual tool statistics.
It does not claim placed/routed timing or power.

## Repository

`HDLean/Semantics` contains machines, reset, clocks, composition, and retirement.
`HDLean/Core` contains the finite AST and word builders. `HDLean/Lib` contains
memory, stream contracts, causal latency contracts, and Moore networks.
`HDLean/Netlist` contains the semantic IR, proved lowering, and proved rewrites.
`HDLean/Backend` contains shared graph construction and the three printers.
`Designs` contains reference specs, implementations/models and proofs. `Tests`
contains kernel certificates, behavioral regressions, and rejection tests.

The [renamed design proposal](docs/Design.md), [decision log](docs/Decisions.md),
and [current status](docs/Status.md) distinguish the original goals from what is
implemented. MIT licensed.
