# Status

Current state of the implementation. The design and its milestones are in
[Design.md](Design.md); implementation choices in [Decisions.md](Decisions.md);
what is trusted in [Trust.md](Trust.md).

## Pipeline

One path to bits. A design is a node graph (`Dag`), either built directly with the
node-allocating `circuit do` (the Toy16 CPU) or translated from an expression-tree
circuit by the proved `Circuit.toDag`. `Dag.lower` (proved once) produces a gate
graph, and the printers (proved once by parse-after-print round trips) produce
SystemVerilog, AIGER and RTLIL. `Proved.emit_correct` gives the meaning of every
emitted file for every design; no per-design validator runs. The CLI reads each
emitted file back with the proved parser.

All proofs are checked by Lean's official kernel. There is no `sorry`, and every
audited theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

## Designs and their challenges

| Design | Challenge (frozen, readable) | Hardware path |
| --- | --- | --- |
| Counter | Decade behaviour after reset from any power-up state; 4 flip-flops | Tree circuit, `toDag` |
| Two-entry FIFO | Exact queue after reset, every payload width; `2w+2` flip-flops | Tree circuit, `toDag` |
| Three-stage pipeline | Three coupled queues after reset; budget | Tree circuit, `toDag` |
| General-depth FIFO | Refines `Fifo.spec (2^k)` after reset, every depth and width; budget | Tree circuit, `toDag` |
| RAM (register array) | Read port follows the read-before-write memory for some initial contents; budget | Tree circuit, `toDag` |
| Toy16 CPU | Retirement refines the ISA from any power-up state; 2-cycle progress; budget | Node graph |
| Dual-clock FIFO | Model level: queue trace after startup for every sampling oracle; enqueue and dequeue progress from reset | Legacy multi-clock circuit, emitted event-encoded |

`scripts/verify.py` audits 28 theorems: the 15 challenge theorems and 13 generic
framework theorems (emitter, lowering, tree translation, refinement rules).

## Checks

- `lake build` and `leanchecker --fresh Designs` (official kernel).
- Challenge audit: axioms, and statement constants from frozen modules or declared holes.
- `lake exe tests`: arbitrary-power-up simulation of every design against its
  reference (9,000 circular-FIFO, 9,600 RAM, 240 CPU, 2,400 pipeline, 8,400 FIFO and
  1,200 counter cycles), plus emitter read-back and mutation rejection.
- `scripts/check_backends.py`: AIGER interpretation, 100 Icarus cycles and Yosys
  RTLIL/SystemVerilog equivalence for every design; a corrupted next state must fail.
- `scripts/check_native_clocks.py`: native multi-domain SV/RTLIL for a two-domain
  fixture, including wrong-clock rejection.
- `Tests/test_workflow.py`: the audit rejects foreign axioms and agent-defined
  statement constants; a weakened agent theorem breaks the frozen challenge.

## Emitted sizes (width 8, depth 16)

| Design | Flip-flops | AND gates |
| --- | --- | --- |
| Counter | 4 | 594 |
| FIFO | 18 | 687 |
| Pipeline | 54 | 2,127 |
| RAM | 136 | 19,272 |
| General-depth FIFO | 144 | 92,625 |
| Toy16 CPU | 4,288 | 107,313 |

The proved lowering does no constant folding or sharing beyond what the node graph
states, and `toDag` does not recover sharing that tree circuits held only in memory.
Synthesis removes most of the redundancy; the ECP5 reports in `docs/reports/` were
measured with the previous, optimizing emitter and should be re-run.

## Known gaps

- Dual-clock FIFO hardware still uses the legacy multi-clock model (clock labels,
  deterministic sampling). Its challenge is model-level until it moves to
  `MultiClock.Shared.MultiDag` (milestone R2).
- Bit-level nodes only, no memory primitive, no module hierarchy: see the scaling
  milestones in the design.
- Exact emitted bytes are not kernel-checked; the proved-parser read-back replaces it.
