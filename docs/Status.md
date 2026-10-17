# Status

Current state of the implementation. The design and its milestones are in
[Design.md](Design.md); implementation choices in [Decisions.md](Decisions.md);
what is trusted in [Trust.md](Trust.md).

## Pipeline

Two entry points, one path to bits. New designs are written in the word-level RTL
(`HDLean/Rtl`, [Design.md](Design.md) 3.1): typed records, a checked builder,
memories and module instances. They print directly as word-level SystemVerilog
(proved round trip) and reach the bit-level backends through the proved
bit-blaster `Design.toDag` (`toDag_nextState`, `toDag_evalOutput`). The bit-level
path below is unchanged; since v0.4 it lowers with `Dag.lowerTight` (negation free,
one gate per AND), and since v0.5 every backend emits `Dag.lowerOpt`: the lowering
followed by the proved AIG optimisation `Graph.optimize`, which `emit_correct`
covers. Word-level designs pass through the proved word-level rewriting
`Design.optimize` first. `hdlean abc-emit` adds ABC's optimisation, accepted only
with an LRAT certificate checked by Lean's verified checker
([Design.md](Design.md) 13.5).

Bit-level path. A design is a node graph (`Dag`), either built directly with the
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
| Toy16 CPU, word level | Retirement refines the ISA after one reset cycle from any power-up store; 2-cycle progress | Word RTL: register file and data memory as RTL memories, ALU as an instantiated module, 13-field register record |
| RAM, word level | Read port follows the read-before-write RAM for some initial state, any inputs and resets | Word RTL: one RTL memory, one write port |

`scripts/verify.py` audits 53 theorems: the 17 challenge theorems, the two word-level
challenges re-proved for the optimised designs, and 34 generic framework theorems
(emitter, lowerings, AIG optimisation, validated emission, word-level rewriting,
tree translation, refinement rules, bit-blasting, word SystemVerilog round trip,
reset, builder, memory and instance rules).
[Review.md](Review.md) is generated from them by `hdlean review`.

## Checks

- `lake build` and `leanchecker --fresh Designs` (official kernel).
- Challenge audit: axioms, and statement constants from frozen modules or declared holes.
- `lake exe tests`: arbitrary-power-up simulation of every design against its
  reference (9,000 circular-FIFO, 9,600 RAM, 240 CPU, 2,400 pipeline, 8,400 FIFO and
  1,200 counter cycles), plus emitter read-back and mutation rejection.
- `scripts/check_backends.py`: AIGER interpretation, 100 Icarus cycles and Yosys
  RTLIL/SystemVerilog equivalence for every design; a corrupted next state must fail.
  For word-level designs, Icarus also runs the word SystemVerilog and the
  bit-blasted netlist side by side against 200 cycles of the Lean trace of
  `Design.step`, and Yosys elaborates the word-level text (hierarchy, memories).
  For the counter, the general-depth FIFO and the word-level RAM, `abc-emit` must be
  validated, match the trace and be Yosys-equivalent to the plain emission.
  A corrupted ABC result is refuted by the SAT solver and not adopted.
- `scripts/check_native_clocks.py`: native multi-domain SV/RTLIL for a two-domain
  fixture, including wrong-clock rejection.
- `Tests/test_workflow.py`: the audit rejects foreign axioms and agent-defined
  statement constants; a weakened agent theorem breaks the frozen challenge.

## Emitted sizes (bit-level formats, width 8)

| Design | State bits | AND gates, lowering only | AND gates, emitted | Logic depth | AND gates, `abc-emit` (validated) |
| --- | --- | --- | --- | --- | --- |
| Counter | 4 | 152 | 33 | 8 | 26 |
| FIFO | 18 | 126 | 107 | 5 | 106 |
| Pipeline | 54 | 378 | 319 | 5 | 316 |
| RAM, register array (16 × 8) | 136 | 4,992 | 796 | 34 | 724 |
| RAM, word level (16 × 8) | 136 | 788 | 788 | 8 | 710 |
| General-depth FIFO | 144 | 19,180 | 1,288 | 17 | 830 |
| Toy16 CPU, bit level | 4,288 | 62,072 | 40,822 | 50 | 25,057 |
| Toy16 CPU, word level | 4,312 | 27,825 | 27,764 | 53 | 25,164 |

"Lowering only" is `Dag.lowerTight`; "emitted" adds the proved `Graph.optimize`
(what `emit` writes and `metrics` reports). The word-level designs come from the
proved bit-blaster; memories are counted as state bits here, and stay memories in
the word-level SystemVerilog. No retiming; synthesis improves on these numbers.
Physical measurements are run on demand ([Physical.md](Physical.md)) and not committed.

## Known gaps

- Dual-clock FIFO hardware still uses the legacy multi-clock model (clock labels,
  deterministic sampling). Its challenge is model-level until it moves to
  `MultiClock.Shared.MultiDag` (milestone R2).
- Word-level RTLIL is not printed yet (bit-level RTLIL is); Yosys reads the word
  SystemVerilog instead.
- The word-level pass rewrites cells in place but does not remove dead cells (that
  needs renumbering); the two word-level designs have nothing for it to rewrite.
- No sequential optimisation (retiming, register merging, state re-encoding):
  deferred, see [Design.md](Design.md) 13.5.
- The word IR has one clock domain; multi-clock designs still use the bit-level
  multi-clock layer.
- Exact emitted bytes are not kernel-checked; the proved-parser read-back replaces it.
