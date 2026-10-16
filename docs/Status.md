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
one gate per AND), which `emit_correct` covers.

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

`scripts/verify.py` audits 40 theorems: the 17 challenge theorems and 23 generic
framework theorems (emitter, both lowerings, tree translation, refinement rules,
bit-blasting, word SystemVerilog round trip, reset, builder, memory and instance rules).
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
- `scripts/check_native_clocks.py`: native multi-domain SV/RTLIL for a two-domain
  fixture, including wrong-clock rejection.
- `Tests/test_workflow.py`: the audit rejects foreign axioms and agent-defined
  statement constants; a weakened agent theorem breaks the frozen challenge.

## Emitted sizes (bit-level formats, width 8)

| Design | State bits | AND gates | Logic depth |
| --- | --- | --- | --- |
| Counter | 4 | 152 | 15 |
| FIFO | 18 | 126 | 5 |
| Pipeline | 54 | 378 | 5 |
| RAM, register array (16 × 8) | 136 | 4,992 | 38 |
| RAM, word level (16 × 8) | 136 | 788 | 8 |
| General-depth FIFO | 144 | 19,180 | 32 |
| Toy16 CPU, bit level | 4,288 | 62,072 | 54 |
| Toy16 CPU, word level | 4,312 | 27,825 | 53 |

Counted after `Dag.lowerTight`. The word-level designs come from the proved
bit-blaster; memories are counted as state bits here, and stay memories in the
word-level SystemVerilog. There is no constant folding beyond the AIG
constructors' and no retiming; synthesis improves on these numbers. The ECP5
reports in `docs/reports/` predate both changes and should be re-run.

## Known gaps

- Dual-clock FIFO hardware still uses the legacy multi-clock model (clock labels,
  deterministic sampling). Its challenge is model-level until it moves to
  `MultiClock.Shared.MultiDag` (milestone R2).
- Word-level RTLIL is not printed yet (bit-level RTLIL is); Yosys reads the word
  SystemVerilog instead.
- No verified optimisation pass on the word IR yet (constant folding, dead cells).
- The word IR has one clock domain; multi-clock designs still use the bit-level
  multi-clock layer.
- Exact emitted bytes are not kernel-checked; the proved-parser read-back replaces it.
