# Implementation coverage

HDLean v0.1 is a working, tested foundation. **The entire proposed project is not
complete.** No unfinished theorem is represented by `sorry` or a replacement
axiom. Missing guarantees below are engineering work, not accepted assumptions.

| Area | Implemented and checked | Remaining |
| --- | --- | --- |
| Machines/reset | Arbitrary power-up; reset schedules; generic simulation; power-up non-interference | Re-assertable reset refinement contracts beyond the startup theorem |
| Types | Domain/dimension-indexed Boolean AST; finite `Synth` encodings | Automatic structure/enum deriving; compact `Fin` encoding |
| Syntax | Lean `circuit do`, explicit typed word builders | Reification of ordinary arithmetic/conditionals; richer hardware diagnostics |
| Core | One driver/register; combinational trees; explicit reset; Moore proof requirement | Typed module instances/memory/CDC nodes in the synthesis AST |
| Lowering | Generic kernel proofs for expressions, reset transitions, outputs | Generic theorem for graph sharing/numbering |
| Backends | SystemVerilog, AIGER, RTLIL; independent parser/simulator/equivalence checks | Verified text printers/parsers and checked external synthesis certificates |
| Graph certificates | All-state/all-input kernel certificates for counter and one-bit FIFO | Parameterized/large-instance certificate generation |
| FIFO | Generic payload-width proof on the actual two-entry circuit; scenarios, mutations, throughput, register budget | General-depth circular FIFO refinement and RAM lowering |
| Circular FIFO | Power-of-two executable ring; garbage-state/reset/wraparound regressions | Generic correctness theorem and physical AST |
| Composition | Generic Moore network theorem; three-stage valid/ready proof; causal assume/guarantee theorem | Bit-level network elaborator and physical composition proof |
| Latency | Causal stream contracts with proved `comb`, `seq`, `par`, `delay` | Finite-state realization of every contract; retiming transformations |
| Toy16 | ISA; single-cycle model; serialized fetch/execute model; reset/retirement/progress theorem; sum scenario | Synthesizable core AST, netlist, pipelining with overlapping instructions, physical metrics |
| Clock crossing | Independent edges/masks; sync2 behavior; stable-source theorem; Gray examples | Generic-width Gray proofs; hardware CDC primitives |
| Async FIFO | Gray-pointer model, independent clocks, conservative full/empty; reset/no-edge theorems; oracle simulations | Full queue-safety theorem, separate-domain reset protocol, synthesizable primitive |
| Memory | Finite synchronous read-before-write primitive and local proofs | Backend primitive lowering/macros |
| Tactics | `circuit_simp`, `simulation`, `hw_cases`, `hw_step`, kernel variant, `compose`, `nonint`, `k_induction` | IC3/invariant suggestions, relation-refutation tactic, signal-level goal rendering |
| Trust workflow | Frozen source manifest; typed challenges; fresh kernel replay; strict axiom report; rejection tests; artifact hashes | Adversarial comparator isolation, reviewer approval enforcement, nanoda and L2/L3 |
| Performance | Structural counts/depth; throughput/progress theorems; proved local rewrites; optional Liberty synthesis script | PDK calibration, OpenSTA/OpenROAD/nextpnr flows, placed/routed timing and power |

## Roadmap exit tests

- **M0:** implemented, including the reset theorem and non-vacuity witness.
- **M1:** the two-entry FIFO is proved on its AST and external RTL checks pass;
  the proposed L2 comparator exit test remains unmet.
- **M2:** core tactics, deterministic refutation-by-testing and waveform output
  work; external invariant discovery and richer diagnostics remain open.
- **M3:** the three-stage model is proved by composition; physical network
  elaboration remains open.
- **M4:** the serialized two-stage model has the headline retirement and progress
  proof; synthesizable core lowering and overlapping pipeline implementation remain open.
- **M5:** the oracle model is executable and primitive lemmas are proved; full
  asynchronous FIFO safety and physical lowering remain open.
- **M6:** structural reports and optional real synthesis are available; a physical
  pipelined-core sign-off report is not available.

The provided challenge files are reviewer candidates. CODEOWNERS is an aid to
review; without server-side required-review rules it is not an access-control
boundary. Nothing in this repository self-approves its specifications.
