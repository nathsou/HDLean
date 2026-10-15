# Implementation coverage

HDLean v0.1 is a working, tested foundation. **The entire proposed project is not
complete.** No unfinished theorem is represented by `sorry` or a replacement
axiom. Missing guarantees below are engineering work, not accepted assumptions.

| Area | Implemented and checked | Remaining |
| --- | --- | --- |
| Machines/reset | Arbitrary power-up; reset schedules; generic simulation; power-up non-interference | Re-assertable reset refinement contracts beyond the startup theorem |
| Types | Domain/dimension-indexed Boolean AST; compact finite encodings; structure/enum `deriving Synth` | Tagged unions with payloads require explicit layouts |
| Syntax | Lean `circuit do` reifies conditionals/equality/logic; proved word arithmetic, comparisons and extension | Richer hardware diagnostics and imperative register builder |
| Core | One driver/register; combinational trees; explicit reset; Moore proof requirement | Typed module instances/memory/CDC nodes in the synthesis AST |
| Lowering | Generic kernel proofs for expressions, reset transitions, outputs; generically proved graph translation validator required by emission | Direct proof of compiler total acceptance (validation rejects conservatively) |
| Backends | SystemVerilog, AIGER, RTLIL; strict parsed-text semantic validation; exact-byte kernel/nanoda certificates for counter and FIFO8 | Checked external synthesis certificates; larger text-certificate scaling |
| Graph certificates | Generic soundness theorem; kernel certificates for counter and one/eight-bit FIFO; mandatory runtime checks through width 64 | Shared representation for very large symbolic cones |
| FIFO | Generic payload-width proof on the actual two-entry circuit; scenarios, mutations, throughput, register budget | General-depth circular FIFO refinement and RAM lowering |
| Circular FIFO | Power-of-two executable ring; garbage-state/reset/wraparound regressions | Generic correctness theorem and physical AST |
| Composition | Generic Moore network theorem; physical network elaboration and trace proof; physical three-stage pipeline refinement | Heterogeneous instance ergonomics |
| Latency | Causal stream contracts with proved `comb`, `seq`, `par`, `delay` | Finite-state realization of every contract; retiming transformations |
| Toy16 | ISA; single-cycle model; serialized fetch/execute model; reset/retirement/progress theorem; sum scenario | Synthesizable core AST, netlist, pipelining with overlapping instructions, physical metrics |
| Clock crossing | Independent edges/masks; sync2 behavior; generic Gray adjacency/injectivity and mixture proofs | Hardware CDC primitives and multi-clock backend |
| Async FIFO | Generic ghost-history queue safety, actual Gray synchronizer/control/memory correspondence, held-reset startup under arbitrary edges/masks | Synthesizable primitive and multi-clock backend |
| Memory | Physical register-array RAM; generic arbitrary-power-up trace proof and exact budget; 9,600 collision/reset test cycles | Technology RAM macro mapping |
| Tactics | `circuit_simp`, `simulation`, `hw_cases`, `hw_step`, kernel variant, `compose`, `nonint`, `k_induction` | IC3/invariant suggestions, relation-refutation tactic, signal-level goal rendering |
| Trust workflow | Frozen source manifest; typed challenges; fresh kernel and pinned nanoda replay; strict axiom policy; exact artifact byte certificates; adversarial rejection tests | Comparator isolation, reviewer approval enforcement and L2/L3 |
| Performance | Structural counts/depth; throughput/progress theorems; proved local rewrites; optional Liberty synthesis script | PDK calibration, OpenSTA/OpenROAD/nextpnr flows, placed/routed timing and power |

## Roadmap exit tests

- **M0:** implemented, including the reset theorem and non-vacuity witness.
- **M1:** the two-entry FIFO is proved on its AST and external RTL checks pass;
  the proposed L2 comparator exit test remains unmet.
- **M2:** core tactics, deterministic refutation-by-testing and waveform output
  work; external invariant discovery and richer diagnostics remain open.
- **M3:** the physical three-stage circuit is proved by composition and checked
  against the reference model on 2,400 cycles.
- **M4:** the serialized two-stage model has the headline retirement and progress
  proof; synthesizable core lowering and overlapping pipeline implementation remain open.
- **M5:** the Gray-pointer model has generic queue safety and held-reset startup
  proofs; physical multi-clock lowering remains open.
- **M6:** structural reports and optional real synthesis are available; a physical
  pipelined-core sign-off report is not available.

The provided challenge files are reviewer candidates. CODEOWNERS is an aid to
review; without server-side required-review rules it is not an access-control
boundary. Nothing in this repository self-approves its specifications.
