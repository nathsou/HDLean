# Implementation decisions

| Date | Decision | Reason and consequence |
| --- | --- | --- |
| 2026-10-15 | Rename the project and namespace to HDLean | Explicit user request. |
| 2026-10-15 | Support RTLIL; remove the proposed word-level model-checker backend | Explicit user correction. All active commands and tests cover SV/AIGER/RTLIL. |
| 2026-10-15 | Start the verified physical library with a two-entry shift-register FIFO | Small, auditable refinement proof for all payload widths. The circular model is retained separately. Storage costs `2w+2` flip-flops rather than the proposal's RAM/pointer budget. No general-depth claim is made. |
| 2026-10-15 | Use a bit-level expression AST and AND/inverter tree as the first semantic IR | Reduces the generic lowering proof to structural induction and Boolean identities. A shared graph is constructed afterwards and has explicit per-instance certificate obligations. |
| 2026-10-15 | Use a structural list cache during graph construction | Kernel reduction can check translation certificates; native hash functions prevented kernel-only evaluation. This trades scaling performance for a smaller initial trust boundary. |
| 2026-10-15 | Require a proof before obtaining Moore denotation | An input-dependent expression must not be interpreted by substituting false inputs without justification. Mealy evaluation stays explicit. |
| 2026-10-15 | Serialize the two-stage Toy16 model | Fetch and execute alternate. The model has no forwarding/flush hazards and proves a stronger two-cycle progress bound; it is not an overlapping pipeline or a synthesized core. |
| 2026-10-15 | Make latency contracts causal stream transducers | A Moore machine cannot implement a nonconstant zero-cycle combinational pipe. Stream contracts support `Pipe 0`, while remaining distinct from finite hardware ASTs. |
| 2026-10-15 | Treat Gray safety as a temporal property | A Gray-encoded value alone does not make arbitrary jumps safe. The CDC model explicitly samples adjacent old/new source values; it does not expose arbitrary multi-bit casts. |
| 2026-10-15 | Ship an honest L1 verifier and reject L2/L3 | The adversarial sandbox, full printer proofs, reviewer approval and independent checker are unfinished. A passing development report must not imply sign-off. |

The guiding principles remain goals. Incomplete parts, especially the single
verified path through text printing, are listed as incomplete rather than being
silently added to the trusted computing base.
