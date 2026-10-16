# Implementation decisions

| Date | Decision | Reason and consequence |
| --- | --- | --- |
| 2026-10-15 | Implement synchronous memory first as an explicit register array | The generic physical trace proof includes arbitrary initial contents and read-before-write collisions. Storage is measured honestly as flip-flops; technology RAM macros remain a separate mapping choice. |
| 2026-10-15 | Check exact printed bytes by a strict parser and generic semantic validator | The compiler, printer and certificate generator remain untrusted. A successful kernel certificate relates actual ASCII artifact bytes to the circuit, with independent nanoda replay available. |
| 2026-10-15 | Validate every shared graph with a generic kernel-proved symbolic checker | Closes the compiler/cache trust gap without proving a particular sharing algorithm. Canonical Boolean cones include constant folding, complements, and commutative ordering. Emission fails if the validator cannot establish equivalence. The explicit total order permits kernel replay, unlike Lean's opaque derived recursive `Ord`. |
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

## Subsequent implementation decisions

| Decision | Reason and consequence |
| --- | --- |
| Implement general power-of-two circular queues as well as the two-entry FIFO | Generic ghost-history proofs cover bounded occupancy, oldest data, wraparound and no overwrite. Physical word-bank circuits refine those models for every depth exponent and width. Padding and register-array storage are counted explicitly. |
| Keep serialized fetch/execute as the Toy16 baseline | The physical AST now implements the entire ISA and retirement interface, with reset and two-cycle progress proofs. It has placed and routed on ECP5. Overlapping instruction execution remains an alternative microarchitecture, not an unstated throughput claim. This supersedes the earlier statement that the core was unsynthesizable. |
| Add physical multi-clock circuits and typed CDC primitives | Registers carry explicit domain assignments. SV/RTLIL use actual independent clocks; AIGER uses explicit edge inputs. Generic graph/parsed-text proofs and external wrong-clock mutations cover those assignments. |
| Replace the list compiler cache with an untrusted native DAG candidate builder | Source-pointer memoization and AND hash-consing make the full CPU practical. Acceptance still requires generic proved local gate validation; unsafe pointer hints never establish equality or a theorem. The original total compiler remains the logical fallback. |
| Add a local graph validator alongside normalized formulas | Proof-carrying memo entries and ordered gate maps avoid expanding shared symbolic cones. Kernel certificates work for small instances; large concrete source/text certificates still have a measured memory limit. |
| Realize finite latency using explicit delay banks | An arbitrary mathematical stream transducer is not synthesizable. Finite banks have generic latency, startup and retiming theorems, including the zero-register case. |
| Use finite reachability as the initial invariant oracle | The oracle suggests a membership relation; initialization, closure and safety must pass a generic kernel-checkable certificate. `refute_small` is an explicit sample diagnostic. This provides the intended untrusted-oracle workflow without requiring IC3. |
| Measure FPGA implementation with pinned Yosys/nextpnr | ECP5 fits the complete register-array CPU where iCE40HX8K did not. Reports retain constraints, binary/model/artifact hashes and actual timing/utilization. No process library or analog measurement is invented. |

## Design revision v0.2 (2026-10-16)

These follow the review of this implementation; [Design.md](Design.md) section 15.5 lists the findings and section 16 the remediation milestones.

| Decision | Reason and consequence |
| --- | --- |
| Move to Lean 4.35.0 | Bundles `lean4lean`, `nanoda`, `con-leche`, `con-ron` and `leanchecker-paranoid`, plus `lake check` and `lake comparator`. The project builds unchanged. The Rust build of nanoda and the separate exporter checkout are removed; `bootstrap.py` now pins the bundled binaries. Default Lake targets are libraries only, so `lake check` can export them. |
| Require `lake check --paranoid` in CI | Every declaration of the project, not only the audited roots, is replayed by five kernels. |
| Read the approved manifest digest from a protected CI variable | A manifest stored in the branch cannot be its own trust anchor (finding F4). CI warns until `HDLEAN_TRUSTED_MANIFEST_SHA256` is set. |
| Planned: explicitly shared core, proved emitter, byte binding only | Replaces per-design validators that the kernel could not re-run for the CPU (finding F6). |
| Planned: domain-indexed multi-clock logic with the sampling oracle in hardware semantics | Raw multi-bit crossings type-checked and metastability was fixed to "always old" in the hardware link (finding F1). |
| Planned: every claimed theorem in a frozen challenge, compared by statement | A theorem weakened to `True` passed L1 (finding F2). |

The historical entries above record decisions at the time. Later entries supersede
implementation limitations as the corresponding features and proofs land. The
[current coverage](Status.md) and [trust boundary](Trust.md) describe the result.

| v0.2 implementation decision | Reason and consequence |
| --- | --- |
| Preserve an oracle primitive in the lowered multi-domain graph | Each domain lowers independently; only an explicitly declared crossing names foreign registered bits. Physical graph execution samples every first flop with the caller's per-bit old/new oracle and samples the old first flop into the second. Generic lowering preserves all choices. Native hierarchical text integration is a separate remaining step. |
| Keep the per-use temporal crossing obligation explicit | A Gray counter advancing once per **source** edge need not differ in only one bit between **destination** edges when the source is faster. `MultiDag.SourceSafe` states the actual interval condition; a one-bit source satisfies it for every schedule. Multi-bit uses need an interval proof or an explicit rate/advance bound. A Gray type tag does not discharge that condition. |
| Freeze stronger queue statements as well as supporting invariants | The circular FIFO now refines the full reviewed list machine at every post-reset observation for all widths/depths. Supporting ghost invariants alone are insufficient headline obligations. |
