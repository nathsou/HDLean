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

## Consolidation, milestone R5 (2026-10-16)

| Decision | Reason and consequence |
| --- | --- |
| Official Lean kernel only | Owner's choice. `lake build` and `leanchecker --fresh` check everything; the export-based replay with nanoda, con-leche, con-ron and lean4lean, the custom comparator and the bundled-kernel scripts are removed. |
| One pipeline: tree circuits compile to node graphs by the proved `Circuit.toDag` | The validator-based tree pipeline (graph validators, fast compiler, old printers and parsers, tree netlist) is deleted. Every design is emitted by the generic proved emitter. |
| Drop exact-byte certificates; read every emitted file back with the proved parser | `emit_correct` already fixes what `emit c` means. Read-back guards the compiled code and the file write at negligible cost; byte certificates did not scale to the CPU. |
| Readable challenges, enforced by statement constants | The generated 2,928-line statement dump, the claims and declaration-fingerprint files and per-design comparator configs are replaced by hand-written `Challenge.lean` files. The audit requires every statement constant to come from a frozen module, Lean, or a declared implementation hole. |
| Frozen interfaces for the general-depth and dual-clock FIFOs | Their observation and input maps were agent-defined. Progress for the dual-clock FIFO is now stated from reset, not from an agent-defined relation. |
| Dual-clock FIFO hardware emitted event-encoded | Its native multi-clock printer used the deleted validators. Clock edges become inputs and the single-clock proved emitter applies; native emission returns with milestone R2. |

The historical entries above record decisions at the time. Later entries supersede
implementation limitations as the corresponding features and proofs land. The
[current coverage](Status.md) and [trust boundary](Trust.md) describe the result.

| v0.2 implementation decision | Reason and consequence |
| --- | --- |
| Preserve an oracle primitive in the lowered multi-domain graph | Each domain lowers independently; only an explicitly declared crossing names foreign registered bits. Physical graph execution samples every first flop with the caller's per-bit old/new oracle and samples the old first flop into the second. Generic lowering preserves all choices. Native hierarchical text integration is a separate remaining step. |
| Keep the per-use temporal crossing obligation explicit | A Gray counter advancing once per **source** edge need not differ in only one bit between **destination** edges when the source is faster. `MultiDag.SourceSafe` states the actual interval condition; a one-bit source satisfies it for every schedule. Multi-bit uses need an interval proof or an explicit rate/advance bound. A Gray type tag does not discharge that condition. |
| Freeze stronger queue statements as well as supporting invariants | The circular FIFO now refines the full reviewed list machine at every post-reset observation for all widths/depths. Supporting ghost invariants alone are insufficient headline obligations. |
| Render complete files with right recursion | Lean 4.35's logical `String.intercalate` accumulates and recopies a growing prefix. The proved-equivalent `Text.join` copies each short line fragment once, preserving exact existing bytes and making pure kernel emitter evaluation linear in output size. |
| Make register allocation explicit in the surface monad | `circuit do` allocates node references and typed register handles, with complete single-driver checking at finalization. `treeCircuit do` preserves the older expression syntax for existing examples. Register capacity remains an explicit finite type parameter; user code does not calculate storage offsets. |
| Keep whole-project and root-only axiom policies distinct | Lake exports unused Prelude axiom declarations, including `sorryAx`. Its whole-project nanoda policy skips unpermitted declarations but rejects every reference to them, followed by Lake's complete used-axiom audit. Root exports retain strict declaration rejection. Native checker regressions cover both cases. |
| Expose source registers through proved state observation ports | Native domain modules have no foreign register operations. The wrapper wires registered source pins into explicit first/second-flop primitives; its parser checks all dimensions, state taps and clock/reset connections. The generic parsed meaning preserves every sampling oracle without adding an oracle input pin. |
| Emit scalar SV logic and storage wires | Very large packed buses caused excessive Icarus elaboration. Scalar names keep sharing explicit; a wire alias preserves the documented packed state observation. Both native printers tie the unused padding bit to zero, without initializing any real register. External transition checks split state aliases before exposing all flip-flop pins. |

## Proved optimisation passes, v0.5 (2026-10-16)

| Decision | Reason and consequence |
| --- | --- |
| Order: AIG pass, then validated ABC, then word-level rewriting; sequential passes deferred | Measured headroom: the bit-level designs carried 15–93% dead or duplicate gates, the word-level ones were within ~10% of ABC, and synthesis consumes word SystemVerilog anyway. Sequential passes change the store layout and power-up behaviour. |
| Checked passes: analyses are hints, steps are justified locally, failure returns the input | Liveness, hash tables and the external optimiser never need proofs. A hash hit is re-checked against the gate or cell it names. The proofs cover only the rewrite steps (`Rw.step_ok`, `step_sound`). |
| The AIG pass runs inside every backend (`Dag.lowerOpt`) | `emit_correct` covers it, metrics report what is shipped, and every format benefits. |
| Validate ABC with a miter, Lean's `AIG.toCNF` and `LRAT.check` | Both are proved in Lean's standard library (`toCNF_equisat`, `check_sound`), so the whole chain runs on official-kernel theorems with no `bv_decide` or native axioms. CaDiCaL is the one bundled with Lean. Adopted graphs keep our ports and names (`adopt`). |
| Binary AIGER reader and writer unproved | ABC reads binary AIGER only. What goes out is a copy of a proved graph; what comes back is validated. |
| Word-level pass keeps every cell index | Cells are rewritten in place (a merged duplicate becomes `zext` of the earlier cell at the same width), so registers, memory ports, outputs and instance store slots need no renaming, and `optimize_sem` transfers challenges with a two-line proof. Dead-cell removal needs renumbering and is left for later. |

## Word-level RTL, v0.4 (2026-10-16)

| Decision | Reason and consequence |
| --- | --- |
| Add a word-level IR beside the bit-level node graph | Memories, word operators (arithmetic, shifts, comparisons, mux, slice, concat, extensions), module instances and typed records were the four scaling gaps. Values are `BitVec` operations on raw naturals read at a width, so the semantics is exactly Lean's bit-vector library, division by zero included. |
| Intrinsically valid builder | Each primitive checks widths and references when it appends a cell, and the builder state carries the validity proof; cells refer only to earlier cells and instances only to earlier modules, so combinational loops and recursive hierarchies cannot be written. |
| Memories: combinational read, synchronous write ports, later ports win, never reset | Matches what synthesis maps to block RAM and keeps the semantics total. A memory always has exactly `2^aw` words after a cycle (`Mem.shape`), so every store is a power-up state. |
| Hierarchy by dependency order; a child is a black box | `Design.sem` evaluates module `k` with the semantics of earlier modules only; `instantiate_ensures` exposes a child's outputs through `e.sem j`, which `Design.env_lt` identifies with the child's own theorem. |
| Bit-blast with Lean's verified `bv_decide` blasters, proved end to end | Reusing `Std.Tactic.BVDecide`'s verified circuits gives all operators for free; `Design.toDag` correctness covers hierarchy flattening, memory decoders and reset. Only the official kernel is involved; `bv_decide` itself is not used as a tactic. |
| Reset as per-bit reset kinds | `sem_reset`: outputs never depend on reset, and the next store under reset is the reset-low store with a per-bit `resetValue`, which is what the node graph applies. |
| Gate-count-preserving lowering `Dag.lowerTight` | The fixed three-gates-per-node layout inflated blasted designs six-fold and made metrics meaningless. A wire table makes negation free and AND one gate; correctness and well-formedness are proved with the same contract, and `emit_correct` now uses it. |
| `hdl_record` instance proofs by `dsimp` and `HVec.rebuild_eq` | The `rfl` proof of `ofVec (toVec r) = r` was exponential in the number of fields (75 s for 14). |
| Normalize record specifications before rebuilding records | Proofs that rebuild a 13-field record from per-field facts timed out on unification of `(toVec (decode ..)).tail^k.head` against field projections; `simp only [Bundle.toVec, HVec.head_cons, HVec.tail_cons]` first makes it syntactic (90 s to 4 s for the Toy16 body). |
| Instruction bus as an input in the word-level Toy16 | A real core does not embed its program as a ROM. The interface answers the fetch address shown on the outputs with the program word in the same cycle (`loop`), which is possible because outputs are registered. |
| Review document generated from the environment | `hdlean review` imports the compiled modules and pretty-prints every challenge statement with notation, its axioms and the definitions it uses, then runs scenarios through spec and design. `verify.py` fails if `docs/Review.md` is stale. |
