# Implementation coverage

The [v0.2 design revision](Design.md) reviews this implementation: section 15.5 lists six gaps (clock-domain crossing in emitted hardware, unfrozen theorem statements, the CPU observation map, a self-referential manifest check, bit-level queue models, and the CPU certificate roadblock) and section 16 the milestones that close them. Rows below describe what is implemented, not those planned changes.

HDLean implements the v0.1 framework and all roadmap example families, with the
explicit design choices below. No unfinished theorem is represented by `sorry`
or a replacement axiom. Acceptance evidence and resource limitations are kept
separate from implementation coverage.

| Area | Implemented and checked |
| --- | --- |
| Machines/reset | Arbitrary power-up; explicit reset inputs; generic simulation and non-interference; arbitrary reset reassertion for physical counter and synchronous FIFO |
| Types/syntax | Dimension/domain-indexed finite AST; compact finite layouts; generic structure/enum `deriving Synth`; ordinary `circuit do` conditionals, logic, equality and word arithmetic |
| Core/composition | One next-state driver per register; bounded wiring; explicit reset kinds; Moore proof requirement; generic physical network transition/output/trace refinement |
| Lowering | Generic kernel proofs for expressions, transitions and outputs; proved normalized-formula and local-gate graph validators; untrusted native DAG candidate compiler |
| Backends | SystemVerilog, AIGER and RTLIL; strict parsed-text semantic validation before emission; native multi-clock SV/RTLIL and explicit-edge AIGER |
| FIFO | Generic payload-width refinement on the two-entry AST; reference scenarios, mutations, throughput and exact register budget |
| Circular FIFO | Generic power-of-two-depth queue safety/order proof; physical bounded word-bank AST; arbitrary-power-up/reset, wraparound and exact storage proofs; 9,000 physical reference cycles |
| Memory | Physical register-array synchronous read-before-write RAM; generic arbitrary-power-up trace proof and exact budget; 9,600 collision/reset cycles |
| Pipeline/latency | Physical three-stage elastic pipeline refinement; 2,400 reference cycles; causal `Pipe` contracts; finite delay realization and latency/retiming theorems including zero stages |
| Toy16 | Full ISA; physical fetch/execute AST; generic opcode, transition, retirement and reset proofs; two-cycle progress bound; 240 arbitrary-power-up physical cycles; actual placed/routed CPU |
| Clock crossing | Independent/coincident edges; typed named two-flop primitives; generic Gray adjacency/injectivity and arbitrary bit-mixture proofs |
| Async FIFO | Generic ghost-history queue safety under arbitrary edge/sample masks; held-reset startup; physical two-domain AST/control/memory correspondence; clock-checked backend and external wrong-clock mutations |
| Automation | Kernel proof tactics; finite invariant search with checked initialization/closure/safety; sampled relation refutation; goal rendering; named/source-aware counterexamples and VCDs |
| Independent checking | Frozen candidate manifest; typed challenges; fresh Lean kernel replay; `lake check --paranoid` with the five kernels bundled in Lean 4.35.0; bundled nanoda/con-leche/con-ron replay of headline roots; strict baseline-axiom policy; exact byte binding and adversarial rejection tests |
| Physical metrics | Actual structural counts; proved progress/budgets; pinned Yosys/ABC/nextpnr flow; routed ECP5 counter, elastic pipeline and complete CPU reports |

## Acceptance evidence and roadblocks

The 77 audited headline roots have passed independent nanoda replay over **6,680
declarations**. Exact counter and FIFO8 bytes in all three formats have passed
kernel/nanoda replay and byte-for-byte artifact binding. Every native emission
also requires the generic graph and final-text semantic validators.

A full concrete CPU artifact certificate remains a **real resource roadblock**.
Its 744,329-byte AIGER file has 40,745 AND gates and 4,288 physical state bits. Single-module
per-line and chunked exact-byte proofs exceeded the 6 GiB Lean allocation cap;
a further attempt with separate 64 GiB address-space and 12 GiB resident/managed
memory limits also failed during lexical checking. A graph-only concrete reduction
reached over 7 GiB process memory before being stopped. Staging lexical proofs
across 23 modules checked all 705 chunks, but the complete parser/graph certificate
has not passed. Even a graph-only experiment with separately checked header
proofs, linear indexing and bounded cache hints exhausted an 11.5 GiB managed
allocation limit (12 GiB RSS watchdog). No CPU byte-certificate success was emitted.
The [measured limits](reports/cpu-certificate-resources.json) and a
[self-contained reproducer](reports/cpu-certificate-reproducer.tar.gz) preserve
the failed experiment. The generic semantic
proofs and independently replayed physical CPU theorems do not erase this gap.

The isolated comparator is implemented, with approved implementation holes,
transitive specification-body comparison and independent byte authentication.
Genuine namespace integration passed on GitHub Actions, including acceptance
of changed correct implementations and rejection of altered statements, hidden
axioms, weakened compiled specifications and mismatched bytes. This managed
workspace does not permit nested user/network namespaces; local skips grant no
assurance. CI also passed the additional primitive-definition authentication
against the independently approved reference. The complete hardware and comparator
jobs passed at `fac1947` in [run 38829509806](https://github.com/nathsou/HDLean/actions/runs/38829509806).
The later `ef4d7ed` staging/traversal checkpoint passed the complete local L1
proof/byte workflow and genuine comparator CI; see the PR checks for final
external-backend results. A reviewer-approved receipt is always external
input; a candidate manifest or fixture approval never approves this project.

The pinned physical CPU run meets **12 MHz** on ECP5-25K and reports **47.02 MHz**
register Fmax, 12,629 combinational cells and 4,234 mapped flip-flops. See
[the reproducible flow and reports](Physical.md) for constraints and provenance.

## Deliberate implementation bounds

- Toy16 alternates fetch and execute. Its theorem promises retirement within two
  cycles; it does not promise overlapping instruction execution or one IPC.
- RAM and circular/async FIFO memory are explicit finite register arrays. There
  is no technology RAM macro or hidden storage estimate. Uniform bank padding is
  counted in AST budgets; mapped counts may shrink through synthesis.
- Async startup holds both resets until both clocks have observed a reset edge.
  The queue theorem then covers arbitrary edge interleavings and sample masks.
  Independent reset assertion during traffic requires a new reset epoch/protocol.
- The finite invariant oracle uses reachability saturation, with fuel and checked
  obligations. It does not claim to implement IC3 or solve arbitrary instances.
- Mathematical `Pipe` contracts may contain arbitrary functions. Synthesis uses
  finite hardware constructors with separate realization proofs.
- Tagged unions with payloads use explicit layouts. Deriving layouts for those
  unions, vendor RAM mapping and alternative overlapping CPUs are extensions.

The [decision log](Decisions.md) records revisions to the proposal's implementation
choices. The [trust boundary](Trust.md) explains what each acceptance path proves.
