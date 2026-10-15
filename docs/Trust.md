# Proof and checking boundary

The Lean kernel checks all admitted theorems. `Tests/Axioms.lean` collects the
transitive axiom dependencies of named headlines from the environment, and
`scripts/verify.py` compares them with a strict allowlist. The FIFO, counter,
Toy16, structural lowering, and concrete graph certificates use only `propext`,
`Classical.choice`, and/or `Quot.sound`. The two eight-bit Gray lemmas additionally
use explicitly named native bit-blasting axioms. Those are reported, never hidden.

`leanchecker --fresh Designs` and `--fresh Tests` replay all imported declarations
into fresh Lean kernel environments. This helps detect environment corruption.
It does **not** implement an independent kernel, a process sandbox, or an external
comparator's full submission protocol. In particular, the L1 scripts must not be
used to execute hostile Lean metaprograms outside a suitable external sandbox.

The trusted manifest includes the framework, reference models, observation/input
maps, challenge files, toolchain, and verifier sources. L1 verifies the manifest's
file set and all its hashes. A manifest stored with a submission is not its own
trust anchor: a reviewer or protected CI configuration must supply the independently
approved SHA-256 through `--manifest-sha256`. Re-freezing sources writes
`approval: review-required` and is never treated as approval. CODEOWNERS only
becomes enforced when repository branch rules require those reviews.

The audit harness requires every expected theorem exactly once. Missing,
duplicated, custom-axiom and `sorryAx` reports fail. The implementation and
interface are checked together against typed challenge declarations. L1 is still
a development workflow; it is not sufficient against arbitrary adversarial
checker modifications. L2 and L3 explicitly return failure.

## What reaches bits

`lowerExpr_correct`, `lower_next` and `lower_output` prove the semantic tree IR
matches the circuit AST. `Graph.validate_sound` proves that the executable symbolic
translation validator accepts only shared graphs equivalent to the exact circuit,
for every state, input, and reset value. Emission uses `checkedCompile`, whose
successful result carries this proof. The compiler, cache and graph numbering are
untrusted; a validation failure aborts emission. Concrete kernel-replayed certificates
also cover the counter and one/eight-bit FIFO. All printers consume
the same shared graph, preserve unconstrained power-up, and make reset explicit.

Independent checks interpret AIGER and compare transitions, simulate SystemVerilog
with Icarus, and ask Yosys to prove RTLIL/SystemVerilog equivalence. The check exposes matched register
inputs and next-state outputs, checks the resulting combinational relation, and
separately audits every original register’s width, clock, and edge polarity. A
corrupted next-state mutation must fail. The flow is tested with Yosys 0.33 and 0.52. These are useful
translation checks but not kernel-replayed proofs of the text printers. The report
records this gap. The executable `emit` command is a development command, not an
acceptance gate. Artifacts produced by `verify.py` are hashed along with the source
snapshot and verification results; a filename alone is never provenance.

## Physical claims

Two-flop metastability resolution is a named physical assumption of the CDC model.
The logical model represents arbitrary edge interleavings and old/new sampling,
not analog behavior or a frequency-ratio guarantee. Memory power-up values are
arbitrary. Async operation after independent reset assertion/release is not yet
proved.

AND count, Boolean depth and flip-flop count are structural quantities. Optional
Liberty mapping uses a real synthesis tool and records the library hash. Physical
timing, placement, power, and tape-out readiness are absent unless an actual flow
produces them; this version produces none of those claims.
