# Extending HDLean

1. Write the reference model and observation map in `Spec.lean` and `Interface.lean`.
   Pin boundary scenarios and bad-design mutations. Use `Option` for invalid data.
2. State exact reset, refinement, progress and resource obligations in `Challenge.lean`.
   Specs and challenges remain review candidates until approved externally.
3. Implement finite hardware expressions. Put arbitrary functions only in the
   mathematical model or explicitly modeled primitives, never into AST constructors.
4. Simulate from garbage initial state before proving. Apply the generic simulation
   theorem and prove reset, one-step preservation, and observation agreement.
5. Compile and compare the exact circuit, not a separately maintained handwritten RTL.
   Add per-instance graph certificates when feasible and independent backend checks.
6. Run `lake build`, `lake exe tests`, `python3 scripts/verify.py --backends`, and
   `python3 Tests/test_workflow.py`. Review the per-theorem axiom report.

Framework and trust-surface changes require a new candidate manifest:
`python3 scripts/freeze.py --write`. A reviewer should compare it with the prior
version and approve its digest outside the submission. Never edit the manifest
just to make an unexpected verification failure disappear.

`hw_step_kernel` uses simplification, arithmetic and kernel-checkable proof search.
`hw_step` also permits `bv_decide`; its native axioms must appear in the report.
Use `decide +kernel` for fixed finite certificates. The local graph validator checks
shared gate equations without expanding symbolic cones. Its native candidate path
scales to the full CPU; concrete kernel reduction remains more resource intensive.

`invariant? system, fuel` suggests a finite reachable-state membership invariant.
`FiniteSystem.check_sound` turns kernel-checked initialization, closure and safety
obligations into an all-traces theorem. Fuel exhaustion never establishes safety.
`refute_small samples with predicate` rejects sampled counterexamples before a
relation proof; it adds no hypothesis. `hw_goal` renders the remaining obligations.
Trace JSON retains register/source names, and waveform VCDs expose individual bits.
Use `--signals state.count_0 inputs.rst` to select named table/VCD signals.

`Delay.hardware stages width` realizes a fixed finite latency from arbitrary
startup storage, including a zero-stage wire. `Delay.latency`, `realizes_pipe` and
`retime` prove the warmup and movement of pure combinational logic across the bank.
An arbitrary mathematical `Pipe` is a contract, not an automatic synthesis request.

There are no imported solver services or external invariant results silently
trusted by the build. Future invariant-search tools must suggest replayable
relations or certificates; they must not introduce axioms.

## Specification v0.2 trust setup

`Verification/Challenge.lean` contains the literal statements of all audited
claims. Its proof aliases are checked on every L1 build. The independently built
`Verification/Solution.lean` copies the actual implementation theorem types;
per-block `comparator.json` files compare those types and their specification
closure using `lake comparator`. The common challenge is protected by the frozen
manifest. Toy16's state and retirement observation maps are in its protected
`Interface.lean`.

The `approved-specifications` CI check fails unless the repository owner supplies
`HDLEAN_TRUSTED_MANIFEST_SHA256` as a protected repository variable after reviewing
the candidate manifest. Development checks remain available without approval.
The candidate digest printed by `scripts/freeze.py --write` is never approval.
Apply `verification/branch-protection.json` to the main branch using GitHub's
branch protection API or equivalent settings. This requires repository admin
access and must include required code-owner review; committing this JSON alone
does not enable branch protection.

The statement audit also compares the complete dependency meaning with
`verification/declarations.json`. This catches changes to helper predicates such
as `Ghost.Safe` even when a theorem keeps the same syntactic type. Only the safe
implementation definitions listed in the comparator configurations may change
body. `scripts/statement_audit.py --record-candidate` prepares new review material;
it is not approval and cannot update the protected repository variable.

Bootstrap places `nanoda-hdlean` in `work/independent-tools/bin`; add that directory
to `PATH` before invoking the block comparators. This adapter authenticates the
unchanged bundled nanoda binary, uses its serial path with a larger OS stack, and
requires an unqualified success report. Lake 4.35's hardcoded four-thread config
overflows nanoda 0.4.19's fixed worker stack on the pipeline proof.
