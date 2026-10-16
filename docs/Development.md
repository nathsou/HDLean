# Extending HDLean

1. Write the reference model and observation map in `Spec.lean` and `Interface.lean`.
   Pin boundary scenarios and bad-design mutations. Use `Option` for invalid data.
2. State exact reset, refinement, progress and resource obligations in `Challenge.lean`.
   Specs and challenges remain review candidates until approved externally.
3. Implement finite hardware expressions. Put arbitrary functions only in the
   mathematical model or explicitly modeled primitives, never into AST constructors.
4. Simulate from garbage initial state before proving. Apply the generic simulation
   theorem and prove reset, one-step preservation, and observation agreement.
5. Emit through the proved emitter (`hdlean emit`). Tree circuits reach it via the
   proved `Circuit.toDag`; new designs should use the node-allocating `circuit do`.
6. If a challenge statement needs an implementation constant, add it to `holes` in
   `verification/frozen.json`; anything else it mentions belongs in a frozen interface.
7. Run `lake build`, `lake exe tests`, `python3 scripts/verify.py --backends`, and
   `python3 Tests/test_workflow.py`. Review the per-theorem axiom report.

Framework and trust-surface changes require a new candidate manifest:
`python3 scripts/freeze.py --write`. A reviewer should compare it with the prior
version and approve its digest outside the submission. Never edit the manifest
just to make an unexpected verification failure disappear.

`hw_step_kernel` uses simplification, arithmetic and kernel-checkable proof search.
`hw_step` also tries `bv_decide`, whose native-evaluation axioms the audit rejects.
Use `decide +kernel` only for small fixed facts; never reduce a whole concrete design.

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
