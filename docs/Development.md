# Extending HDLean

1. Write the reference model in `Spec.lean` and the ports, with how the reference
   reads them, in `Interface.lean` (typed records via `hdl_record`, decoded with
   `Bundle.decode`). Use `Option` for data that is invalid on some cycles.
2. State exact reset, refinement, progress and budget obligations in
   `Challenge.lean`. Specs and challenges remain review candidates until approved
   externally.
3. Write the design with the builder (`Ctx.mealy`, `mealy`, and the cell
   operations of `HDLean/Rtl/Build.lean`). Factor repeated structure into
   builder functions generic in the context (see `Fifo.Word.flags` and
   `Fifo.Word.advance`, used once by the FIFO and three times by the pipeline).
   Larger state composes records with `Both` and `Lanes`
   (`HDLean/Rtl/Named.lean`; the Euler solvers are examples); return the next
   state as `{ r with field := … }`, so that unmentioned registers hold. If
   `Ctx.module` comes out empty, `runE` says which cell or wiring the builder
   rejected; wrap parts of the program in `scope "name"` or `scope here%` to
   locate it.
4. Simulate from an all-zero and a random store before proving (`hdlean rtl-trace`,
   or a test in `Tests/Main.lean`).
5. Prove the body with `rtl_let` and the operator lemmas, giving the outputs and
   next registers as functions of the decoded records; `mealy_build` and the
   lemmas of `HDLean/Rtl/MealyDesign.lean` (`mealy_step`, `mealy_output`,
   `mealy_isMoore`, `mealy_stateBits`) turn that into facts about the design. Then
   apply the generic simulation theorem (`refinesAfterReset_of_simulation`) and
   prove reset, one-step preservation and observation agreement on the records.
   Outputs or memory addresses that must be registers (multi-clock crossings) use
   `mealy_build_cells`.
6. Emit with `hdlean rtl-emit` (word level) or `hdlean emit` (bit-blasted).
7. If a challenge statement needs an implementation constant, add it to `holes` in
   `verification/frozen.json`; anything else it mentions belongs in a frozen interface.
8. Run `lake build`, `lake exe tests` and `python3 scripts/verify.py --backends`.
   Review the per-theorem axiom report.

Framework and trust-surface changes require a new candidate manifest:
`python3 scripts/freeze.py --write`. A reviewer should compare it with the prior
version and approve its digest outside the submission. Never edit the manifest
just to make an unexpected verification failure disappear.

Use `decide` only for small fixed facts (a context's `ok` check); never reduce a
whole design. `bv_decide` and `native_decide` add axioms the audit rejects.

There are no imported solver services or external invariant results silently
trusted by the build.
