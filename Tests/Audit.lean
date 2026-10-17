import HDLean
import Designs

/-!
Challenge audit, run by `scripts/verify.py`. For every theorem declared in a
`Designs.*.Challenge` module, plus the framework theorems listed below, it prints
the axioms the proof depends on and, for every constant in the theorem's
statement, the module that declares it. `verify.py` then requires only the three
standard axioms, and requires every statement constant to come from a frozen
module, from Lean itself, or from the manifest's list of implementation holes.
-/

open Lean Elab Command

/-- Generic framework results that no single challenge depends on. -/
def frameworkTheorems : List Name := [
  ``HDLean.Backend.Proved.emit_correct, ``HDLean.Dag.lower_correct, ``HDLean.Dag.lower_wellFormed,
  ``HDLean.refinesAfterReset_of_simulation, ``HDLean.refinesResetSchedule_of_simulation,
  ``HDLean.retiresLike_of_simulation, ``HDLean.compose_contracts, ``HDLean.reset_noninterference,
  ``HDLean.Dag.lowerTight_correct, ``HDLean.Dag.lowerTight_wellFormed,
  ``HDLean.Backend.Graph.optimize_eval, ``HDLean.Backend.Graph.optimize_wellFormed,
  ``HDLean.Dag.lowerOpt_correct, ``HDLean.Dag.lowerOpt_wellFormed,
  ``HDLean.Backend.Validate.check_sound, ``HDLean.Backend.Validate.select_eval,
  ``HDLean.Backend.Validate.select_wellFormed, ``HDLean.Backend.Proved.emitWith_correct,
  ``HDLean.Rtl.Design.optimize_sem, ``HDLean.Rtl.Design.compact_sem, ``HDLean.Rtl.Design.optimized_step, ``HDLean.Rtl.Design.optimized_output,
  ``HDLean.Optimized.toy16_correctness, ``HDLean.Optimized.ram_correctness,
  ``HDLean.Rtl.Design.toDag_nextState, ``HDLean.Rtl.Design.toDag_evalOutput,
  ``HDLean.Rtl.Design.parse_systemVerilog, ``HDLean.Rtl.Design.parseSystemVerilog_canonical,
  ``HDLean.Rtl.Design.parse_rtlil, ``HDLean.Rtl.Design.parseRTLIL_canonical,
  ``HDLean.Rtl.MDesign.parse_systemVerilog, ``HDLean.Rtl.MDesign.parse_rtlil,
  ``HDLean.Rtl.Blast.sem_reset, ``HDLean.Rtl.Build.mealy_build, ``HDLean.Rtl.Build.mealy_mem,
  ``HDLean.Rtl.Build.instantiate_ensures, ``HDLean.Rtl.Build.mealy_build_cells,
  ``HDLean.Rtl.mealy_stateBits, ``HDLean.Rtl.mealy_isMoore, ``HDLean.Rtl.mealy_step, ``HDLean.Rtl.mealy_output,
  ``HDLean.Rtl.mealy_sem_regs, ``HDLean.Rtl.mealy_sem_outputs, ``HDLean.Rtl.MDesign.regOut_of,
  ``HDLean.AsyncFifo.Word.decode_next, ``HDLean.Fifo.Circular.Word.decode_step]

run_cmd liftTermElabM do
  let env ← getEnv
  let moduleOf (n : Name) : String :=
    match env.getModuleIdxFor? n with
    | some idx => (env.allImportedModuleNames[idx.toNat]!).toString
    | none => ""
  let isChallenge (m : String) := m.startsWith "Designs." && m.endsWith ".Challenge"
  let mut names : Array Name := frameworkTheorems.toArray
  for (n, info) in env.constants.toList do
    if let .thmInfo _ := info then
      if isChallenge (moduleOf n) && !n.isInternal then names := names.push n
  let mut reports : Array Json := #[]
  for n in names do
    let info ← getConstInfo n
    let axioms ← collectAxioms n
    let used := info.type.getUsedConstants
    reports := reports.push (Json.mkObj [
      ("theorem", toJson n.toString), ("module", toJson (moduleOf n)),
      ("axioms", toJson (axioms.map Name.toString)),
      ("statement_constants", Json.arr (used.map fun c =>
        Json.mkObj [("name", toJson c.toString), ("module", toJson (moduleOf c))]))])
  logInfo ("HDLEAN_AUDIT=" ++ (Json.arr reports).compress)
