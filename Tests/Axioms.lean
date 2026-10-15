import HDLean
import Designs
import Tests.Certificates
open Lean in
run_cmd do
  let names := #[
    ``HDLean.Machine.refines_of_simulation,
    ``HDLean.refinesAfterReset_of_simulation,
    ``HDLean.reset_noninterference,
    ``HDLean.lowerExpr_correct, ``HDLean.lower_next, ``HDLean.lower_output,
    ``HDLean.Backend.Graph.validate_sound,
    ``HDLean.compose_contracts, ``HDLean.network_refines,
    ``HDLean.SkidBuffer.pipeline_correct, ``HDLean.Netlist.optimize_correct, ``HDLean.retiresLike_of_simulation,
    ``HDLean.Fifo.Challenge.correctness, ``HDLean.Fifo.Challenge.budget,
    ``HDLean.Fifo.full_rate, ``HDLean.Counter.Challenge.correctness,
    ``HDLean.Counter.Challenge.budget, ``HDLean.Toy16.Challenge.correctness,
    ``HDLean.sync2_stable, ``HDLean.sample_adjacent, ``HDLean.gray_one_bit8, ``HDLean.one_bit_mix8,
    ``HDLean.Tests.fifo1_graph, ``HDLean.Tests.counter_graph, ``HDLean.Tests.fifo8_graph]
  let mut reports := #[]
  for name in names do
    let axioms ← collectAxioms name
    reports := reports.push (Json.mkObj [("theorem", toJson name.toString),
      ("axioms", toJson (axioms.map Name.toString))])
  logInfo ("HDLEAN_AXIOMS=" ++ (Json.arr reports).compress)
