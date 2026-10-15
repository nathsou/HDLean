import HDLean
import Designs
import Tests.Certificates
import Tests.Types
import Tests.Syntax
open Lean in
run_cmd do
  let names := #[
    ``HDLean.Machine.refines_of_simulation,
    ``HDLean.refinesAfterReset_of_simulation,
    ``HDLean.reset_noninterference,
    ``HDLean.lowerExpr_correct, ``HDLean.lower_next, ``HDLean.lower_output,
    ``HDLean.Backend.Graph.validate_sound,
    ``HDLean.Backend.Format.validates_sound, ``HDLean.Backend.Format.correct_of_validated,
    ``HDLean.RAMCircuit.hardware_correct, ``HDLean.RAMCircuit.decode_output,
    ``HDLean.Circuit.network_correct, ``HDLean.SkidBuffer.Challenge.correctness,
    ``HDLean.SkidBuffer.Challenge.budget,
    ``HDLean.WordExpr.selectBalanced_correct, ``HDLean.WordExpr.addWithCarry_correct, ``HDLean.WordExpr.addWithCarry_overflow,
    ``HDLean.WordExpr.sub_correct, ``HDLean.WordExpr.ult_correct, ``HDLean.WordExpr.equal_correct,
    ``HDLean.WordExpr.signExtend_correct, ``HDLean.WordExpr.setWidth_correct,
    ``HDLean.Tests.packet_roundtrip, ``HDLean.Tests.surfaceIncrement_correct,
    ``HDLean.compose_contracts, ``HDLean.network_refines,
    ``HDLean.SkidBuffer.pipeline_correct, ``HDLean.Netlist.optimize_correct, ``HDLean.retiresLike_of_simulation,
    ``HDLean.Fifo.Challenge.correctness, ``HDLean.Fifo.Challenge.budget,
    ``HDLean.Fifo.full_rate, ``HDLean.Counter.Challenge.correctness,
    ``HDLean.Counter.Challenge.budget, ``HDLean.Toy16.Challenge.correctness, ``HDLean.Toy16.Challenge.budget,
    ``HDLean.Toy16.Physical.decode_next, ``HDLean.Toy16.Physical.decode_output,
    ``HDLean.AsyncFifo.Physical.decode_next, ``HDLean.AsyncFifo.Physical.output_ready,
    ``HDLean.AsyncFifo.Physical.output_valid, ``HDLean.AsyncFifo.Physical.output_data,
    ``HDLean.AsyncFifo.Physical.hardware_preserves_queue, ``HDLean.AsyncFifo.Physical.storage_bits,
    ``HDLean.MultiClock.Graph.eval_correct, ``HDLean.MultiClock.Circuit.eventCircuit_correct,
    ``HDLean.MultiClock.Format.correct_of_validated,
    ``HDLean.AsyncFifo.ungray_gray, ``HDLean.AsyncFifo.step_refines_queue,
    ``HDLean.AsyncFifo.reset_establishes_queue, ``HDLean.AsyncFifo.reset_progress,
    ``HDLean.sync2_stable, ``HDLean.sample_adjacent, ``HDLean.gray_one_bit8, ``HDLean.one_bit_mix8,
    ``HDLean.one_bit_mix, ``HDLean.gray_adjacent, ``HDLean.gray_injective,
    ``HDLean.gray_increment_ne, ``HDLean.sample_gray_increment,
    ``HDLean.Tests.fifo1_graph, ``HDLean.Tests.counter_graph, ``HDLean.Tests.fifo8_graph]
  let mut reports := #[]
  for name in names do
    let axioms ← collectAxioms name
    reports := reports.push (Json.mkObj [("theorem", toJson name.toString),
      ("axioms", toJson (axioms.map Name.toString))])
  logInfo ("HDLEAN_AXIOMS=" ++ (Json.arr reports).compress)

