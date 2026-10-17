import Designs.SkidBuffer.Word

namespace HDLean.PipelineRtl.Challenge
open HDLean.Rtl HDLean.SkidBuffer.Word

/-- From any power-up store, after one reset cycle, every stage's ports follow
the reviewed network of three two-entry queues, for every positive payload
width. Implementation holes: `SkidBuffer.Word.design`, `SkidBuffer.Word.moore`. -/
theorem correctness (w : Nat) (hw : 0 < w) :
    RefinesAfterReset ((SkidBuffer.Word.design w).denote (SkidBuffer.Word.moore w hw)) (wordSpec w) (observe w) 1 :=
  SkidBuffer.Word.correct w hw

/-- Three stages of two payload words and a two-bit count each. -/
theorem budget (w : Nat) (hw : 0 < w) :
    Rtl.Blast.stateBits (SkidBuffer.Word.design w) (SkidBuffer.Word.design w).top ≤ 3 * (2 * w + 2) :=
  Nat.le_of_eq (SkidBuffer.Word.stateBits w hw)

end HDLean.PipelineRtl.Challenge
