import Designs.Counter.Word

namespace HDLean.CounterRtl.Challenge
open HDLean.Rtl HDLean.Counter.Word

/-- From any power-up store, after one reset cycle, the output word follows the
decade counter. Implementation holes: `Counter.Word.design`, `Counter.Word.moore`. -/
theorem correctness : RefinesAfterReset (Counter.Word.design.denote Counter.Word.moore) wordSpec value 1 :=
  Counter.Word.correct

/-- Four state bits. -/
theorem budget : Rtl.Blast.stateBits Counter.Word.design Counter.Word.design.top = 4 :=
  Counter.Word.stateBits

end HDLean.CounterRtl.Challenge
