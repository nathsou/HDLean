import Designs.Fifo.Word

namespace HDLean.Fifo.Challenge
open HDLean.Rtl HDLean.Fifo.Word

/-- From any power-up store, after one reset cycle, the two-entry FIFO follows
the reviewed bounded queue of capacity two, for every positive payload width.
Implementation holes: `Fifo.Word.design`, `Fifo.Word.moore`. -/
theorem correctness (w : Nat) (hw : 0 < w) :
    RefinesAfterReset ((Fifo.Word.design w).denote (Fifo.Word.moore w hw)) (queueSpec 2 w) (observe w) 1 :=
  Fifo.Word.correct w hw

/-- Two payload words and a two-bit count. -/
theorem budget (w : Nat) (hw : 0 < w) : Rtl.Blast.stateBits (Fifo.Word.design w) (Fifo.Word.design w).top ≤ 2 * w + 2 :=
  Nat.le_of_eq (Fifo.Word.stateBits w hw)

end HDLean.Fifo.Challenge
