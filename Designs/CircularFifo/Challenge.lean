import Designs.Fifo.CircularWord

namespace HDLean.CircularFifo.Challenge
open HDLean.Rtl HDLean.Fifo.Word

/-- From any power-up store (memory contents included), after one reset cycle,
the general-depth FIFO follows the reviewed bounded queue of capacity `2^k`, for
every positive depth exponent and payload width. Implementation holes:
`Fifo.Circular.Word.design`, `Fifo.Circular.Word.moore`. -/
theorem correctness (k w : Nat) (hk : 0 < k) (hw : 0 < w) :
    RefinesAfterReset ((Fifo.Circular.Word.design k w).denote (Fifo.Circular.Word.moore k w hk hw))
      (queueSpec (2 ^ k) w) (observe w) 1 :=
  Fifo.Circular.Word.correct k w hk hw

/-- A `k`-bit head, a `k+1`-bit count and `2^k` payload words of memory. -/
theorem budget (k w : Nat) (hk : 0 < k) (hw : 0 < w) :
    Rtl.Blast.stateBits (Fifo.Circular.Word.design k w) (Fifo.Circular.Word.design k w).top ≤ 2 * k + 1 + 2 ^ k * w :=
  Nat.le_of_eq (Fifo.Circular.Word.stateBits k w hk hw)

end HDLean.CircularFifo.Challenge
