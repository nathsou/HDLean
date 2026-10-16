import Designs.Fifo.CircularHardware
namespace HDLean.Fifo.Circular.Challenge
/-- Frozen obligation; trace-level queue refinement is added in milestone R4. -/
theorem correctness :
∀ (k w : Nat)
  (s :
    Fin
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.Fifo.Circular.Physical.entries k)
          (HDLean.Fifo.Circular.Physical.bits k w)) →
      Bool)
  (xs :
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      Bool)
  (g : HDLean.Fifo.Circular.Ghost) (history : Nat → BitVec w),
  HDLean.Fifo.Circular.Ghost.Safe g
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
    @HDLean.Fifo.Circular.Ghost.Controls w k g (@HDLean.Fifo.Circular.Physical.decode k w s) →
      @HDLean.Fifo.Circular.Ghost.Memory w k g history (@HDLean.Fifo.Circular.Physical.decode k w s) →
        have input := HDLean.Fifo.Circular.Physical.decodeInput k w xs;
        have g' :=
          HDLean.Fifo.Circular.Ghost.advance g
            (@HDLean.Fifo.Circular.push w k (@HDLean.Fifo.Circular.Physical.decode k w s) input)
            (@HDLean.Fifo.Circular.pop w k (@HDLean.Fifo.Circular.Physical.decode k w s) input);
        And
          (HDLean.Fifo.Circular.Ghost.Safe g'
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
          (And
            (@HDLean.Fifo.Circular.Ghost.Controls w k g'
              (@HDLean.Fifo.Circular.Physical.decode k w
                (@HDLean.Circuit.next (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (HDLean.Fifo.Circular.Physical.entries k) (HDLean.Fifo.Circular.Physical.bits k w))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (HDLean.Fifo.Circular.Physical.hardware k w) s
                  (@Prod.mk.{0, 0}
                    (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                      Bool)
                    Bool xs Bool.false))))
            (And
              (@HDLean.Fifo.Circular.Ghost.Memory w k g'
                (@HDLean.Fifo.Circular.Ghost.record w k g history (@HDLean.Fifo.Circular.Physical.decode k w s) input)
                (@HDLean.Fifo.Circular.Physical.decode k w
                  (@HDLean.Circuit.next (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (HDLean.Fifo.Circular.Physical.entries k) (HDLean.Fifo.Circular.Physical.bits k w))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (HDLean.Fifo.Circular.Physical.hardware k w) s
                    (@Prod.mk.{0, 0}
                      (Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                        Bool)
                      Bool xs Bool.false))))
              (@Eq.{1} Bool (@HDLean.Fifo.Circular.pop w k (@HDLean.Fifo.Circular.Physical.decode k w s) input)
                  Bool.true →
                @Eq.{1} (BitVec w)
                  (@HDLean.Fifo.Circular.State.buffer w k (@HDLean.Fifo.Circular.Physical.decode k w s)
                    (@HDLean.Fifo.Circular.State.head w k (@HDLean.Fifo.Circular.Physical.decode k w s)))
                  (history (HDLean.Fifo.Circular.Ghost.read g))))) :=
  @HDLean.Fifo.Circular.Physical.hardware_preserves_queue
end HDLean.Fifo.Circular.Challenge
