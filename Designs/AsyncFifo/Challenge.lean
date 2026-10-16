import Designs.AsyncFifo.Hardware
namespace HDLean.AsyncFifo.Challenge
/-- Frozen obligation; trace-level queue refinement is added in milestone R4. -/
theorem correctness :
∀ (k w : Nat)
  (s :
    Fin
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.AsyncFifo.Physical.entries k)
          (HDLean.AsyncFifo.Physical.bankWidth k w)) →
      Bool)
  (xs :
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w) →
      Bool)
  (rst : Bool) (edge : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Bool)
  (g : HDLean.AsyncFifo.Ghost) (history : Nat → BitVec w),
  HDLean.AsyncFifo.Ghost.Safe g
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
    @HDLean.AsyncFifo.Ghost.Controls k w g (HDLean.AsyncFifo.Physical.decode k w s) →
      @HDLean.AsyncFifo.Ghost.Memory k w g history (HDLean.AsyncFifo.Physical.decode k w s) →
        @Eq.{1} Bool
            (xs
              (@Fin.mk
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Decidable.byContradiction
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w))
                  (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w))
                  fun
                    (a :
                      Not
                        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w))) =>
                  HDLean.AsyncFifo.Physical.writeReset._proof_1 w a)))
            Bool.false →
          @Eq.{1} Bool
              (xs
                (@Fin.mk
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Decidable.byContradiction
                    (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w))
                    (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w))
                    fun
                      (a :
                        Not
                          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w))) =>
                    HDLean.AsyncFifo.Physical.readReset._proof_1 w a)))
              Bool.false →
            @Exists.{1} HDLean.AsyncFifo.Ghost fun (g' : HDLean.AsyncFifo.Ghost) =>
              And
                (HDLean.AsyncFifo.Ghost.Safe g'
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
                (And
                  (@HDLean.AsyncFifo.Ghost.Controls k w g'
                    (HDLean.AsyncFifo.Physical.decode k w
                      (@HDLean.MultiClock.Circuit.next (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (HDLean.AsyncFifo.Physical.entries k) (HDLean.AsyncFifo.Physical.bankWidth k w))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                        (HDLean.AsyncFifo.Physical.hardware k w) s
                        (@Prod.mk.{0, 0}
                          (Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w) →
                            Bool)
                          Bool xs rst)
                        edge)))
                  (@HDLean.AsyncFifo.Ghost.Memory k w g'
                    (@HDLean.AsyncFifo.Ghost.record k w g history (HDLean.AsyncFifo.Physical.decode k w s)
                      (HDLean.AsyncFifo.Physical.decodeInput k w xs edge))
                    (HDLean.AsyncFifo.Physical.decode k w
                      (@HDLean.MultiClock.Circuit.next (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (HDLean.AsyncFifo.Physical.entries k) (HDLean.AsyncFifo.Physical.bankWidth k w))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                        (HDLean.AsyncFifo.Physical.hardware k w) s
                        (@Prod.mk.{0, 0}
                          (Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w) →
                            Bool)
                          Bool xs rst)
                        edge)))) :=
  @HDLean.AsyncFifo.Physical.hardware_preserves_queue
end HDLean.AsyncFifo.Challenge
