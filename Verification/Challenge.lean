import HDLean
import Designs
import Tests.Certificates
import Tests.Types
import Tests.Syntax
import Tests.Invariant

/- Frozen literal statements. Changing an implementation theorem cannot change these obligations. -/
set_option linter.unusedVariables false
namespace HDLean.Review


/-- Frozen statement of `HDLean.AsyncFifo.Physical.decode_next`. -/
theorem AsyncFifo_Physical_decode_next :
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
  (rst : Bool) (edge : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Bool),
  @Eq.{1} (HDLean.AsyncFifo.State k w)
    (HDLean.AsyncFifo.Physical.decode k w
      (@HDLean.MultiClock.Circuit.next (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.AsyncFifo.Physical.entries k)
          (HDLean.AsyncFifo.Physical.bankWidth k w))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
        (HDLean.AsyncFifo.Physical.hardware k w) s
        (@Prod.mk.{0, 0}
          (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w) →
            Bool)
          Bool xs rst)
        edge))
    (@HDLean.AsyncFifo.next k w (HDLean.AsyncFifo.Physical.decode k w s)
      (HDLean.AsyncFifo.Physical.decodeInput k w xs edge)) :=
  @HDLean.AsyncFifo.Physical.decode_next

/-- Frozen statement of `HDLean.AsyncFifo.Physical.hardware_preserves_queue`. -/
theorem AsyncFifo_Physical_hardware_preserves_queue :
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

/-- Frozen statement of `HDLean.AsyncFifo.Physical.output_data`. -/
theorem AsyncFifo_Physical_output_data :
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
  (j : Fin w),
  @Eq.{1} Bool
    (@HDLean.MultiClock.Circuit.output (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.AsyncFifo.Physical.entries k)
        (HDLean.AsyncFifo.Physical.bankWidth k w))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
      (HDLean.AsyncFifo.Physical.hardware k w) s xs
      (@Fin.mk
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val w j))
        (@Decidable.byContradiction
          (@LT.lt.{0} Nat instLTNat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val w j))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w))
          (Nat.decLt
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val w j))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w))
          fun
            (a :
              Not
                (@LT.lt.{0} Nat instLTNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val w j))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w))) =>
          HDLean.AsyncFifo.Physical.output_data._proof_1 w j a)))
    (@BitVec.getLsbD w (@HDLean.AsyncFifo.data k w (HDLean.AsyncFifo.Physical.decode k w s)) (@Fin.val w j)) :=
  @HDLean.AsyncFifo.Physical.output_data

/-- Frozen statement of `HDLean.AsyncFifo.Physical.output_ready`. -/
theorem AsyncFifo_Physical_output_ready :
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
      Bool),
  @Eq.{1} Bool
    (@HDLean.MultiClock.Circuit.output (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.AsyncFifo.Physical.entries k)
        (HDLean.AsyncFifo.Physical.bankWidth k w))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
      (HDLean.AsyncFifo.Physical.hardware k w) s xs
      (@Fin.mk
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Decidable.byContradiction
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w))
          (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w))
          fun
            (a :
              Not
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w))) =>
          HDLean.AsyncFifo.Physical.output_ready._proof_1 w a)))
    (@HDLean.AsyncFifo.enqReady k w (HDLean.AsyncFifo.Physical.decode k w s)) :=
  @HDLean.AsyncFifo.Physical.output_ready

/-- Frozen statement of `HDLean.AsyncFifo.Physical.output_valid`. -/
theorem AsyncFifo_Physical_output_valid :
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
      Bool),
  @Eq.{1} Bool
    (@HDLean.MultiClock.Circuit.output (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.AsyncFifo.Physical.entries k)
        (HDLean.AsyncFifo.Physical.bankWidth k w))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
      (HDLean.AsyncFifo.Physical.hardware k w) s xs
      (@Fin.mk
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Decidable.byContradiction
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w))
          (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w))
          fun
            (a :
              Not
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w))) =>
          HDLean.AsyncFifo.Physical.output_valid._proof_1 w a)))
    (@HDLean.AsyncFifo.deqValid k w (HDLean.AsyncFifo.Physical.decode k w s)) :=
  @HDLean.AsyncFifo.Physical.output_valid

/-- Frozen statement of `HDLean.AsyncFifo.Physical.storage_bits`. -/
theorem AsyncFifo_Physical_storage_bits :
    ∀ (k w : Nat),
  @Eq.{1} Nat
    (@HDLean.Netlist.Module.ffBits (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.AsyncFifo.Physical.entries k)
        (HDLean.AsyncFifo.Physical.bankWidth k w))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
      (@HDLean.lower (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.AsyncFifo.Physical.entries k)
          (HDLean.AsyncFifo.Physical.bankWidth k w))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
        (@HDLean.MultiClock.Circuit.combinational (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) w)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.AsyncFifo.Physical.entries k)
            (HDLean.AsyncFifo.Physical.bankWidth k w))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
          (HDLean.AsyncFifo.Physical.hardware k w))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
      (@Max.max.{0} Nat Nat.instMax
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        w)) :=
  @HDLean.AsyncFifo.Physical.storage_bits

/-- Frozen statement of `HDLean.AsyncFifo.reset_establishes_queue`. -/
theorem AsyncFifo_reset_establishes_queue :
    ∀ {k w : Nat} {s : HDLean.AsyncFifo.State k w},
  @HDLean.AsyncFifo.ResetProgress k w Bool.true Bool.true s →
    ∀ (history : Nat → BitVec w),
      And
        (HDLean.AsyncFifo.Ghost.Safe HDLean.AsyncFifo.Ghost.empty
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
        (And (@HDLean.AsyncFifo.Ghost.Controls k w HDLean.AsyncFifo.Ghost.empty s)
          (@HDLean.AsyncFifo.Ghost.Memory k w HDLean.AsyncFifo.Ghost.empty history s)) :=
  @HDLean.AsyncFifo.reset_establishes_queue

/-- Frozen statement of `HDLean.AsyncFifo.reset_progress`. -/
theorem AsyncFifo_reset_progress :
    ∀ {k w : Nat} {s : HDLean.AsyncFifo.State k w} {i : HDLean.AsyncFifo.Input k w} {writeSeen readSeen : Bool},
  @HDLean.AsyncFifo.ResetProgress k w writeSeen readSeen s →
    @Eq.{1} Bool (@HDLean.AsyncFifo.Input.writeReset k w i) Bool.true →
      @Eq.{1} Bool (@HDLean.AsyncFifo.Input.readReset k w i) Bool.true →
        And
          (@HDLean.AsyncFifo.ResetProgress k w (Bool.or writeSeen (@HDLean.AsyncFifo.Input.writeEdge k w i))
            (Bool.or readSeen (@HDLean.AsyncFifo.Input.readEdge k w i)) (@HDLean.AsyncFifo.next k w s i))
          (@Eq.{1} (BitVec k → BitVec w) (@HDLean.AsyncFifo.State.memory k w (@HDLean.AsyncFifo.next k w s i))
            (@HDLean.AsyncFifo.State.memory k w s)) :=
  @HDLean.AsyncFifo.reset_progress

/-- Frozen statement of `HDLean.AsyncFifo.step_refines_queue`. -/
theorem AsyncFifo_step_refines_queue :
    ∀ {k w : Nat} {g : HDLean.AsyncFifo.Ghost} {s : HDLean.AsyncFifo.State k w} {i : HDLean.AsyncFifo.Input k w}
  {history : Nat → BitVec w},
  HDLean.AsyncFifo.Ghost.Safe g
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
    @HDLean.AsyncFifo.Ghost.Controls k w g s →
      @HDLean.AsyncFifo.Ghost.Memory k w g history s →
        @Eq.{1} Bool (@HDLean.AsyncFifo.Input.writeReset k w i) Bool.false →
          @Eq.{1} Bool (@HDLean.AsyncFifo.Input.readReset k w i) Bool.false →
            @Exists.{1} HDLean.AsyncFifo.Ghost fun (g' : HDLean.AsyncFifo.Ghost) =>
              And
                (HDLean.AsyncFifo.Ghost.Safe g'
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
                (And (@HDLean.AsyncFifo.Ghost.Controls k w g' (@HDLean.AsyncFifo.next k w s i))
                  (And
                    (@HDLean.AsyncFifo.Ghost.Memory k w g' (@HDLean.AsyncFifo.Ghost.record k w g history s i)
                      (@HDLean.AsyncFifo.next k w s i))
                    (And
                      (@Eq.{1} Nat (HDLean.AsyncFifo.Ghost.written g')
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (HDLean.AsyncFifo.Ghost.written g)
                          (@ite.{1} Nat (@Eq.{1} Bool (@HDLean.AsyncFifo.push k w s i) Bool.true)
                            (instDecidableEqBool (@HDLean.AsyncFifo.push k w s i) Bool.true)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                      (And
                        (@Eq.{1} Nat (HDLean.AsyncFifo.Ghost.read g')
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (HDLean.AsyncFifo.Ghost.read g)
                            (@ite.{1} Nat (@Eq.{1} Bool (@HDLean.AsyncFifo.pop k w s i) Bool.true)
                              (instDecidableEqBool (@HDLean.AsyncFifo.pop k w s i) Bool.true)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                        (@Eq.{1} Bool (@HDLean.AsyncFifo.pop k w s i) Bool.true →
                          @Eq.{1} (BitVec w) (@HDLean.AsyncFifo.data k w s)
                            (history (HDLean.AsyncFifo.Ghost.read g))))))) :=
  @HDLean.AsyncFifo.step_refines_queue

/-- Frozen statement of `HDLean.AsyncFifo.ungray_gray`. -/
theorem AsyncFifo_ungray_gray :
    ∀ {w : Nat} (x : BitVec w), @Eq.{1} (BitVec w) (@HDLean.AsyncFifo.ungray w (@HDLean.gray w x)) x :=
  @HDLean.AsyncFifo.ungray_gray

/-- Frozen statement of `HDLean.Backend.Format.correct_of_validated`. -/
theorem Backend_Format_correct_of_validated :
    ∀ {d i r o : Nat} (format : HDLean.Backend.Format) (text : String) (g : HDLean.Backend.Graph)
  (c : HDLean.Circuit d i r o),
  @HDLean.Backend.Graph.Equivalent d i r o g c →
    @Eq.{1} Bool (HDLean.Backend.Format.validates format text g) Bool.true →
      @HDLean.Backend.Format.Correct d i r o format text c :=
  @HDLean.Backend.Format.correct_of_validated

/-- Frozen statement of `HDLean.Backend.Format.validates_sound`. -/
theorem Backend_Format_validates_sound :
    ∀ (format : HDLean.Backend.Format) (text : String) (g : HDLean.Backend.Graph),
  @Eq.{1} Bool (HDLean.Backend.Format.validates format text g) Bool.true →
    ∀ (inputs state : Array.{0} Bool),
      @Eq.{1} (Option.{0} (Prod.{0, 0} (Array.{0} Bool) (Array.{0} Bool)))
        (HDLean.Backend.Format.meaning format text inputs state)
        (@Option.some.{0} (Prod.{0, 0} (Array.{0} Bool) (Array.{0} Bool)) (HDLean.Backend.Graph.eval g inputs state)) :=
  @HDLean.Backend.Format.validates_sound

/-- Frozen statement of `HDLean.Backend.Graph.validateLocal_sound`. -/
theorem Backend_Graph_validateLocal_sound :
    ∀ {d i r o : Nat} (g : HDLean.Backend.Graph) (c : HDLean.Circuit d i r o)
  (hint : optParam.{1} (HDLean.Expr d i r → Nat) (@HDLean.Backend.Local.pointerHint i r d)),
  @Eq.{1} Bool (@HDLean.Backend.Graph.validateLocal d i r o g c hint) Bool.true →
    @HDLean.Backend.Graph.Equivalent d i r o g c :=
  @HDLean.Backend.Graph.validateLocal_sound

/-- Frozen statement of `HDLean.Backend.Graph.validate_sound`. -/
theorem Backend_Graph_validate_sound :
    ∀ {d i r o : Nat} (g : HDLean.Backend.Graph) (c : HDLean.Circuit d i r o),
  @Eq.{1} Bool (@HDLean.Backend.Graph.validate d i r o g c) Bool.true → @HDLean.Backend.Graph.Equivalent d i r o g c :=
  @HDLean.Backend.Graph.validate_sound

/-- Frozen statement of `HDLean.Circuit.network_correct`. -/
theorem Circuit_network_correct :
    ∀ {count d i r o external : Nat} (ms : Fin count → HDLean.Circuit d i r o)
  (hm : ∀ (j : Fin count), @HDLean.Circuit.IsMoore d i r o (ms j))
  (wire : Fin count → Fin i → HDLean.Circuit.Connection external count o)
  (state₀ : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) count r) → Bool)
  (xs : Nat → Prod.{0, 0} (Fin external → Bool) Bool) (t : Nat),
  @Eq.{1} (Fin count → Fin o → Bool)
    (@HDLean.Circuit.unpack count o
      (@HDLean.PMachine.runFrom (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) count r) → Bool)
        (Prod.{0, 0} (Fin external → Bool) Bool)
        (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) count o) → Bool)
        (@HDLean.Circuit.denote d external (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) count r)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) count o)
          (@HDLean.Circuit.network count d i r o external ms hm wire)
          (@HDLean.Circuit.network_isMoore count d i r o external ms hm wire))
        state₀ xs t))
    (@HDLean.PMachine.runFrom (Fin count → Fin r → Bool) (Prod.{0, 0} (Fin external → Bool) Bool)
      (Fin count → Fin o → Bool) (@HDLean.Circuit.networkModel count d i r o external ms wire)
      (@HDLean.Circuit.unpack count r state₀) xs t) :=
  @HDLean.Circuit.network_correct

/-- Frozen statement of `HDLean.Counter.Challenge.budget`. -/
theorem Counter_Challenge_budget :
    @Eq.{1} Nat
  (@HDLean.Netlist.Module.ffBits (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@HDLean.lower (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) HDLean.Counter.hardware))
  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) :=
  @HDLean.Counter.Challenge.budget

/-- Frozen statement of `HDLean.Counter.Challenge.correctness`. -/
theorem Counter_Challenge_correctness :
    @HDLean.RefinesAfterReset (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Bool)
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Bool)
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Bool) Nat Nat
  (@HDLean.Circuit.denote (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) HDLean.Counter.hardware HDLean.Counter.moore)
  HDLean.Counter.wireSpec HDLean.Counter.value (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) :=
  @HDLean.Counter.Challenge.correctness

/-- Frozen statement of `HDLean.Counter.reset_schedule`. -/
theorem Counter_reset_schedule :
    @HDLean.RefinesResetSchedule (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Bool)
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Bool)
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Bool) Nat Nat
  (@HDLean.Circuit.denote (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) HDLean.Counter.hardware HDLean.Counter.moore)
  HDLean.Counter.wireSpec HDLean.Counter.value :=
  @HDLean.Counter.reset_schedule

/-- Frozen statement of `HDLean.Delay.latency`. -/
theorem Delay_latency :
    ∀ (stages width : Nat)
  (initial : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stages width) → Bool)
  (xs : Nat → BitVec width) (t : Nat),
  @Eq.{1} (BitVec width)
    (HDLean.Delay.observe stages width initial xs
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t stages))
    (xs t) :=
  @HDLean.Delay.latency

/-- Frozen statement of `HDLean.Delay.realizes_pipe`. -/
theorem Delay_realizes_pipe :
    ∀ (stages width : Nat)
  (initial : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stages width) → Bool)
  (startup xs : Nat → BitVec width) (t : Nat),
  @Eq.{1} (BitVec width)
    (HDLean.Delay.observe stages width initial xs
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t stages))
    (@HDLean.Pipe.run
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) stages)
      (BitVec width) (BitVec width)
      (@HDLean.Pipe.delay (BitVec width) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (BitVec width)
        stages startup (@HDLean.Pipe.comb (BitVec width) (BitVec width) (@id.{1} (BitVec width))))
      xs (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t stages)) :=
  @HDLean.Delay.realizes_pipe

/-- Frozen statement of `HDLean.Delay.retime`. -/
theorem Delay_retime :
    ∀ {width outWidth : Nat} (f : BitVec width → BitVec outWidth) (stages : Nat)
  (left : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stages width) → Bool)
  (right : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stages outWidth) → Bool)
  (xs : Nat → BitVec width) (t : Nat),
  @Eq.{1} (BitVec outWidth)
    (f
      (HDLean.Delay.observe stages width left xs
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t stages)))
    (HDLean.Delay.observe stages outWidth right (fun (u : Nat) => f (xs u))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t stages)) :=
  @HDLean.Delay.retime

/-- Frozen statement of `HDLean.Fifo.Challenge.budget`. -/
theorem Fifo_Challenge_budget :
    ∀ (w : Nat),
  @LE.le.{0} Nat instLENat
    (@HDLean.Netlist.Module.ffBits (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HDLean.lower (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (HDLean.Fifo.hardware w)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) :=
  @HDLean.Fifo.Challenge.budget

/-- Frozen statement of `HDLean.Fifo.Challenge.correctness`. -/
theorem Fifo_Challenge_correctness :
    ∀ (w : Nat),
  @HDLean.RefinesAfterReset
    (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      Bool)
    (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      Bool)
    (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      Bool)
    (List.{0} (Vector.{0} Bool w)) (HDLean.Fifo.Output (Vector.{0} Bool w))
    (@HDLean.Circuit.denote (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (HDLean.Fifo.hardware w) (HDLean.Fifo.hardware_moore w))
    (HDLean.Fifo.wireSpec w) (@HDLean.Fifo.observe w) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) :=
  @HDLean.Fifo.Challenge.correctness

/-- Frozen statement of `HDLean.Fifo.Circular.Physical.decode_next`. -/
theorem Fifo_Circular_Physical_decode_next :
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
  (rst : Bool),
  @Eq.{1} (HDLean.Fifo.Circular.State w k)
    (@HDLean.Fifo.Circular.Physical.decode k w
      (@HDLean.Circuit.next (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.Fifo.Circular.Physical.entries k)
          (HDLean.Fifo.Circular.Physical.bits k w))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (HDLean.Fifo.Circular.Physical.hardware k w) s
        (@Prod.mk.{0, 0}
          (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
            Bool)
          Bool xs rst)))
    (@HDLean.PMachine.next (HDLean.Fifo.Circular.State w k) (Prod.{0, 0} (HDLean.Fifo.Input (BitVec w)) Bool)
      (HDLean.Fifo.Output (BitVec w)) (HDLean.Fifo.Circular.machine w k) (@HDLean.Fifo.Circular.Physical.decode k w s)
      (@Prod.mk.{0, 0} (HDLean.Fifo.Input (BitVec w)) Bool (HDLean.Fifo.Circular.Physical.decodeInput k w xs) rst)) :=
  @HDLean.Fifo.Circular.Physical.decode_next

/-- Frozen statement of `HDLean.Fifo.Circular.Physical.decode_output`. -/
theorem Fifo_Circular_Physical_decode_output :
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
      Bool),
  @Eq.{1} (HDLean.Fifo.Output (BitVec w))
    (@HDLean.Fifo.Circular.Physical.observe w
      (@HDLean.Circuit.evalOutput (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.Fifo.Circular.Physical.entries k)
          (HDLean.Fifo.Circular.Physical.bits k w))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (HDLean.Fifo.Circular.Physical.hardware k w) s xs))
    (@HDLean.PMachine.out (HDLean.Fifo.Circular.State w k) (Prod.{0, 0} (HDLean.Fifo.Input (BitVec w)) Bool)
      (HDLean.Fifo.Output (BitVec w)) (HDLean.Fifo.Circular.machine w k) (@HDLean.Fifo.Circular.Physical.decode k w s)) :=
  @HDLean.Fifo.Circular.Physical.decode_output

/-- Frozen statement of `HDLean.Fifo.Circular.Physical.hardware_preserves_queue`. -/
theorem Fifo_Circular_Physical_hardware_preserves_queue :
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

/-- Frozen statement of `HDLean.Fifo.Circular.Physical.storage_bits`. -/
theorem Fifo_Circular_Physical_storage_bits :
    ∀ (k w : Nat),
  @Eq.{1} Nat
    (@HDLean.Netlist.Module.ffBits (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.Fifo.Circular.Physical.entries k)
        (HDLean.Fifo.Circular.Physical.bits k w))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HDLean.lower (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (HDLean.Fifo.Circular.Physical.entries k)
          (HDLean.Fifo.Circular.Physical.bits k w))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (HDLean.Fifo.Circular.Physical.hardware k w)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
      (@Max.max.{0} Nat Nat.instMax
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        w)) :=
  @HDLean.Fifo.Circular.Physical.storage_bits

/-- Frozen statement of `HDLean.Fifo.Circular.reset_establishes_queue`. -/
theorem Fifo_Circular_reset_establishes_queue :
    ∀ {w k : Nat} (s : HDLean.Fifo.Circular.State w k) (i : HDLean.Fifo.Input (BitVec w)) (history : Nat → BitVec w),
  have zero :=
    HDLean.Fifo.Circular.Ghost.mk (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
  And
    (HDLean.Fifo.Circular.Ghost.Safe zero
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
    (And
      (@HDLean.Fifo.Circular.Ghost.Controls w k zero
        (@HDLean.PMachine.next (HDLean.Fifo.Circular.State w k) (Prod.{0, 0} (HDLean.Fifo.Input (BitVec w)) Bool)
          (HDLean.Fifo.Output (BitVec w)) (HDLean.Fifo.Circular.machine w k) s
          (@Prod.mk.{0, 0} (HDLean.Fifo.Input (BitVec w)) Bool i Bool.true)))
      (@HDLean.Fifo.Circular.Ghost.Memory w k zero history
        (@HDLean.PMachine.next (HDLean.Fifo.Circular.State w k) (Prod.{0, 0} (HDLean.Fifo.Input (BitVec w)) Bool)
          (HDLean.Fifo.Output (BitVec w)) (HDLean.Fifo.Circular.machine w k) s
          (@Prod.mk.{0, 0} (HDLean.Fifo.Input (BitVec w)) Bool i Bool.true)))) :=
  @HDLean.Fifo.Circular.reset_establishes_queue

/-- Frozen statement of `HDLean.Fifo.Circular.step_refines_queue`. -/
theorem Fifo_Circular_step_refines_queue :
    ∀ {w k : Nat} {g : HDLean.Fifo.Circular.Ghost} {s : HDLean.Fifo.Circular.State w k} {i : HDLean.Fifo.Input (BitVec w)}
  {history : Nat → BitVec w},
  HDLean.Fifo.Circular.Ghost.Safe g
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
    @HDLean.Fifo.Circular.Ghost.Controls w k g s →
      @HDLean.Fifo.Circular.Ghost.Memory w k g history s →
        have g' :=
          HDLean.Fifo.Circular.Ghost.advance g (@HDLean.Fifo.Circular.push w k s i) (@HDLean.Fifo.Circular.pop w k s i);
        And
          (HDLean.Fifo.Circular.Ghost.Safe g'
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
          (And
            (@HDLean.Fifo.Circular.Ghost.Controls w k g'
              (@HDLean.PMachine.next (HDLean.Fifo.Circular.State w k) (Prod.{0, 0} (HDLean.Fifo.Input (BitVec w)) Bool)
                (HDLean.Fifo.Output (BitVec w)) (HDLean.Fifo.Circular.machine w k) s
                (@Prod.mk.{0, 0} (HDLean.Fifo.Input (BitVec w)) Bool i Bool.false)))
            (And
              (@HDLean.Fifo.Circular.Ghost.Memory w k g' (@HDLean.Fifo.Circular.Ghost.record w k g history s i)
                (@HDLean.PMachine.next (HDLean.Fifo.Circular.State w k)
                  (Prod.{0, 0} (HDLean.Fifo.Input (BitVec w)) Bool) (HDLean.Fifo.Output (BitVec w))
                  (HDLean.Fifo.Circular.machine w k) s
                  (@Prod.mk.{0, 0} (HDLean.Fifo.Input (BitVec w)) Bool i Bool.false)))
              (@Eq.{1} Bool (@HDLean.Fifo.Circular.pop w k s i) Bool.true →
                @Eq.{1} (BitVec w) (@HDLean.Fifo.Circular.State.buffer w k s (@HDLean.Fifo.Circular.State.head w k s))
                  (history (HDLean.Fifo.Circular.Ghost.read g))))) :=
  @HDLean.Fifo.Circular.step_refines_queue

/-- Frozen statement of `HDLean.Fifo.full_rate`. -/
theorem Fifo_full_rate :
    ∀ {α : Type} (cap : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) cap →
    ∀ (xs : Nat → HDLean.Fifo.Input α),
      (∀ (t : Nat), @Eq.{1} Bool (@HDLean.Fifo.Input.deqReady α (xs t)) Bool.true) →
        ∀ (t : Nat),
          @Eq.{1} Bool
            (@HDLean.Fifo.Output.enqReady α
              (@HDLean.Machine.run (List.{0} α) (HDLean.Fifo.Input α) (HDLean.Fifo.Output α) (HDLean.Fifo.spec α cap) xs
                t))
            Bool.true :=
  @HDLean.Fifo.full_rate

/-- Frozen statement of `HDLean.Fifo.hardware_reset_schedule`. -/
theorem Fifo_hardware_reset_schedule :
    ∀ (w : Nat),
  @HDLean.RefinesResetSchedule
    (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      Bool)
    (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      Bool)
    (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      Bool)
    (List.{0} (Vector.{0} Bool w)) (HDLean.Fifo.Output (Vector.{0} Bool w))
    (@HDLean.Circuit.denote (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (HDLean.Fifo.hardware w) (HDLean.Fifo.hardware_moore w))
    (HDLean.Fifo.wireSpec w) (@HDLean.Fifo.observe w) :=
  @HDLean.Fifo.hardware_reset_schedule

/-- Frozen statement of `HDLean.Machine.refines_of_simulation`. -/
theorem Machine_refines_of_simulation :
    ∀ {σ ι ο τ π : Type} (impl : HDLean.Machine σ ι ο) (spec : HDLean.Machine τ ι π) (obs : ο → π) (R : σ → τ → Prop),
  R (@HDLean.Machine.init σ ι ο impl) (@HDLean.Machine.init τ ι π spec) →
    (∀ (s : σ) (q : τ) (i : ι), R s q → R (@HDLean.Machine.next σ ι ο impl s i) (@HDLean.Machine.next τ ι π spec q i)) →
      (∀ (s : σ) (q : τ),
          R s q → @Eq.{1} π (obs (@HDLean.Machine.out σ ι ο impl s)) (@HDLean.Machine.out τ ι π spec q)) →
        @HDLean.Refines σ ι ο τ π impl spec obs :=
  @HDLean.Machine.refines_of_simulation

/-- Frozen statement of `HDLean.MultiClock.Circuit.eventCircuit_correct`. -/
theorem MultiClock_Circuit_eventCircuit_correct :
    ∀ {nd i r o : Nat} (c : HDLean.MultiClock.Circuit nd i r o) (s : Fin r → Bool) (xs : Fin i → Bool) (rst : Bool)
  (edge : Fin nd → Bool) (unusedReset : Bool),
  And
    (@Eq.{1} (Fin r → Bool)
      (@HDLean.Circuit.next (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          nd)
        r o (@HDLean.MultiClock.Circuit.eventCircuit nd i r o c) s
        (@Prod.mk.{0, 0}
          (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                nd) →
            Bool)
          Bool (@HDLean.MultiClock.Circuit.eventInputs nd i xs rst edge) unusedReset))
      (@HDLean.MultiClock.Circuit.next nd i r o c s (@Prod.mk.{0, 0} (Fin i → Bool) Bool xs rst) edge))
    (@Eq.{1} (Fin o → Bool)
      (@HDLean.Circuit.evalOutput (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          nd)
        r o (@HDLean.MultiClock.Circuit.eventCircuit nd i r o c) s
        (@HDLean.MultiClock.Circuit.eventInputs nd i xs rst edge))
      (@HDLean.MultiClock.Circuit.output nd i r o c s xs)) :=
  @HDLean.MultiClock.Circuit.eventCircuit_correct

/-- Frozen statement of `HDLean.MultiClock.Format.correct_of_validated`. -/
theorem MultiClock_Format_correct_of_validated :
    ∀ {nd i r o : Nat} (f : HDLean.MultiClock.Format) (text : String) (g : HDLean.MultiClock.Graph)
  (c : HDLean.MultiClock.Circuit nd i r o),
  @HDLean.MultiClock.Graph.Equivalent nd i r o g c →
    @Eq.{1} Bool (HDLean.MultiClock.Format.validates f text g) Bool.true →
      ∀ (xs : Vector.{0} Bool i) (s : Vector.{0} Bool r) (rst : Bool) (edge : Nat → Bool),
        @Eq.{1} (Option.{0} (Prod.{0, 0} (Array.{0} Bool) (Array.{0} Bool)))
          (HDLean.MultiClock.Format.meaning f text edge (@Array.push.{0} Bool (@Vector.toArray.{0} Bool i xs) rst)
            (@Vector.toArray.{0} Bool r s))
          (@Option.some.{0} (Prod.{0, 0} (Array.{0} Bool) (Array.{0} Bool))
            (@Prod.mk.{0, 0} (Array.{0} Bool) (Array.{0} Bool)
              (@Vector.toArray.{0} Bool r
                (@Vector.ofFn.{0} r Bool
                  (@HDLean.MultiClock.Circuit.next nd i r o c
                    (fun (k : Fin r) =>
                      @GetElem.getElem.{0, 0, 0} (Vector.{0} Bool r) (Fin r) Bool
                        (fun (xs : Vector.{0} Bool r) (i : Fin r) => @LT.lt.{0} Nat instLTNat (@Fin.val r i) r)
                        (@Fin.instGetElemFinVal.{0, 0} (Vector.{0} Bool r) Bool
                          (fun (x : Vector.{0} Bool r) (i : Nat) => @LT.lt.{0} Nat instLTNat i r) r
                          (@Vector.instGetElemNatLt.{0} Bool r))
                        s k
                        (@Decidable.byContradiction (@LT.lt.{0} Nat instLTNat (@Fin.val r k) r)
                          (Nat.decLt (@Fin.val r k) r) fun (a : Not (@LT.lt.{0} Nat instLTNat (@Fin.val r k) r)) =>
                          @HDLean.MultiClock.Format.correct_of_validated._proof_1 r k a))
                    (@Prod.mk.{0, 0} (Fin i → Bool) Bool
                      (fun (k : Fin i) =>
                        @GetElem.getElem.{0, 0, 0} (Vector.{0} Bool i) (Fin i) Bool
                          (fun (xs : Vector.{0} Bool i) (i_1 : Fin i) => @LT.lt.{0} Nat instLTNat (@Fin.val i i_1) i)
                          (@Fin.instGetElemFinVal.{0, 0} (Vector.{0} Bool i) Bool
                            (fun (x : Vector.{0} Bool i) (i_1 : Nat) => @LT.lt.{0} Nat instLTNat i_1 i) i
                            (@Vector.instGetElemNatLt.{0} Bool i))
                          xs k
                          (@Decidable.byContradiction (@LT.lt.{0} Nat instLTNat (@Fin.val i k) i)
                            (Nat.decLt (@Fin.val i k) i) fun (a : Not (@LT.lt.{0} Nat instLTNat (@Fin.val i k) i)) =>
                            @HDLean.MultiClock.Format.correct_of_validated._proof_1 i k a))
                      rst)
                    fun (d : Fin nd) => edge (@Fin.val nd d))))
              (@Vector.toArray.{0} Bool o
                (@Vector.ofFn.{0} o Bool
                  (@HDLean.MultiClock.Circuit.output nd i r o c
                    (fun (k : Fin r) =>
                      @GetElem.getElem.{0, 0, 0} (Vector.{0} Bool r) (Fin r) Bool
                        (fun (xs : Vector.{0} Bool r) (i : Fin r) => @LT.lt.{0} Nat instLTNat (@Fin.val r i) r)
                        (@Fin.instGetElemFinVal.{0, 0} (Vector.{0} Bool r) Bool
                          (fun (x : Vector.{0} Bool r) (i : Nat) => @LT.lt.{0} Nat instLTNat i r) r
                          (@Vector.instGetElemNatLt.{0} Bool r))
                        s k
                        (@Decidable.byContradiction (@LT.lt.{0} Nat instLTNat (@Fin.val r k) r)
                          (Nat.decLt (@Fin.val r k) r) fun (a : Not (@LT.lt.{0} Nat instLTNat (@Fin.val r k) r)) =>
                          @HDLean.MultiClock.Format.correct_of_validated._proof_1 r k a))
                    fun (k : Fin i) =>
                    @GetElem.getElem.{0, 0, 0} (Vector.{0} Bool i) (Fin i) Bool
                      (fun (xs : Vector.{0} Bool i) (i_1 : Fin i) => @LT.lt.{0} Nat instLTNat (@Fin.val i i_1) i)
                      (@Fin.instGetElemFinVal.{0, 0} (Vector.{0} Bool i) Bool
                        (fun (x : Vector.{0} Bool i) (i_1 : Nat) => @LT.lt.{0} Nat instLTNat i_1 i) i
                        (@Vector.instGetElemNatLt.{0} Bool i))
                      xs k
                      (@Decidable.byContradiction (@LT.lt.{0} Nat instLTNat (@Fin.val i k) i)
                        (Nat.decLt (@Fin.val i k) i) fun (a : Not (@LT.lt.{0} Nat instLTNat (@Fin.val i k) i)) =>
                        @HDLean.MultiClock.Format.correct_of_validated._proof_1 i k a)))))) :=
  @HDLean.MultiClock.Format.correct_of_validated

/-- Frozen statement of `HDLean.MultiClock.Graph.eval_correct`. -/
theorem MultiClock_Graph_eval_correct :
    ∀ {nd i r o : Nat} {g : HDLean.MultiClock.Graph} {c : HDLean.MultiClock.Circuit nd i r o},
  @HDLean.MultiClock.Graph.Equivalent nd i r o g c →
    ∀ (xs : Vector.{0} Bool i) (s : Vector.{0} Bool r) (rst : Bool) (edge : Nat → Bool),
      @Eq.{1} (Prod.{0, 0} (Array.{0} Bool) (Array.{0} Bool))
        (HDLean.MultiClock.Graph.eval g edge (@Array.push.{0} Bool (@Vector.toArray.{0} Bool i xs) rst)
          (@Vector.toArray.{0} Bool r s))
        (@Prod.mk.{0, 0} (Array.{0} Bool) (Array.{0} Bool)
          (@Vector.toArray.{0} Bool r
            (@Vector.ofFn.{0} r Bool
              (@HDLean.MultiClock.Circuit.next nd i r o c
                (fun (k : Fin r) =>
                  @GetElem.getElem.{0, 0, 0} (Vector.{0} Bool r) (Fin r) Bool
                    (fun (xs : Vector.{0} Bool r) (i : Fin r) => @LT.lt.{0} Nat instLTNat (@Fin.val r i) r)
                    (@Fin.instGetElemFinVal.{0, 0} (Vector.{0} Bool r) Bool
                      (fun (x : Vector.{0} Bool r) (i : Nat) => @LT.lt.{0} Nat instLTNat i r) r
                      (@Vector.instGetElemNatLt.{0} Bool r))
                    s k
                    (@Decidable.byContradiction (@LT.lt.{0} Nat instLTNat (@Fin.val r k) r) (Nat.decLt (@Fin.val r k) r)
                      fun (a : Not (@LT.lt.{0} Nat instLTNat (@Fin.val r k) r)) =>
                      @HDLean.MultiClock.Graph.eval_correct._proof_1 r k a))
                (@Prod.mk.{0, 0} (Fin i → Bool) Bool
                  (fun (k : Fin i) =>
                    @GetElem.getElem.{0, 0, 0} (Vector.{0} Bool i) (Fin i) Bool
                      (fun (xs : Vector.{0} Bool i) (i_1 : Fin i) => @LT.lt.{0} Nat instLTNat (@Fin.val i i_1) i)
                      (@Fin.instGetElemFinVal.{0, 0} (Vector.{0} Bool i) Bool
                        (fun (x : Vector.{0} Bool i) (i_1 : Nat) => @LT.lt.{0} Nat instLTNat i_1 i) i
                        (@Vector.instGetElemNatLt.{0} Bool i))
                      xs k
                      (@Decidable.byContradiction (@LT.lt.{0} Nat instLTNat (@Fin.val i k) i)
                        (Nat.decLt (@Fin.val i k) i) fun (a : Not (@LT.lt.{0} Nat instLTNat (@Fin.val i k) i)) =>
                        @HDLean.MultiClock.Graph.eval_correct._proof_1 i k a))
                  rst)
                fun (d : Fin nd) => edge (@Fin.val nd d))))
          (@Vector.toArray.{0} Bool o
            (@Vector.ofFn.{0} o Bool
              (@HDLean.MultiClock.Circuit.output nd i r o c
                (fun (k : Fin r) =>
                  @GetElem.getElem.{0, 0, 0} (Vector.{0} Bool r) (Fin r) Bool
                    (fun (xs : Vector.{0} Bool r) (i : Fin r) => @LT.lt.{0} Nat instLTNat (@Fin.val r i) r)
                    (@Fin.instGetElemFinVal.{0, 0} (Vector.{0} Bool r) Bool
                      (fun (x : Vector.{0} Bool r) (i : Nat) => @LT.lt.{0} Nat instLTNat i r) r
                      (@Vector.instGetElemNatLt.{0} Bool r))
                    s k
                    (@Decidable.byContradiction (@LT.lt.{0} Nat instLTNat (@Fin.val r k) r) (Nat.decLt (@Fin.val r k) r)
                      fun (a : Not (@LT.lt.{0} Nat instLTNat (@Fin.val r k) r)) =>
                      @HDLean.MultiClock.Graph.eval_correct._proof_1 r k a))
                fun (k : Fin i) =>
                @GetElem.getElem.{0, 0, 0} (Vector.{0} Bool i) (Fin i) Bool
                  (fun (xs : Vector.{0} Bool i) (i_1 : Fin i) => @LT.lt.{0} Nat instLTNat (@Fin.val i i_1) i)
                  (@Fin.instGetElemFinVal.{0, 0} (Vector.{0} Bool i) Bool
                    (fun (x : Vector.{0} Bool i) (i_1 : Nat) => @LT.lt.{0} Nat instLTNat i_1 i) i
                    (@Vector.instGetElemNatLt.{0} Bool i))
                  xs k
                  (@Decidable.byContradiction (@LT.lt.{0} Nat instLTNat (@Fin.val i k) i) (Nat.decLt (@Fin.val i k) i)
                    fun (a : Not (@LT.lt.{0} Nat instLTNat (@Fin.val i k) i)) =>
                    @HDLean.MultiClock.Graph.eval_correct._proof_1 i k a))))) :=
  @HDLean.MultiClock.Graph.eval_correct

/-- Frozen statement of `HDLean.Netlist.optimize_correct`. -/
theorem Netlist_optimize_correct :
    ∀ {d i r : Nat} (a : HDLean.Netlist.Node d i r) (xs : Fin i → Bool) (s : Fin r → Bool),
  @Eq.{1} Bool (@HDLean.Netlist.Node.eval i r d xs s (@HDLean.Netlist.optimize d i r a))
    (@HDLean.Netlist.Node.eval i r d xs s a) :=
  @HDLean.Netlist.optimize_correct

/-- Frozen statement of `HDLean.RAMCircuit.decode_output`. -/
theorem RAMCircuit_decode_output :
    ∀ (a w : Nat)
  (s :
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
            w)
          w) →
      Bool)
  (xs :
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
          w) →
      Bool),
  @Eq.{1} (BitVec w)
    (@HDLean.WordExpr.eval (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) w
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) w
      (@HDLean.WordExpr.inputs w w (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Decidable.byContradiction
          (@LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) w)
            w)
          (Nat.decLe
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) w)
            w)
          fun
            (a :
              Not
                (@LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) w)
                  w)) =>
          HDLean.RAMCircuit.decode_output._proof_3 w a))
      (@HDLean.Circuit.evalOutput (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
          w)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
            w)
          w)
        w (HDLean.RAMCircuit.hardware a w) s xs)
      fun (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) =>
      HDLean.RAMCircuit.decode_output.match_1.{1}
        (fun (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) => Bool) k)
    (@HDLean.RAMState.readData
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
      w (@HDLean.RAMCircuit.decode a w s)) :=
  @HDLean.RAMCircuit.decode_output

/-- Frozen statement of `HDLean.RAMCircuit.hardware_correct`. -/
theorem RAMCircuit_hardware_correct :
    ∀ (a w : Nat)
  (s₀ :
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
            w)
          w) →
      Bool)
  (xs :
    Nat →
      Prod.{0, 0}
        (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
              w) →
          Bool)
        Bool)
  (t : Nat),
  @Eq.{1}
    (HDLean.RAMState
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
      w)
    (@HDLean.RAMCircuit.decode a w
      (@HDLean.PMachine.stateFrom
        (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                w)
              w) →
          Bool)
        (Prod.{0, 0}
          (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
                w) →
            Bool)
          Bool)
        (Fin w → Bool)
        (@HDLean.Circuit.denote (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
            w)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
              w)
            w)
          w (HDLean.RAMCircuit.hardware a w) (HDLean.RAMCircuit.hardware_moore a w))
        s₀ xs t))
    (@HDLean.PMachine.stateFrom
      (HDLean.RAMState
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
        w)
      (HDLean.RAMRequest
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
        w)
      (BitVec w)
      (HDLean.ram
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
        w)
      (@HDLean.RAMCircuit.decode a w s₀)
      (fun (n : Nat) =>
        HDLean.RAMCircuit.decodeInput a w
          (@Prod.fst.{0, 0}
            (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
                  w) →
              Bool)
            Bool (xs n)))
      t) :=
  @HDLean.RAMCircuit.hardware_correct

/-- Frozen statement of `HDLean.SkidBuffer.Challenge.budget`. -/
theorem SkidBuffer_Challenge_budget :
    ∀ (w : Nat),
  @LE.le.{0} Nat instLENat
    (@HDLean.Netlist.Module.ffBits (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HDLean.lower (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (HDLean.SkidBuffer.hardware w)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) :=
  @HDLean.SkidBuffer.Challenge.budget

/-- Frozen statement of `HDLean.SkidBuffer.Challenge.correctness`. -/
theorem SkidBuffer_Challenge_correctness :
    ∀ (w : Nat),
  @HDLean.RefinesAfterReset
    (Fin
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
      Bool)
    (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      Bool)
    (Fin
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
      Bool)
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → List.{0} (Vector.{0} Bool w))
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → HDLean.Fifo.Output (Vector.{0} Bool w))
    (@HDLean.Circuit.denote (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (HDLean.SkidBuffer.hardware w) (HDLean.SkidBuffer.hardware_moore w))
    (HDLean.SkidBuffer.pipelineWireSpec w) (@HDLean.SkidBuffer.observePipeline w)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) :=
  @HDLean.SkidBuffer.Challenge.correctness

/-- Frozen statement of `HDLean.SkidBuffer.pipeline_correct`. -/
theorem SkidBuffer_pipeline_correct :
    ∀ {α : Type} (garbage : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → α) (fallback : α),
  @HDLean.Refines (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → HDLean.Fifo.State α)
    (HDLean.Fifo.Input α) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → HDLean.Fifo.Output α)
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → List.{0} α)
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → HDLean.Fifo.Output α)
    (@HDLean.Machine.network (HDLean.Fifo.State α) (HDLean.Fifo.Input α) (HDLean.Fifo.Output α) (HDLean.Fifo.Input α)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (fun (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
        @HDLean.SkidBuffer.stage α (garbage k))
      (@HDLean.SkidBuffer.wiring α fallback))
    (@HDLean.Machine.network (List.{0} α) (HDLean.Fifo.Input α) (HDLean.Fifo.Output α) (HDLean.Fifo.Input α)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
        HDLean.Fifo.spec α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HDLean.SkidBuffer.wiring α fallback))
    (@id.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → HDLean.Fifo.Output α)) :=
  @HDLean.SkidBuffer.pipeline_correct

/-- Frozen statement of `HDLean.Tests.counter_graph`. -/
theorem Tests_counter_graph :
    @HDLean.Backend.Graph.Equivalent (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
  (@HDLean.Backend.compile (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@HDLean.lower (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) HDLean.Counter.hardware))
  HDLean.Counter.hardware :=
  @HDLean.Tests.counter_graph

/-- Frozen statement of `HDLean.Tests.fifo1_graph`. -/
theorem Tests_fifo1_graph :
    @HDLean.Backend.Graph.Equivalent (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@HDLean.Backend.compile (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HDLean.lower (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (HDLean.Fifo.hardware (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (HDLean.Fifo.hardware (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) :=
  @HDLean.Tests.fifo1_graph

/-- Frozen statement of `HDLean.Tests.fifo8_graph`. -/
theorem Tests_fifo8_graph :
    @HDLean.Backend.Graph.Equivalent (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@HDLean.Backend.compile (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HDLean.lower (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (HDLean.Fifo.hardware (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
  (HDLean.Fifo.hardware (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) :=
  @HDLean.Tests.fifo8_graph

/-- Frozen statement of `HDLean.Tests.packet_roundtrip`. -/
theorem Tests_packet_roundtrip :
    ∀ {w : Nat} (p : HDLean.Tests.Packet w),
  @Eq.{1} (HDLean.Tests.Packet w)
    (@HDLean.Synth.decode (HDLean.Tests.Packet w) (@HDLean.Tests.instSynthPacket w)
      (@HDLean.Synth.encode (HDLean.Tests.Packet w) (@HDLean.Tests.instSynthPacket w) p))
    p :=
  @HDLean.Tests.packet_roundtrip

/-- Frozen statement of `HDLean.Tests.surfaceIncrement_correct`. -/
theorem Tests_surfaceIncrement_correct :
    ∀ (xs : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Bool)
  (state : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Bool),
  @Eq.{1} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
    (@HDLean.WordExpr.eval (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) HDLean.Tests.surfaceIncrement xs state)
    (have count :=
      @HDLean.WordExpr.eval (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@HDLean.WordExpr.registers (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@of_decide_eq_true
            (@LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (Nat.decLe
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@id.{0}
              (@Eq.{1} Bool
                (@Decidable.decide
                  (@LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (Nat.decLe
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                Bool.true)
              (@Eq.refl.{1} Bool Bool.true))))
        xs state;
    @ite.{1} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@Eq.{1} Bool
        (xs
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (nat_lit 0))))
        Bool.true)
      (instDecidableEqBool
        (xs
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (nat_lit 0))))
        Bool.true)
      (@ite.{1} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@Eq.{1} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) count
          (@OfNat.ofNat.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 9)
            (@BitVec.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 9))))
        (@instDecidableEqBitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) count
          (@OfNat.ofNat.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 9)
            (@BitVec.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 9))))
        (@OfNat.ofNat.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
          (@BitVec.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 0)))
        (@HAdd.hAdd.{0, 0, 0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@instHAdd.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@BitVec.instAdd (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
          count
          (@OfNat.ofNat.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
            (@BitVec.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (nat_lit 1)))))
      count) :=
  @HDLean.Tests.surfaceIncrement_correct

/-- Frozen statement of `HDLean.Toy16.Challenge.budget`. -/
theorem Toy16_Challenge_budget :
    ∀ (imem : HDLean.Toy16.Addr → HDLean.Toy16.Word),
  @LE.le.{0} Nat instLENat
    (@HDLean.Netlist.Module.ffBits (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268)))
        (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
      (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
      (@HDLean.lower (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268)))
          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
        (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79))) (HDLean.Toy16.Physical.hardware imem)))
    (@OfNat.ofNat.{0} Nat (nat_lit 4288) (instOfNatNat (nat_lit 4288))) :=
  @HDLean.Toy16.Challenge.budget

/-- Frozen statement of `HDLean.Toy16.Challenge.correctness`. -/
theorem Toy16_Challenge_correctness :
    ∀ (imem : HDLean.Toy16.Addr → HDLean.Toy16.Word)
  (s₀ :
    Fin
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268)))
          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))) →
      Bool)
  (rst : Nat → Bool),
  @Eq.{1} Bool (rst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) Bool.true →
    (∀ (t : Nat),
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t →
          @Eq.{1} Bool (rst t) Bool.false) →
      @Exists.{1} (HDLean.Toy16.Reg → HDLean.Toy16.Word) fun (regs : HDLean.Toy16.Reg → HDLean.Toy16.Word) =>
        @Exists.{1} (HDLean.Toy16.Addr → HDLean.Toy16.Word) fun (mem : HDLean.Toy16.Addr → HDLean.Toy16.Word) =>
          have retire := fun (t : Nat) =>
            HDLean.Toy16.Physical.observe
              (@HDLean.PMachine.runFrom
                (Fin
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))) →
                  Bool)
                (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → Bool) Bool)
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79))) → Bool)
                (@HDLean.Circuit.denote (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79))) (HDLean.Toy16.Physical.hardware imem)
                  (HDLean.Toy16.Physical.hardware_moore imem))
                s₀
                (fun (n : Nat) =>
                  @Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → Bool) Bool
                    (@Fin.elim0.{1} Bool) (rst n))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))));
          And
            (@HDLean.RetiresLike.{0} HDLean.Toy16.Retire retire
              (HDLean.Toy16.isaRetire imem (HDLean.Toy16.ArchState.atReset regs mem)))
            (@HDLean.Progress.{0} HDLean.Toy16.Retire (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              retire HDLean.Toy16.Retire.halt) :=
  @HDLean.Toy16.Challenge.correctness

/-- Frozen statement of `HDLean.Toy16.Physical.decode_next`. -/
theorem Toy16_Physical_decode_next :
    ∀ (imem : HDLean.Toy16.Addr → HDLean.Toy16.Word)
  (s :
    Fin
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268)))
          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))) →
      Bool)
  (rst : Bool),
  @Eq.{1} HDLean.Toy16.CoreState
    (HDLean.Toy16.Physical.decode
      (@HDLean.Circuit.next (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268)))
          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
        (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79))) (HDLean.Toy16.Physical.hardware imem) s
        (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → Bool) Bool
          (@Fin.elim0.{1} Bool) rst)))
    (@HDLean.PMachine.next HDLean.Toy16.CoreState Bool (Option.{0} HDLean.Toy16.Retire) (HDLean.Toy16.core imem)
      (HDLean.Toy16.Physical.decode s) rst) :=
  @HDLean.Toy16.Physical.decode_next

/-- Frozen statement of `HDLean.Toy16.Physical.decode_output`. -/
theorem Toy16_Physical_decode_output :
    ∀ (imem : HDLean.Toy16.Addr → HDLean.Toy16.Word)
  (s :
    Fin
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268)))
          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))) →
      Bool),
  @Eq.{1} (Option.{0} HDLean.Toy16.Retire)
    (HDLean.Toy16.Physical.observe
      (@HDLean.Circuit.evalOutput (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268)))
          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
        (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79))) (HDLean.Toy16.Physical.hardware imem) s
        (@Fin.elim0.{1} Bool)))
    (@HDLean.PMachine.out HDLean.Toy16.CoreState Bool (Option.{0} HDLean.Toy16.Retire) (HDLean.Toy16.core imem)
      (HDLean.Toy16.Physical.decode s)) :=
  @HDLean.Toy16.Physical.decode_output

/-- Frozen statement of `HDLean.Verification.FiniteSystem.check_sound`. -/
theorem Verification_FiniteSystem_check_sound :
    ∀ {n i : Nat} (sys : HDLean.Verification.FiniteSystem n i) (candidate safe : Fin n → Bool),
  @Eq.{1} Bool (@HDLean.Verification.FiniteSystem.check n i sys candidate safe) Bool.true →
    ∀ (s : Fin n),
      @Eq.{1} Bool (@HDLean.Verification.FiniteSystem.initial n i sys s) Bool.true →
        ∀ (xs : Nat → Fin i) (t : Nat),
          @Eq.{1} Bool
            (safe
              (@HDLean.PMachine.stateFrom (Fin n) (Fin i) (Fin n)
                (@HDLean.PMachine.mk (Fin n) (Fin i) (Fin n) (@id.{1} (Fin n))
                  (@HDLean.Verification.FiniteSystem.next n i sys))
                s xs t))
            Bool.true :=
  @HDLean.Verification.FiniteSystem.check_sound

/-- Frozen statement of `HDLean.WordExpr.addWithCarry_correct`. -/
theorem WordExpr_addWithCarry_correct :
    ∀ {d i r w : Nat} (a b : HDLean.WordExpr d i r w) (initial : HDLean.Expr d i r) (xs : Fin i → Bool)
  (state : Fin r → Bool),
  @Eq.{1} (BitVec w)
    (@HDLean.WordExpr.eval d i r w
      (@Prod.fst.{0, 0} (HDLean.WordExpr d i r w) (HDLean.Expr d i r)
        (@HDLean.WordExpr.addWithCarry d i r w a b initial))
      xs state)
    (@HAdd.hAdd.{0, 0, 0} (BitVec w) (BitVec w) (BitVec w) (@instHAdd.{0} (BitVec w) (@BitVec.instAdd w))
      (@HAdd.hAdd.{0, 0, 0} (BitVec w) (BitVec w) (BitVec w) (@instHAdd.{0} (BitVec w) (@BitVec.instAdd w))
        (@HDLean.WordExpr.eval d i r w a xs state) (@HDLean.WordExpr.eval d i r w b xs state))
      (@BitVec.setWidth (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w
        (BitVec.ofBool (@HDLean.Expr.eval i r d xs state initial)))) :=
  @HDLean.WordExpr.addWithCarry_correct

/-- Frozen statement of `HDLean.WordExpr.addWithCarry_overflow`. -/
theorem WordExpr_addWithCarry_overflow :
    ∀ {d i r w : Nat} (a b : HDLean.WordExpr d i r w) (initial : HDLean.Expr d i r) (xs : Fin i → Bool)
  (state : Fin r → Bool),
  @Eq.{1} Bool
    (@HDLean.Expr.eval i r d xs state
      (@Prod.snd.{0, 0} (HDLean.WordExpr d i r w) (HDLean.Expr d i r)
        (@HDLean.WordExpr.addWithCarry d i r w a b initial)))
    (@BitVec.carry w w (@HDLean.WordExpr.eval d i r w a xs state) (@HDLean.WordExpr.eval d i r w b xs state)
      (@HDLean.Expr.eval i r d xs state initial)) :=
  @HDLean.WordExpr.addWithCarry_overflow

/-- Frozen statement of `HDLean.WordExpr.equal_correct`. -/
theorem WordExpr_equal_correct :
    ∀ {d i r w : Nat} (a b : HDLean.WordExpr d i r w) (xs : Fin i → Bool) (state : Fin r → Bool),
  @Eq.{1} Bool (@HDLean.Expr.eval i r d xs state (@HDLean.WordExpr.equal d i r w a b))
    (@Decidable.decide
      (@Eq.{1} (BitVec w) (@HDLean.WordExpr.eval d i r w a xs state) (@HDLean.WordExpr.eval d i r w b xs state))
      (@instDecidableEqBitVec w (@HDLean.WordExpr.eval d i r w a xs state) (@HDLean.WordExpr.eval d i r w b xs state))) :=
  @HDLean.WordExpr.equal_correct

/-- Frozen statement of `HDLean.WordExpr.selectBalanced_correct`. -/
theorem WordExpr_selectBalanced_correct :
    ∀ {d i r a w : Nat} (address : HDLean.WordExpr d i r a)
  (table :
    Fin
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a) →
      HDLean.WordExpr d i r w)
  (xs : Fin i → Bool) (state : Fin r → Bool),
  @Eq.{1} (BitVec w) (@HDLean.WordExpr.eval d i r w (@HDLean.WordExpr.selectBalanced d i r w a address table) xs state)
    (@HDLean.WordExpr.eval d i r w
      (table
        (@Fin.mk
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
          (@BitVec.toNat a (@HDLean.WordExpr.eval d i r a address xs state))
          (@BitVec.isLt a (@HDLean.WordExpr.eval d i r a address xs state))))
      xs state) :=
  @HDLean.WordExpr.selectBalanced_correct

/-- Frozen statement of `HDLean.WordExpr.setWidth_correct`. -/
theorem WordExpr_setWidth_correct :
    ∀ {d i r w : Nat} (a : HDLean.WordExpr d i r w) (size : Nat) (xs : Fin i → Bool) (state : Fin r → Bool),
  @Eq.{1} (BitVec size) (@HDLean.WordExpr.eval d i r size (@HDLean.WordExpr.setWidth d i r w a size) xs state)
    (@BitVec.setWidth w size (@HDLean.WordExpr.eval d i r w a xs state)) :=
  @HDLean.WordExpr.setWidth_correct

/-- Frozen statement of `HDLean.WordExpr.signExtend_correct`. -/
theorem WordExpr_signExtend_correct :
    ∀ {d i r w : Nat} (a : HDLean.WordExpr d i r w) (size : Nat) (xs : Fin i → Bool) (state : Fin r → Bool),
  @Eq.{1} (BitVec size) (@HDLean.WordExpr.eval d i r size (@HDLean.WordExpr.signExtend d i r w a size) xs state)
    (@BitVec.signExtend w size (@HDLean.WordExpr.eval d i r w a xs state)) :=
  @HDLean.WordExpr.signExtend_correct

/-- Frozen statement of `HDLean.WordExpr.sub_correct`. -/
theorem WordExpr_sub_correct :
    ∀ {d i r w : Nat} (a b : HDLean.WordExpr d i r w) (xs : Fin i → Bool) (state : Fin r → Bool),
  @Eq.{1} (BitVec w) (@HDLean.WordExpr.eval d i r w (@HDLean.WordExpr.sub d i r w a b) xs state)
    (@HSub.hSub.{0, 0, 0} (BitVec w) (BitVec w) (BitVec w) (@instHSub.{0} (BitVec w) (@BitVec.instSub w))
      (@HDLean.WordExpr.eval d i r w a xs state) (@HDLean.WordExpr.eval d i r w b xs state)) :=
  @HDLean.WordExpr.sub_correct

/-- Frozen statement of `HDLean.WordExpr.ult_correct`. -/
theorem WordExpr_ult_correct :
    ∀ {d i r w : Nat} (a b : HDLean.WordExpr d i r w) (xs : Fin i → Bool) (state : Fin r → Bool),
  @Eq.{1} Bool (@HDLean.Expr.eval i r d xs state (@HDLean.WordExpr.ult d i r w a b))
    (@BitVec.ult w (@HDLean.WordExpr.eval d i r w a xs state) (@HDLean.WordExpr.eval d i r w b xs state)) :=
  @HDLean.WordExpr.ult_correct

/-- Frozen statement of `HDLean.compose_contracts`. -/
theorem compose_contracts :
    ∀ {A B : Nat → Prop}, HDLean.CausalContract A B → HDLean.CausalContract B A → ∀ (t : Nat), And (A t) (B t) :=
  @HDLean.compose_contracts

/-- Frozen statement of `HDLean.gray_adjacent`. -/
theorem gray_adjacent :
    ∀ {w : Nat} (x : BitVec w),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) w →
    @HDLean.Adjacent w (@HDLean.gray w x)
      (@HDLean.gray w
        (@HAdd.hAdd.{0, 0, 0} (BitVec w) (BitVec w) (BitVec w) (@instHAdd.{0} (BitVec w) (@BitVec.instAdd w)) x
          (@OfNat.ofNat.{0} (BitVec w) (nat_lit 1) (@BitVec.instOfNat w (nat_lit 1))))) :=
  @HDLean.gray_adjacent

/-- Frozen statement of `HDLean.gray_increment_ne`. -/
theorem gray_increment_ne :
    ∀ {w : Nat} (x : BitVec w),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) w →
    @Ne.{1} (BitVec w) (@HDLean.gray w x)
      (@HDLean.gray w
        (@HAdd.hAdd.{0, 0, 0} (BitVec w) (BitVec w) (BitVec w) (@instHAdd.{0} (BitVec w) (@BitVec.instAdd w)) x
          (@OfNat.ofNat.{0} (BitVec w) (nat_lit 1) (@BitVec.instOfNat w (nat_lit 1))))) :=
  @HDLean.gray_increment_ne

/-- Frozen statement of `HDLean.gray_injective`. -/
theorem gray_injective :
    ∀ {w : Nat} (a b : BitVec w), @Eq.{1} (BitVec w) (@HDLean.gray w a) (@HDLean.gray w b) → @Eq.{1} (BitVec w) a b :=
  @HDLean.gray_injective

/-- Frozen statement of `HDLean.gray_one_bit8`. -/
theorem gray_one_bit8 :
    ∀ (x : BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))),
  have d :=
    @HXor.hXor.{0, 0, 0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      (@instHXorOfXorOp.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (@BitVec.instXorOp (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
      (@HDLean.gray (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) x)
      (@HDLean.gray (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
        (@HAdd.hAdd.{0, 0, 0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (@instHAdd.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (@BitVec.instAdd (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
          x
          (@OfNat.ofNat.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 1)
            (@BitVec.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 1)))));
  And
    (@Ne.{1} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) d
      (@OfNat.ofNat.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 0)
        (@BitVec.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 0))))
    (@Eq.{1} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      (@HAnd.hAnd.{0, 0, 0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (@instHAndOfAndOp.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (@BitVec.instAndOp (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
        d
        (@HSub.hSub.{0, 0, 0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (@instHSub.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (@BitVec.instSub (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
          d
          (@OfNat.ofNat.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 1)
            (@BitVec.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 1)))))
      (@OfNat.ofNat.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 0)
        (@BitVec.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 0)))) :=
  @HDLean.gray_one_bit8

/-- Frozen statement of `HDLean.lowerExpr_correct`. -/
theorem lowerExpr_correct :
    ∀ {d : HDLean.Domain} {i r : Nat} (e : HDLean.Expr d i r) (xs : Fin i → Bool) (s : Fin r → Bool),
  @Eq.{1} Bool (@HDLean.Netlist.Node.eval i r d xs s (@HDLean.lowerExpr d i r e)) (@HDLean.Expr.eval i r d xs s e) :=
  @HDLean.lowerExpr_correct

/-- Frozen statement of `HDLean.lower_next`. -/
theorem lower_next :
    ∀ {d i r o : Nat} (c : HDLean.Circuit d i r o) (s : Fin r → Bool) (xs : Prod.{0, 0} (Fin i → Bool) Bool),
  @Eq.{1} (Fin r → Bool) (@HDLean.Netlist.Module.next d i r o (@HDLean.lower d i r o c) s xs)
    (@HDLean.Circuit.next d i r o c s xs) :=
  @HDLean.lower_next

/-- Frozen statement of `HDLean.lower_output`. -/
theorem lower_output :
    ∀ {d i r o : Nat} (c : HDLean.Circuit d i r o) (s : Fin r → Bool) (xs : Fin i → Bool),
  @Eq.{1} (Fin o → Bool) (@HDLean.Netlist.Module.evalOutput d i r o (@HDLean.lower d i r o c) s xs)
    (@HDLean.Circuit.evalOutput d i r o c s xs) :=
  @HDLean.lower_output

/-- Frozen statement of `HDLean.network_refines`. -/
theorem network_refines :
    ∀ {σ ι ο τ κ : Type} (count : Nat) (a : Fin count → HDLean.Machine σ ι ο) (b : Fin count → HDLean.Machine τ ι ο)
  (wire : κ → (Fin count → ο) → Fin count → ι) (R : Fin count → σ → τ → Prop),
  (∀ (k : Fin count), R k (@HDLean.Machine.init σ ι ο (a k)) (@HDLean.Machine.init τ ι ο (b k))) →
    (∀ (k : Fin count) (s : σ) (q : τ) (i : ι),
        R k s q → R k (@HDLean.Machine.next σ ι ο (a k) s i) (@HDLean.Machine.next τ ι ο (b k) q i)) →
      (∀ (k : Fin count) (s : σ) (q : τ),
          R k s q → @Eq.{1} ο (@HDLean.Machine.out σ ι ο (a k) s) (@HDLean.Machine.out τ ι ο (b k) q)) →
        @HDLean.Refines (Fin count → σ) κ (Fin count → ο) (Fin count → τ) (Fin count → ο)
          (@HDLean.Machine.network σ ι ο κ count a wire) (@HDLean.Machine.network τ ι ο κ count b wire)
          (@id.{1} (Fin count → ο)) :=
  @HDLean.network_refines

/-- Frozen statement of `HDLean.one_bit_mix`. -/
theorem one_bit_mix :
    ∀ {w : Nat} (a b m : BitVec w),
  @Eq.{1} (BitVec w)
      (@HAnd.hAnd.{0, 0, 0} (BitVec w) (BitVec w) (BitVec w) (@instHAndOfAndOp.{0} (BitVec w) (@BitVec.instAndOp w))
        (@HXor.hXor.{0, 0, 0} (BitVec w) (BitVec w) (BitVec w) (@instHXorOfXorOp.{0} (BitVec w) (@BitVec.instXorOp w)) a
          b)
        (@HSub.hSub.{0, 0, 0} (BitVec w) (BitVec w) (BitVec w) (@instHSub.{0} (BitVec w) (@BitVec.instSub w))
          (@HXor.hXor.{0, 0, 0} (BitVec w) (BitVec w) (BitVec w) (@instHXorOfXorOp.{0} (BitVec w) (@BitVec.instXorOp w))
            a b)
          (@OfNat.ofNat.{0} (BitVec w) (nat_lit 1) (@BitVec.instOfNat w (nat_lit 1)))))
      (@OfNat.ofNat.{0} (BitVec w) (nat_lit 0) (@BitVec.instOfNat w (nat_lit 0))) →
    Or (@Eq.{1} (BitVec w) (@HDLean.sampleBits w a b m) a) (@Eq.{1} (BitVec w) (@HDLean.sampleBits w a b m) b) :=
  @HDLean.one_bit_mix

/-- Frozen statement of `HDLean.one_bit_mix8`. -/
theorem one_bit_mix8 :
    ∀ (a b m : BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))),
  @Eq.{1} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      (@HAnd.hAnd.{0, 0, 0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (@instHAndOfAndOp.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (@BitVec.instAndOp (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
        (@HXor.hXor.{0, 0, 0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (@instHXorOfXorOp.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (@BitVec.instXorOp (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
          a b)
        (@HSub.hSub.{0, 0, 0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          (@instHSub.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (@BitVec.instSub (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
          (@HXor.hXor.{0, 0, 0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (@instHXorOfXorOp.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (@BitVec.instXorOp (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
            a b)
          (@OfNat.ofNat.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 1)
            (@BitVec.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 1)))))
      (@OfNat.ofNat.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 0)
        (@BitVec.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (nat_lit 0))) →
    Or
      (@Eq.{1} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (@HDLean.sampleBits (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) a b m) a)
      (@Eq.{1} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
        (@HDLean.sampleBits (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) a b m) b) :=
  @HDLean.one_bit_mix8

/-- Frozen statement of `HDLean.refinesAfterReset_of_simulation`. -/
theorem refinesAfterReset_of_simulation :
    ∀ {σ ι ο τ π : Type} (impl : HDLean.PMachine σ (Prod.{0, 0} ι Bool) ο) (spec : HDLean.Machine τ ι π) (obs : ο → π)
  (r : Nat) (R : σ → τ → Prop),
  (∀ (s₀ : σ) (xs : Nat → Prod.{0, 0} ι Bool),
      (∀ (t : Nat), @LT.lt.{0} Nat instLTNat t r → @Eq.{1} Bool (@Prod.snd.{0, 0} ι Bool (xs t)) Bool.true) →
        R (@HDLean.PMachine.stateFrom σ (Prod.{0, 0} ι Bool) ο impl s₀ xs r) (@HDLean.Machine.init τ ι π spec)) →
    (∀ (s : σ) (q : τ) (i : ι),
        R s q →
          R (@HDLean.PMachine.next σ (Prod.{0, 0} ι Bool) ο impl s (@Prod.mk.{0, 0} ι Bool i Bool.false))
            (@HDLean.Machine.next τ ι π spec q i)) →
      (∀ (s : σ) (q : τ),
          R s q →
            @Eq.{1} π (obs (@HDLean.PMachine.out σ (Prod.{0, 0} ι Bool) ο impl s)) (@HDLean.Machine.out τ ι π spec q)) →
        @HDLean.RefinesAfterReset σ ι ο τ π impl spec obs r :=
  @HDLean.refinesAfterReset_of_simulation

/-- Frozen statement of `HDLean.refinesResetSchedule_of_simulation`. -/
theorem refinesResetSchedule_of_simulation :
    ∀ {σ ι ο τ π : Type} (impl : HDLean.PMachine σ (Prod.{0, 0} ι Bool) ο) (spec : HDLean.Machine τ ι π) (obs : ο → π)
  (R : σ → τ → Prop),
  (∀ (s : σ) (i : ι),
      R (@HDLean.PMachine.next σ (Prod.{0, 0} ι Bool) ο impl s (@Prod.mk.{0, 0} ι Bool i Bool.true))
        (@HDLean.Machine.init τ ι π spec)) →
    (∀ (s : σ) (q : τ) (i : ι),
        R s q →
          R (@HDLean.PMachine.next σ (Prod.{0, 0} ι Bool) ο impl s (@Prod.mk.{0, 0} ι Bool i Bool.false))
            (@HDLean.Machine.next τ ι π spec q i)) →
      (∀ (s : σ) (q : τ),
          R s q →
            @Eq.{1} π (obs (@HDLean.PMachine.out σ (Prod.{0, 0} ι Bool) ο impl s)) (@HDLean.Machine.out τ ι π spec q)) →
        @HDLean.RefinesResetSchedule σ ι ο τ π impl spec obs :=
  @HDLean.refinesResetSchedule_of_simulation

/-- Frozen statement of `HDLean.reset_noninterference`. -/
theorem reset_noninterference :
    ∀ {σ ι ο τ π : Type} {impl : HDLean.PMachine σ (Prod.{0, 0} ι Bool) ο} {spec : HDLean.Machine τ ι π} {obs : ο → π}
  {r : Nat},
  @HDLean.RefinesAfterReset σ ι ο τ π impl spec obs r →
    ∀ (a b : σ) (xs : Nat → Prod.{0, 0} ι Bool),
      (∀ (t : Nat), @LT.lt.{0} Nat instLTNat t r → @Eq.{1} Bool (@Prod.snd.{0, 0} ι Bool (xs t)) Bool.true) →
        (∀ (t : Nat), @LE.le.{0} Nat instLENat r t → @Eq.{1} Bool (@Prod.snd.{0, 0} ι Bool (xs t)) Bool.false) →
          ∀ (t : Nat),
            @Eq.{1} π
              (obs
                (@HDLean.PMachine.runFrom σ (Prod.{0, 0} ι Bool) ο impl a xs
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r t)))
              (obs
                (@HDLean.PMachine.runFrom σ (Prod.{0, 0} ι Bool) ο impl b xs
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r t))) :=
  @HDLean.reset_noninterference

/-- Frozen statement of `HDLean.retiresLike_of_simulation`. -/
theorem retiresLike_of_simulation.{u_1} :
    ∀ {σ ι α : Type} {τ : Sort u_1} (impl : HDLean.Machine σ ι (Option.{0} α)) (step : τ → τ) (initial : τ) (event : τ → α)
  (R : σ → τ → Prop),
  R (@HDLean.Machine.init σ ι (Option.{0} α) impl) initial →
    (∀ (s : σ) (q : τ) (i : ι),
        R s q →
          @Eq.{1} (Option.{0} α) (@HDLean.Machine.out σ ι (Option.{0} α) impl s) (@Option.none.{0} α) →
            R (@HDLean.Machine.next σ ι (Option.{0} α) impl s i) q) →
      (∀ (s : σ) (q : τ) (i : ι) (a : α),
          R s q →
            @Eq.{1} (Option.{0} α) (@HDLean.Machine.out σ ι (Option.{0} α) impl s) (@Option.some.{0} α a) →
              And (@Eq.{1} α a (event q)) (R (@HDLean.Machine.next σ ι (Option.{0} α) impl s i) (step q))) →
        ∀ (xs : Nat → ι),
          @HDLean.RetiresLike.{0} α (@HDLean.Machine.run σ ι (Option.{0} α) impl xs) fun (n : Nat) =>
            event (@HDLean.iterate.{u_1} τ step initial n) :=
  @HDLean.retiresLike_of_simulation.{u_1}

/-- Frozen statement of `HDLean.sample_adjacent`. -/
theorem sample_adjacent :
    ∀ {w : Nat} (a b m : BitVec w),
  @HDLean.Adjacent w a b →
    Or (@Eq.{1} (BitVec w) (@HDLean.sampleBits w a b m) a) (@Eq.{1} (BitVec w) (@HDLean.sampleBits w a b m) b) :=
  @HDLean.sample_adjacent

/-- Frozen statement of `HDLean.sample_gray_increment`. -/
theorem sample_gray_increment :
    ∀ {w : Nat} (x mask : BitVec w),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) w →
    Or
      (@Eq.{1} (BitVec w)
        (@HDLean.sampleBits w (@HDLean.gray w x)
          (@HDLean.gray w
            (@HAdd.hAdd.{0, 0, 0} (BitVec w) (BitVec w) (BitVec w) (@instHAdd.{0} (BitVec w) (@BitVec.instAdd w)) x
              (@OfNat.ofNat.{0} (BitVec w) (nat_lit 1) (@BitVec.instOfNat w (nat_lit 1)))))
          mask)
        (@HDLean.gray w x))
      (@Eq.{1} (BitVec w)
        (@HDLean.sampleBits w (@HDLean.gray w x)
          (@HDLean.gray w
            (@HAdd.hAdd.{0, 0, 0} (BitVec w) (BitVec w) (BitVec w) (@instHAdd.{0} (BitVec w) (@BitVec.instAdd w)) x
              (@OfNat.ofNat.{0} (BitVec w) (nat_lit 1) (@BitVec.instOfNat w (nat_lit 1)))))
          mask)
        (@HDLean.gray w
          (@HAdd.hAdd.{0, 0, 0} (BitVec w) (BitVec w) (BitVec w) (@instHAdd.{0} (BitVec w) (@BitVec.instAdd w)) x
            (@OfNat.ofNat.{0} (BitVec w) (nat_lit 1) (@BitVec.instOfNat w (nat_lit 1)))))) :=
  @HDLean.sample_gray_increment

/-- Frozen statement of `HDLean.sync2_stable`. -/
theorem sync2_stable :
    ∀ (s : HDLean.Sync2 Bool) (v a b : Bool),
  @Eq.{1} Bool (@HDLean.Sync2.second Bool (HDLean.sync2Step (HDLean.sync2Step s Bool.true v v a) Bool.true v v b)) v :=
  @HDLean.sync2_stable

end HDLean.Review
