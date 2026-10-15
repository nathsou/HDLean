import Std

namespace IndependentFixtures

theorem valid : 2 + 2 = (4 : Nat) := rfl

axiom foreign : False
theorem foreignProof : False := foreign

theorem admitted : False := by sorry

theorem nativeProof : 2 + 2 = (4 : Nat) := by native_decide

end IndependentFixtures
