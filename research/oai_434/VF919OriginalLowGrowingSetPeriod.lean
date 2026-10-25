import OAI.NumberTheory.DirichletL.Detector.GramJoint

/-!
# The true two-column period retains the calibration primes twice

This file proves a source-exact obstruction to removing a growing set S
from the Gram period using only the small norm of a dual frequency.

This is algebra, NOT a disproof of a future analytic CRT cancellation,
and does not assert a global exponent improvement.
-/

namespace OAI

namespace VF919OriginalLowGrowingSetPeriod

open scoped Classical BigOperators
open SevenEighths.ProbePhysical SevenEighths.ProbeGramCommon
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- The original jointFixedModulus includes the entire calibration ideal
    G_S = product of S with multiplicity at least two. -/
theorem jointFixedModulus_calibration_square
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal) :
    (∏ P ∈ S, P)^2 ∣
      SevenEighths.ProbeGramCommon.jointFixedModulus S hS := by
  rw [← SevenEighths.ProbePhysical.calibrationForSet_span S hS]
  let G : Id := Ideal.span {(calibrationForSet S hS).generator}
  let N : Id := Ideal.span {(calibrationLowData S hS).numeratorGood}
  change G^2 ∣
    (G * (1 * G * Ideal.span {(72 : O)} * N) * Ideal.span {(4 : O)}) *
      Ideal.span {ConcretePrimeRowBridge.goodLambda^2} *
      Ideal.span {(72 : O)}
  refine ⟨Ideal.span {(72 : O)} * N * Ideal.span {(4 : O)} *
    Ideal.span {ConcretePrimeRowBridge.goodLambda^2} *
    Ideal.span {(72 : O)}, ?_⟩
  simp only [one_mul, pow_two]
  ac_rfl

/-- The FULL two-column period inherits those square calibration factors,
    regardless of the chosen frequency's good numerator r. -/
theorem jointPeriod_calibration_square
    {ι : Type*} [Fintype ι]
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    (P : ι → Id) (r : O) :
    (∏ p ∈ S, p)^2 ∣
      SevenEighths.ProbeGramCommon.jointPeriod S hS P r := by
  apply dvd_trans (jointFixedModulus_calibration_square S hS)
  change SevenEighths.ProbeGramCommon.jointFixedModulus S hS ∣
    SevenEighths.ProbeGramCommon.jointFixedModulus S hS *
      (∏ i, P i) * Ideal.span {r}
  refine ⟨(∏ i, P i) * Ideal.span {r}, ?_⟩
  simp only [mul_assoc]

#print axioms jointFixedModulus_calibration_square
#print axioms jointPeriod_calibration_square

end VF919OriginalLowGrowingSetPeriod

end OAI
