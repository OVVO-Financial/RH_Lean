import RHLean.Analysis.SquareRootMatchedDegreeOneRecovery
import RHLean.Proof.SquareRootAmplificationClosure

/-!
# Signed transport amplification audit

The square-root amplification target is the fully recovered shifted state
`matched - H - 1`, not the matched channel alone.  The first theorem supplies
the exact normalization needed to use the existing amplification closure.

There is also a finite obstruction to requesting a subunit amplification
constant in the repository's all-`R >= 2` formulation: at `R = 2`, the lower
critical envelope `K = 1` is admissible and the endpoint numerator is four.
Consequently every uniform constant in that formulation is at least one.

This module supplies no uniform endpoint bound and introduces no analytic
hypothesis beyond the explicitly quantified input to its obstruction theorem.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis

/-- The exact amplification numerator retains both the ancestral correction
`-H` and the exceptional unit-source shift `-1` before the norm is taken. -/
theorem recoveredMatchedShiftedEnergy_eq_amplificationNumerator
    (R : ℕ) (hR : 2 ≤ R) :
    ‖squareRootMatchedBornSmoothTransport R -
        squareRootPositiveSmoothPrimeMertensTransform R - 1‖ ^ 2 =
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) := by
  rw [squareRootMatched_sub_positivePrimeTransform_eq_squarePrefixMertens
    R (by omega)]
  unfold squarePrefixMertens
  rw [squarePrefixEndpoint_pred_eq_squareRootEndpoint R (by omega)]
  exact shiftedMertensEnergy_eq_intSquare (squareRootEndpoint R)

/-- The lower-scale data at the first nontrivial root admit the unit envelope. -/
theorem lowerMertensCriticalEnvelope_two_one :
    LowerMertensCriticalEnvelope 2 1 := by
  refine ⟨ by norm_num, ?_ ⟩
  intro y hy
  have hyCases : y = 0 ∨ y = 1 := by omega
  rcases hyCases with rfl | rfl
  · norm_num [mertensSummatoryInt]
  · norm_num [mertensSummatoryInt]

/-- An amplification constant below one cannot satisfy the exact all-root
statement: its first square endpoint already forces `1 <= A`. -/
theorem squareRootEndpointAmplification_constant_ge_one
    {A : ℝ}
    (hbound : ∀ R : ℕ, ∀ K : ℝ,
      2 ≤ R → LowerMertensCriticalEnvelope R K →
        (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) ≤
          A * (R : ℝ) ^ 2 * K) :
    1 ≤ A := by
  have h := hbound 2 1 (by norm_num) lowerMertensCriticalEnvelope_two_one
  have hM : mertensSummatoryInt (squareRootEndpoint 2) = -1 := by
    native_decide
  rw [hM] at h
  norm_num at h
  linarith

end RHLean.Proof
