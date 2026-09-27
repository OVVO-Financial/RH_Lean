import Mathlib
import RHLean.Proof.SquareRootMertensEndpointAmplification
import «research.GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE»

/-!
# Endpoint amplification closes the post-789 finite-bound target explicitly

This module records the exact quantitative transfer from the square-root
endpoint amplification seam back into the post-789 returned-core currency.

If one has any fixed endpoint amplification constant

  (M(R^2-1)-1)^2 <= A R^2 K,

then the canonical rough correlation

  M(R-1)-M(R^2-1)

is bounded using only the lower-envelope value at R-1:

  Corr_R^2 <= (2 A + 2) R^2 K.

No q^2 daughter energy is needed for this step.  Feeding this through the
already-compiled Young comparison at a=1/8, b=2 gives

  post789 remainder <= 2 E_R + (9/4)(A+1) R^2 K.

Thus the original "prove any universal finite post-789 bound" target is reduced
with explicit constants to the square-root endpoint amplification theorem.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- A fixed, non-existential endpoint amplification hypothesis. -/
def SquareRootMertensEndpointAmplificationWith (A : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    2 ≤ R →
    LowerMertensCriticalEnvelope R K →
    (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) ≤
      A * (R : ℝ) ^ 2 * K

/-- **Endpoint amplification -> pure root-scale CORR bound.**

The lower endpoint M(R-1)-1 is already controlled by the defining critical
envelope.  The top endpoint M(R^2-1)-1 is the sole new input. -/
theorem canonicalRoughCorrelation_rootBound_of_endpointAmplificationWith
    {A : ℝ} (hA : 0 ≤ A)
    (hAmp : SquareRootMertensEndpointAmplificationWith A) :
    CanonicalRoughCorrelationLowQ2EnergyStatementWith 0 (2 * A + 2) := by
  intro R K hR hK
  have hTop := hAmp R K (by omega) hK
  have hPred := hK.2 (R - 1) (by omega)
  have hPredCast :
      (((mertensSummatoryInt (R - 1) - 1 : ℤ) : ℝ)) =
        (mertensSummatoryInt (R - 1) : ℝ) - 1 := by
    push_cast
    ring
  have hTopCast :
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)) =
        (mertensSummatoryInt (squareRootEndpoint R) : ℝ) - 1 := by
    push_cast
    ring
  rw [hPredCast] at hPred
  rw [hTopCast] at hTop
  have hRcast : (((R - 1 + 1 : ℕ) : ℝ)) = (R : ℝ) := by
    have h : R - 1 + 1 = R := by omega
    rw [h]
  rw [hRcast] at hPred
  have hK0 : 0 ≤ K := hK.1
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  have hPredAbsorb :
      K * (R : ℝ) ≤ (R : ℝ) ^ 2 * K := by
    nlinarith
  have hGap :
      ((mertensSummatoryInt (squareRootEndpoint R) : ℝ) -
          (mertensSummatoryInt (R - 1) : ℝ)) ^ 2 ≤
        (2 * A + 2) * (R : ℝ) ^ 2 * K := by
    have hsq :=
      sq_nonneg
        (((mertensSummatoryInt (squareRootEndpoint R) : ℝ) - 1) +
          ((mertensSummatoryInt (R - 1) : ℝ) - 1))
    nlinarith
  rw [norm_sq_squareRootCanonicalRoughCorrelation_eq_post789EndpointGap_sq
      (R := R) (by omega)]
  unfold lowOwnerPost789EndpointGapReal
  norm_num
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hGap

/-- **Explicit post-789 universal bound from endpoint amplification.**

Choosing Young parameters a=1/8 and b=2 preserves the RH-sufficient daughter
coefficient 2. -/
theorem post789SignedRemainderBound_two_of_endpointAmplificationWith
    {A : ℝ} (hA : 0 ≤ A)
    (hAmp : SquareRootMertensEndpointAmplificationWith A) :
    LowOwnerPost789SignedCrossDiagonalRemainderBound
      2 ((9 / 4 : ℝ) * (A + 1)) := by
  have hCorr :=
    canonicalRoughCorrelation_rootBound_of_endpointAmplificationWith hA hAmp
  have h :=
    post789SignedRemainderBound_of_correlationLowQ2Energy
      (a := 1 / 8) (b := 2) (by norm_num) (by norm_num) hCorr
  intro R K hR hK
  have hh := h R K hR hK
  norm_num at hh ⊢
  nlinarith

/-- The existential endpoint theorem therefore supplies an explicit existential
finite post-789 bound with daughter coefficient exactly 2. -/
theorem exists_post789SignedRemainderBound_two_of_endpointAmplification
    (hAmp : SquareRootMertensEndpointAmplificationStatement) :
    ∃ C : ℝ, 0 ≤ C ∧
      LowOwnerPost789SignedCrossDiagonalRemainderBound 2 C := by
  rcases hAmp with ⟨A, hA, hAmpA⟩
  refine ⟨(9 / 4 : ℝ) * (A + 1), ?_, ?_⟩
  · positivity
  · exact post789SignedRemainderBound_two_of_endpointAmplificationWith
      hA hAmpA

end RHLean.Proof
