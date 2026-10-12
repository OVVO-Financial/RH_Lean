import Mathlib
import «research.GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE»

/-!
# #919: all-scale signed aggregate ceiling with the genuine top Mertens endpoint

This proves the unconditional bound suggested by the 9/8 Young comparison:

  S_R <= 2 E_R + (9/4) M(R^2-1)^2 + 9 R K

for every R >= 56 and every legitimate lower Mertens envelope K.

Here S is the COMPLETE post-789 signed cross/diagonal remainder,
including all first-owner cells; it is NOT an owner-two clipped boundary
alone. E is the actual q^2 daughter energy. The upper Mertens value is
a genuine remaining term, *not* replaced by a root-scale envelope.

In particular this theorem does not imply S <= 2 E + C R^2 K with
one constant C independent of R and K. It makes the missing arithmetic
estimate impossible to hide behind formal transport or negative-branch
algebra.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The lower-scale envelope controls M(R-1), but NOT M(R^2-1).
It includes the harmless baseline K >= 1. -/
theorem vf919RootMertens_sq_le_four_root_envelope
    {R : ℕ} {K : ℝ} (hR : 56 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    (((mertensSummatoryInt (R - 1) : ℤ) : ℝ)) ^ 2 ≤
      4 * (R : ℝ) * K := by
  have hK1 : (1 : ℝ) ≤ K := by
    have h0 := hK.2 0 (by omega)
    have hm0 : mertensSummatoryInt 0 = 0 := by
      simp [mertensSummatoryInt]
    rw [hm0] at h0
    norm_num at h0
    exact h0
  have hroot := hK.2 (R - 1) (by omega)
  have hRN : (R - 1) + 1 = R := by omega
  rw [hRN] at hroot
  have hroot' :
      ((((mertensSummatoryInt (R - 1) : ℤ) : ℝ) - 1) ^ 2) ≤
        K * (R : ℝ) := by
    simpa only [Int.cast_sub, Int.cast_one] using hroot
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ R)
  have hRK : 1 ≤ K * (R : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hK1)
      (sub_nonneg.mpr hRreal)]
  nlinarith [sq_nonneg ((((mertensSummatoryInt (R - 1) : ℤ) : ℝ)) - 2)]

/-- This is an honest UNCONDITIONAL all-root bound for the COMPLETE
signed remainder; the top Mertens square is still present. -/
theorem vf919Post789_signedAggregate_le_twoEnergy_add_topMertensSq
    {R : ℕ} {K : ℝ} (hR : 56 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    lowOwnerPost789SignedCrossDiagonalRemainder R ≤
      2 * canonicalRoughLowQ2DaughterEnergy R +
      (9 / 4 : ℝ) *
        (((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ)) ^ 2 +
      9 * (R : ℝ) * K := by
  let mTop : ℝ :=
    ((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ)
  let mRoot : ℝ := ((mertensSummatoryInt (R - 1) : ℤ) : ℝ)
  have hyoung := post789SignedRemainder_le_correlationSq_young
    (R := R) (a := (1 / 8 : ℝ)) (b := (2 : ℝ))
    (by omega) (by norm_num) (by norm_num)
  rw [norm_sq_squareRootCanonicalRoughCorrelation_eq_post789EndpointGap_sq
    (by omega : 2 ≤ R)] at hyoung
  change lowOwnerPost789SignedCrossDiagonalRemainder R ≤
    (1 + (1 / 8 : ℝ)) * (mTop - mRoot) ^ 2 +
      2 * canonicalRoughLowQ2DaughterEnergy R at hyoung
  have hroot : mRoot ^ 2 ≤ 4 * (R : ℝ) * K :=
    vf919RootMertens_sq_le_four_root_envelope hR hK
  have hgap : (mTop - mRoot) ^ 2 ≤
      2 * mTop ^ 2 + 2 * mRoot ^ 2 := by
    nlinarith [sq_nonneg (mTop + mRoot)]
  change lowOwnerPost789SignedCrossDiagonalRemainder R ≤
      2 * canonicalRoughLowQ2DaughterEnergy R +
      (9 / 4 : ℝ) * mTop ^ 2 + 9 * (R : ℝ) * K
  nlinarith

end RHLean.Proof
