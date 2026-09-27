import Mathlib
import «research.GLOBAL_RETURNED_CORE_TOP_TWO_COMPLETED_BRANCH_ASSEMBLY»

/-!
# The post-#789 signed remainder is the CORR square in disguise

PR #796 composed the completed Dirichlet branch energy with the global
top-two Stokes Fubini and obtained exactly

  TopCompletedBranchAssembly_R = Q_R^2 + X_R,
  X_R = G_R^2 + 2 Q_R G_R - D_R,
  G_R = M(R^2 - 1) - M(R - 1).

This file checks whether `X_R` is a genuinely smaller remainder.  It is not.
The canonical rough correlation already satisfies, by a compiled identity,

  corr_R = M(R - 1) - M(R^2 - 1) = -G_R,

so `G_R^2` is literally the square consumed by the CORR-4 terminal interface.
With only the quarter frame `Q_R^2 <= E_R/4` and the diagonal bounds
`0 <= D_R <= 3 R^2`, the remainder is pinned to that square from both sides:

  (1/2) corr_R^2 - (1/2) E_R - 3 R^2 <= X_R <= (1 + a) corr_R^2 + b E_R,

for every `a > 0`, `4 a b = 1`.

Consequences recorded below:

* any post-#789 bound with coefficient `A` forces the CORR square with
  coefficient `2 A + 1` (this recovers the compiled AMP transfer without AMP);
* conversely CORR-low `(beta, c)` gives a post-#789 bound with coefficient
  `(1 + a) beta + b`; in particular CORR-low `1/2` lands at `5/4`, inside the
  original `A <= 3/2` corridor;
* hence "some post-#789 bound" and "some CORR-low bound" are the same
  existence statement, and the #796 completed-branch assembly dominates half
  of the top-endpoint Mertens square up to `E_R/2` and root scale.

The 2026-09-27 sharpening at the end of this module also gives

  (3/4) corr_R^2 - E_R - 3 R^2 <= X_R,
  (3/4) corr_R^2 - (3/4) E_R - 3 R^2 <= FinalStokes_R.

These transfers admit remainder coefficient `2` and final-Stokes coefficient
`9/4`, respectively, at CORR coefficient `4`. The earlier theorems remain
unchanged. This improves sufficient coefficients, not the arithmetic scale:
no uniform upper estimate for the remainder or final Stokes term is proved.

This is an exact carrier audit.  It proves no contraction.  The remaining
quantitative seam is exactly the top-endpoint correlation estimate already
consumed by `riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy`; the
branch completion and top-two Stokes composition did not remove it.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The canonical rough correlation is the negative post-#789 endpoint gap. -/
theorem squareRootCanonicalRoughCorrelation_eq_neg_post789EndpointGap
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootCanonicalRoughCorrelation R =
      ((-lowOwnerPost789EndpointGapReal R : ℝ) : ℂ) := by
  rw [squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint R hR,
    ← mertensSummatoryInt_cast (R - 1),
    ← mertensSummatoryInt_cast (squareRootEndpoint R)]
  unfold lowOwnerPost789EndpointGapReal
  push_cast
  ring

/-- The CORR square is exactly the post-#789 endpoint-gap square. -/
theorem norm_sq_squareRootCanonicalRoughCorrelation_eq_post789EndpointGap_sq
    {R : ℕ} (hR : 2 ≤ R) :
    ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 =
      lowOwnerPost789EndpointGapReal R ^ 2 := by
  rw [squareRootCanonicalRoughCorrelation_eq_neg_post789EndpointGap hR,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, neg_sq]

/-- **Exact dictionary.** The signed remainder is the CORR square plus the
reciprocal-column cross term minus the Möbius diagonal. -/
theorem lowOwnerPost789SignedCrossDiagonalRemainder_eq_correlationSq_add_cross_sub_diagonal
    {R : ℕ} (hR : 2 ≤ R) :
    lowOwnerPost789SignedCrossDiagonalRemainder R =
      ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 +
        2 * lowOwnerReciprocalMertensColumnReal R *
          lowOwnerPost789EndpointGapReal R -
        lowOwnerZeroFrequencyMobiusDiagonal R := by
  unfold lowOwnerPost789SignedCrossDiagonalRemainder
  rw [norm_sq_squareRootCanonicalRoughCorrelation_eq_post789EndpointGap_sq hR]

private theorem lowOwnerZeroFrequencyMobiusDiagonal_nonneg_corrEquiv
    (R : ℕ) :
    0 ≤ lowOwnerZeroFrequencyMobiusDiagonal R := by
  unfold lowOwnerZeroFrequencyMobiusDiagonal signedBlockEnergy
  apply Finset.sum_nonneg
  intro j _hj
  positivity

/-- **The remainder is not lower order.** Half of the top-endpoint CORR
square survives in `X_R`, up to half the q² energy and root scale. -/
theorem half_correlationSq_sub_le_post789SignedRemainder
    {R : ℕ} (hR : 2 ≤ R) :
    (1 / 2 : ℝ) * ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 -
        (1 / 2 : ℝ) * canonicalRoughLowQ2DaughterEnergy R -
        3 * (R : ℝ) ^ 2 ≤
      lowOwnerPost789SignedCrossDiagonalRemainder R := by
  rw [lowOwnerPost789SignedCrossDiagonalRemainder_eq_correlationSq_add_cross_sub_diagonal
      hR,
    norm_sq_squareRootCanonicalRoughCorrelation_eq_post789EndpointGap_sq hR]
  have hQ :=
    lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy R
  have hD := lowOwnerZeroFrequencyMobiusDiagonal_le_three_root_sq R
  nlinarith [sq_nonneg (lowOwnerPost789EndpointGapReal R +
    2 * lowOwnerReciprocalMertensColumnReal R)]

/-- **Young upper comparison.** For `a > 0` and `4 a b = 1`, the remainder is
at most `(1 + a)` CORR squares plus `b` q² energies.  The diagonal is dropped
only in the favorable direction. -/
theorem post789SignedRemainder_le_correlationSq_young
    {R : ℕ} (hR : 2 ≤ R) {a b : ℝ} (ha : 0 < a) (hab : 4 * a * b = 1) :
    lowOwnerPost789SignedCrossDiagonalRemainder R ≤
      (1 + a) * ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 +
        b * canonicalRoughLowQ2DaughterEnergy R := by
  rw [lowOwnerPost789SignedCrossDiagonalRemainder_eq_correlationSq_add_cross_sub_diagonal
      hR,
    norm_sq_squareRootCanonicalRoughCorrelation_eq_post789EndpointGap_sq hR]
  have hQ :=
    lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy R
  have hD := lowOwnerZeroFrequencyMobiusDiagonal_nonneg_corrEquiv R
  set G := lowOwnerPost789EndpointGapReal R
  set Q := lowOwnerReciprocalMertensColumnReal R
  set E := canonicalRoughLowQ2DaughterEnergy R
  have hsq : 0 ≤ (2 * a * G - 2 * Q) ^ 2 + (E - 4 * Q ^ 2) := by
    have h := sq_nonneg (2 * a * G - 2 * Q)
    linarith
  have hid : (2 * a * G - 2 * Q) ^ 2 + (E - 4 * Q ^ 2) =
      4 * a * (a * G ^ 2 + b * E - 2 * Q * G) := by
    linear_combination (-E) * hab
  have hscaled : 0 ≤ 4 * a * (a * G ^ 2 + b * E - 2 * Q * G) := by
    rw [← hid]
    exact hsq
  have hcross : 0 ≤ a * G ^ 2 + b * E - 2 * Q * G := by
    by_contra hneg
    push_neg at hneg
    have h4a : (0 : ℝ) < 4 * a := by linarith
    have := mul_neg_of_pos_of_neg h4a hneg
    linarith
  nlinarith [hcross, hD]

/-- Any post-#789 signed remainder bound forces the top-endpoint CORR square
directly, with the same coefficient `2 A + 1` as the compiled AMP transfer. -/
theorem correlationSq_le_of_post789SignedRemainderBound
    {A C : ℝ}
    (hRem : LowOwnerPost789SignedCrossDiagonalRemainderBound A C) :
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
        (2 * A + 1) * canonicalRoughLowQ2DaughterEnergy R +
          (2 * C + 6) * (R : ℝ) ^ 2 * K := by
  intro R K hR hK
  have hLow := half_correlationSq_sub_le_post789SignedRemainder
    (R := R) (by omega)
  have hX := hRem R K hR hK
  have hK1 : 1 ≤ K := by
    have h0 := hK.2 0 (by omega)
    have hm0 : mertensSummatoryInt 0 = 0 := by
      simp [mertensSummatoryInt]
    rw [hm0] at h0
    norm_num at h0
    exact h0
  have hR2 : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
  have hRK : (R : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 * K := by
    nlinarith [mul_nonneg hR2 (sub_nonneg.mpr hK1)]
  nlinarith [hLow, hX, hRK]

/-- **Converse transfer.** A CORR-low estimate gives a post-#789 signed
remainder estimate, for every Young split `a > 0`, `4 a b = 1`. -/
theorem post789SignedRemainderBound_of_correlationLowQ2Energy
    {beta c a b : ℝ} (ha : 0 < a) (hab : 4 * a * b = 1)
    (hCorr : CanonicalRoughCorrelationLowQ2EnergyStatementWith beta c) :
    LowOwnerPost789SignedCrossDiagonalRemainderBound
      ((1 + a) * beta + b) ((1 + a) * c) := by
  intro R K hR hK
  have hX := post789SignedRemainder_le_correlationSq_young
    (R := R) (by omega) ha hab
  have hC := hCorr R K hR hK
  have h1a : 0 ≤ 1 + a := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hC h1a
  nlinarith [hX, hscaled]

/-- **No quantitative narrowing.** Some post-#789 signed remainder bound
exists exactly when some CORR-low bound exists. -/
theorem exists_post789SignedRemainderBound_iff_exists_correlationLowQ2Energy :
    (∃ A C : ℝ, 0 ≤ C ∧
        LowOwnerPost789SignedCrossDiagonalRemainderBound A C) ↔
      (∃ beta c : ℝ, 0 ≤ c ∧
        CanonicalRoughCorrelationLowQ2EnergyStatementWith beta c) := by
  constructor
  · rintro ⟨A, C, hC, hRem⟩
    exact ⟨2 * A + 1, 2 * (C + 3), by linarith,
      correlationLowQ2Energy_of_post789SignedRemainderBound hRem⟩
  · rintro ⟨beta, c, hc, hCorr⟩
    exact ⟨(1 + 1 / 2) * beta + 1 / 2, (1 + 1 / 2) * c,
      mul_nonneg (by norm_num) hc,
      post789SignedRemainderBound_of_correlationLowQ2Energy
        (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) hCorr⟩

/-- CORR-low with coefficient `1/2` lands inside the post-#789 `3/2`
corridor, at coefficient `5/4`. -/
theorem post789SignedRemainderBound_fiveQuarters_of_correlationLowHalf
    {c : ℝ}
    (hCorr : CanonicalRoughCorrelationLowQ2EnergyStatementWith (1 / 2) c) :
    LowOwnerPost789SignedCrossDiagonalRemainderBound (5 / 4) ((3 / 2) * c) := by
  have h := post789SignedRemainderBound_of_correlationLowQ2Energy
    (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) hCorr
  intro R K hR hK
  have hR' := h R K hR hK
  linarith

/-- **Corridor sandwich.** The RH-sufficient post-#789 corridor sits between
two CORR-low statements of the same top-endpoint type: CORR-low `1/2` implies
it, and it implies CORR-low `2 A + 1 <= 4`. -/
theorem post789Corridor_sandwich
    {A C : ℝ} (hA : A ≤ 3 / 2)
    (hRem : LowOwnerPost789SignedCrossDiagonalRemainderBound A C) :
    CanonicalRoughCorrelationLowQ2EnergyStatementWith
        (2 * A + 1) (2 * (C + 3)) ∧
      2 * A + 1 ≤ 4 :=
  ⟨correlationLowQ2Energy_of_post789SignedRemainderBound hRem, by linarith⟩

/-- **The #796 completed-branch assembly dominates the top Mertens square.**
Up to half the q² energy and root scale, any upper bound on the completed
branch / top-two assembly is an upper bound on half of
`(M(R^2 - 1) - M(R - 1))^2`. -/
theorem half_correlationSq_le_topCompletedBranchAssembly_add
    {R : ℕ} (hR : 56 ≤ R) :
    (1 / 2 : ℝ) * ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
      lowOwnerTopCompletedBranchAssembly R hR +
        (1 / 2 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        3 * (R : ℝ) ^ 2 := by
  rw [lowOwnerTopCompletedBranchAssembly_eq_q2Sq_add_signedRemainder hR]
  have h := half_correlationSq_sub_le_post789SignedRemainder
    (R := R) (by omega)
  have hQ := sq_nonneg (lowOwnerReciprocalMertensColumnReal R)
  linarith

/-! ## Sharpened coefficient transfers, 2026-09-27

These are unconditional algebraic comparisons followed by conditional
consumers. They do not assert either uniform arithmetic upper bound.
-/

/-- Exact square certificate for the three-quarter remainder comparison. -/
theorem post789_remainder_threeQuarters_certificate (G Q E D r : ℝ) :
    (G ^ 2 + 2 * Q * G - D) -
        ((3 / 4 : ℝ) * G ^ 2 - E - 3 * r ^ 2) =
      (1 / 4 : ℝ) * (G + 4 * Q) ^ 2 +
        (E - 4 * Q ^ 2) + (3 * r ^ 2 - D) := by
  ring

/-- Exact square certificate for the three-quarter final-Stokes comparison. -/
theorem post789_finalStokes_threeQuarters_certificate (G Q E D : ℝ) :
    4 * ((G + Q) ^ 2 - D) - 3 * G ^ 2 + 3 * E + 4 * D =
      (G + 4 * Q) ^ 2 + 3 * (E - 4 * Q ^ 2) := by
  ring

/-- A different square completion retains three quarters of the CORR square,
with one daughter energy and the same diagonal budget. -/
theorem threeQuarters_correlationSq_sub_le_post789SignedRemainder
    {R : ℕ} (hR : 2 ≤ R) :
    (3 / 4 : ℝ) * ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 -
        canonicalRoughLowQ2DaughterEnergy R - 3 * (R : ℝ) ^ 2 ≤
      lowOwnerPost789SignedCrossDiagonalRemainder R := by
  rw [norm_sq_squareRootCanonicalRoughCorrelation_eq_post789EndpointGap_sq hR]
  unfold lowOwnerPost789SignedCrossDiagonalRemainder
  have hQ :=
    lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy R
  have hD := lowOwnerZeroFrequencyMobiusDiagonal_le_three_root_sq R
  nlinarith [sq_nonneg (lowOwnerPost789EndpointGapReal R +
    4 * lowOwnerReciprocalMertensColumnReal R)]

/-- The final-Stokes comparison retains its actual reciprocal square rather
than dropping it before completing the square. -/
theorem threeQuarters_correlationSq_sub_le_finalStokes
    {R : ℕ} (hR : 56 ≤ R) :
    (3 / 4 : ℝ) * ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 -
        (3 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R -
        3 * (R : ℝ) ^ 2 ≤
      lowOwnerCanonicalSignedStokesFinalBoundary R := by
  rw [norm_sq_squareRootCanonicalRoughCorrelation_eq_post789EndpointGap_sq
      (by omega : 2 ≤ R),
    lowOwnerCanonicalSignedStokesFinalBoundary_eq_q2Sq_add_post789Remainder hR]
  unfold lowOwnerPost789SignedCrossDiagonalRemainder
  have hQ :=
    lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy R
  have hD := lowOwnerZeroFrequencyMobiusDiagonal_le_three_root_sq R
  nlinarith [sq_nonneg (lowOwnerPost789EndpointGapReal R +
    4 * lowOwnerReciprocalMertensColumnReal R)]

private theorem root_sq_le_lowerEnvelope_scale_corrEquiv
    {R : ℕ} {K : ℝ} (hR : 1 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    (R : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 * K := by
  have hK1 : 1 ≤ K := by
    have h0 := hK.2 0 (by omega)
    have hm0 : mertensSummatoryInt 0 = 0 := by
      simp [mertensSummatoryInt]
    rw [hm0] at h0
    norm_num at h0
    exact h0
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left hK1 (sq_nonneg (R : ℝ)))

/-- Sharpened remainder transfer: `A` maps to `4*(A+1)/3`, with boundary
constant `4*C/3+4`. The upper bound remains an explicit hypothesis. -/
theorem correlationLowQ2Energy_of_post789SignedRemainderBound_threeQuarters
    {A C : ℝ}
    (hRem : LowOwnerPost789SignedCrossDiagonalRemainderBound A C) :
    CanonicalRoughCorrelationLowQ2EnergyStatementWith
      ((4 / 3 : ℝ) * (A + 1)) ((4 / 3 : ℝ) * C + 4) := by
  intro R K hR hK
  have hLow := threeQuarters_correlationSq_sub_le_post789SignedRemainder
    (R := R) (by omega)
  have hUpper := hRem R K hR hK
  have hScale := root_sq_le_lowerEnvelope_scale_corrEquiv
    (by omega : 1 ≤ R) hK
  nlinarith [hLow, hUpper, hScale]

/-- Sharpened final-Stokes transfer: `B` maps to `4*B/3+1`, with boundary
constant `4*C/3+4`. No unsigned ownerwise estimate is introduced. -/
theorem correlationLowQ2Energy_of_finalStokesQ2EnergyBound_threeQuarters
    {B C : ℝ}
    (hFinal : LowOwnerFinalStokesQ2EnergyBound B C) :
    CanonicalRoughCorrelationLowQ2EnergyStatementWith
      ((4 / 3 : ℝ) * B + 1) ((4 / 3 : ℝ) * C + 4) := by
  intro R K hR hK
  have hLow := threeQuarters_correlationSq_sub_le_finalStokes hR
  have hUpper := hFinal R K hR hK
  have hScale := root_sq_le_lowerEnvelope_scale_corrEquiv
    (by omega : 1 ≤ R) hK
  nlinarith [hLow, hUpper, hScale]

/-- A uniform signed remainder bound with coefficient `2` suffices for CORR-4. -/
theorem correlationFour_of_post789SignedRemainderBound_two
    {C : ℝ} (hC : 0 ≤ C)
    (hRem : LowOwnerPost789SignedCrossDiagonalRemainderBound 2 C) :
    CanonicalRoughCorrelationFourQ2EnergyStatement := by
  apply correlationFour_iff_exists_lowQ2Energy.mpr
  refine ⟨(4 / 3 : ℝ) * C + 4, by positivity, ?_⟩
  have hLow :=
    correlationLowQ2Energy_of_post789SignedRemainderBound_threeQuarters hRem
  convert hLow using 1 <;> norm_num

/-- A uniform final-Stokes bound with coefficient `9/4` suffices for CORR-4. -/
theorem correlationFour_of_finalStokesQ2EnergyBound_nineQuarters
    {C : ℝ} (hC : 0 ≤ C)
    (hFinal : LowOwnerFinalStokesQ2EnergyBound (9 / 4) C) :
    CanonicalRoughCorrelationFourQ2EnergyStatement := by
  apply correlationFour_iff_exists_lowQ2Energy.mpr
  refine ⟨(4 / 3 : ℝ) * C + 4, by positivity, ?_⟩
  have hLow :=
    correlationLowQ2Energy_of_finalStokesQ2EnergyBound_threeQuarters hFinal
  convert hLow using 1 <;> norm_num

/-- Conditional closure at the relaxed remainder coefficient `2`. -/
theorem riemannHypothesis_of_post789SignedRemainderBound_two
    {C : ℝ} (hC : 0 ≤ C)
    (hRem : LowOwnerPost789SignedCrossDiagonalRemainderBound 2 C) :
    RiemannHypothesis :=
  riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy
    (correlationFour_of_post789SignedRemainderBound_two hC hRem)

/-- Conditional closure at the relaxed final-Stokes coefficient `9/4`. -/
theorem riemannHypothesis_of_finalStokesQ2EnergyBound_nineQuarters
    {C : ℝ} (hC : 0 ≤ C)
    (hFinal : LowOwnerFinalStokesQ2EnergyBound (9 / 4) C) :
    RiemannHypothesis :=
  riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy
    (correlationFour_of_finalStokesQ2EnergyBound_nineQuarters hC hFinal)

end RHLean.Proof
