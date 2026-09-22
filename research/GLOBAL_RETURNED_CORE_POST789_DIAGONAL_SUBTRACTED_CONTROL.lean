import Mathlib
import «research.GLOBAL_RETURNED_CORE_POST755_AMPLITUDE_CLOSURE»
import «research.GLOBAL_RETURNED_CORE_STOKES_ENDPOINT_AMPLITUDE_IDENTIFICATION»
import «research.GLOBAL_RETURNED_CORE_FINAL_STOKES_RH_BRIDGE»

/-!
# Post-#789 diagonal-subtracted quantitative target

PR #789 showed that the square-endpoint energy must be reassembled before it is
estimated: the missing term is genuine cross-owner covariance, not a new
positive packet.  In the returned-core/Stokes coordinates the same principle is
already visible in the exact identity

  FinalStokes_R = A_R^2 - D_R,

where `A_R` is the single post-#755 global amplitude and `D_R` is the
one-amplitude Mobius diagonal.

The reciprocal q^2 daughter column inside `A_R` already satisfies the sharp
quarter-frame estimate

  Q_R^2 <= (1/4) E_R^(q^2).

Consequently the useful quantitative target is not an upper bound on `A_R^2`
by itself.  Such a bound throws away exactly the diagonal/cross cancellation
that #789 exposed.  Instead define the signed remainder after removing
`Q_R^2`:

  X_R = (M(X_R)-M(R-1))^2
        + 2 Q_R (M(X_R)-M(R-1))
        - D_R.

Then

  FinalStokes_R = Q_R^2 + X_R.

The strongest cancellation target is

  X_R <= -(1/4) E_R^(q^2) + C R^2 K,

which cancels the reciprocal daughter frame completely.  But the existing
correlation consumer only needs coefficient 4.  Passing the final Stokes bound
through the exact AMP inequality sends a remainder coefficient A to correlation
coefficient

  1/2 + 2 * (A + 1/4) = 2*A + 1.

Hence the actual quantitative threshold is only

  A <= 3/2.

This is substantially weaker than full quarter cancellation.  No absolute
value, parent-square estimate, ownerwise square, or frozen coefficient synthesis
appears.

This module name-locks both the exact-cancellation special case and the weaker
A <= 3/2 threshold that is already sufficient for the existing RH consumer.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The signed top-endpoint gap in the orientation used by the post-#755 real
branch amplitude. -/
def lowOwnerPost789EndpointGapReal (R : ℕ) : ℝ :=
  ((mertensSummatoryInt (squareRootEndpoint R) : ℤ) : ℝ) -
    ((mertensSummatoryInt (R - 1) : ℤ) : ℝ)

/-- The exact signed remainder after the reciprocal q^2 column square is
removed from the diagonal-subtracted post-#755 amplitude energy. -/
def lowOwnerPost789SignedCrossDiagonalRemainder (R : ℕ) : ℝ :=
  lowOwnerPost789EndpointGapReal R ^ 2 +
    2 * lowOwnerReciprocalMertensColumnReal R *
      lowOwnerPost789EndpointGapReal R -
    lowOwnerZeroFrequencyMobiusDiagonal R

/-- The post-#755 global amplitude is the reciprocal q^2 daughter column plus
the signed top-endpoint gap. -/
theorem lowOwnerGlobalBranchIncidenceDifferenceAmplitude_eq_reciprocal_add_endpointGap
    {R p r : ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerGlobalBranchIncidenceDifferenceAmplitude R p r =
      lowOwnerReciprocalMertensColumnReal R +
        lowOwnerPost789EndpointGapReal R := by
  rw [lowOwnerGlobalBranchIncidenceDifferenceAmplitude_eq_mertensGap
    hR hp hr hpr]
  unfold lowOwnerPost789EndpointGapReal
  ring

/-- Exact post-#789 energy split: reciprocal q^2 square plus one signed
cross/diagonal remainder. -/
theorem lowOwnerGlobalAmplitudeSq_sub_diagonal_eq_q2Sq_add_post789Remainder
    {R p r : ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerGlobalBranchIncidenceDifferenceAmplitude R p r ^ 2 -
        lowOwnerZeroFrequencyMobiusDiagonal R =
      lowOwnerReciprocalMertensColumnReal R ^ 2 +
        lowOwnerPost789SignedCrossDiagonalRemainder R := by
  rw [lowOwnerGlobalBranchIncidenceDifferenceAmplitude_eq_reciprocal_add_endpointGap
    hR hp hr hpr]
  unfold lowOwnerPost789SignedCrossDiagonalRemainder
  ring

/-- The final signed Stokes boundary is literally the post-#789
diagonal-subtracted global amplitude. -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_post789GlobalAmplitudeSq_sub_diagonal
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      lowOwnerGlobalBranchIncidenceDifferenceAmplitude R 2 3 ^ 2 -
        lowOwnerZeroFrequencyMobiusDiagonal R := by
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_remainderNormSq_sub_diagonal hR]
  rw [← lowOwnerGlobalBranchIncidenceDifferenceAmplitude_sq_eq_remainderNormSq
    hR (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 3)
      (by norm_num : 2 < 3)]

/-- **Exact post-#789 final-boundary normal form.**

The entire final Stokes object is the reciprocal q^2 column square plus the
single signed cross/diagonal remainder. -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_q2Sq_add_post789Remainder
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      lowOwnerReciprocalMertensColumnReal R ^ 2 +
        lowOwnerPost789SignedCrossDiagonalRemainder R := by
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_post789GlobalAmplitudeSq_sub_diagonal
    hR]
  exact
    lowOwnerGlobalAmplitudeSq_sub_diagonal_eq_q2Sq_add_post789Remainder
      (by omega : 2 ≤ R)
      (by norm_num : Nat.Prime 2) (by norm_num : Nat.Prime 3)
      (by norm_num : 2 < 3)

/-- The genuinely recursive LOW q^2 daughter energy is nonnegative. -/
private theorem canonicalRoughLowQ2DaughterEnergy_nonneg_post789 (R : ℕ) :
    0 ≤ canonicalRoughLowQ2DaughterEnergy R := by
  unfold canonicalRoughLowQ2DaughterEnergy
  apply Finset.sum_nonneg
  intro q _hq
  unfold rawQ2ChildEnergyReal
  positivity

/-- Quantitative target with the lower-scale envelope kept live.

The coefficient `A` is allowed to be negative.  The critical target is
`A = -1/4`: it cancels the reciprocal-column quarter-frame exactly. -/
def LowOwnerPost789SignedCrossDiagonalRemainderBound (A C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerPost789SignedCrossDiagonalRemainder R ≤
      A * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- Any signed remainder estimate transfers directly to the final Stokes
boundary, paying only the already-proved `1/4` reciprocal q^2 frame. -/
theorem finalStokesQ2EnergyBound_of_post789SignedRemainderBound
    {A C : ℝ}
    (hRem : LowOwnerPost789SignedCrossDiagonalRemainderBound A C) :
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      lowOwnerCanonicalSignedStokesFinalBoundary R ≤
        (A + 1 / 4) * canonicalRoughLowQ2DaughterEnergy R +
          C * (R : ℝ) ^ 2 * K := by
  intro R K hR hK
  have hQ :=
    lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy R
  have hX := hRem R K hR hK
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_q2Sq_add_post789Remainder
    hR]
  nlinarith

/-- A post-#789 signed remainder estimate gives an AMP remainder estimate
without discarding the diagonal subtraction.  The only extra cost is the
elementary diagonal `D_R <= 3 R^2`, absorbed by the live lower envelope
`K >= 1`. -/
theorem physicalAmplitudeRemainderQ2EnergyBound_of_post789SignedRemainderBound
    {A C : ℝ}
    (hRem : LowOwnerPost789SignedCrossDiagonalRemainderBound A C) :
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 ≤
        (A + 1 / 4) * canonicalRoughLowQ2DaughterEnergy R +
          (C + 3) * (R : ℝ) ^ 2 * K := by
  intro R K hR hK
  have hFinal :=
    finalStokesQ2EnergyBound_of_post789SignedRemainderBound hRem
      R K hR hK
  have hDiag := lowOwnerZeroFrequencyMobiusDiagonal_le_three_root_sq R
  have hK1 : 1 ≤ K := by
    have h0 := hK.2 0 (by omega)
    have hm0 : mertensSummatoryInt 0 = 0 := by
      simp [mertensSummatoryInt]
    rw [hm0] at h0
    norm_num at h0
  have hR2 : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
  have hDiagK :
      lowOwnerZeroFrequencyMobiusDiagonal R ≤
        3 * (R : ℝ) ^ 2 * K := by
    calc
      lowOwnerZeroFrequencyMobiusDiagonal R ≤
          3 * (R : ℝ) ^ 2 := hDiag
      _ ≤ 3 * (R : ℝ) ^ 2 * K := by
        nlinarith
  have hIdentity :=
    lowOwnerCanonicalSignedStokesFinalBoundary_eq_remainderNormSq_sub_diagonal
      hR
  rw [hIdentity] at hFinal
  nlinarith

/-- Passing the post-#789 remainder through the exact AMP transport sends
daughter coefficient `A` to correlation coefficient `2*A + 1`.  This is the
key quantitative conversion: the reciprocal quarter frame and the AMP
one-half/two-square inequality are accounted for exactly. -/
theorem correlationLowQ2Energy_of_post789SignedRemainderBound
    {A C : ℝ}
    (hRem : LowOwnerPost789SignedCrossDiagonalRemainderBound A C) :
    CanonicalRoughCorrelationLowQ2EnergyStatementWith
      (2 * A + 1) (2 * (C + 3)) := by
  intro R K hR hK
  have hCorr :=
    correlation_energy_le_half_lowEnergy_add_twice_physicalRemainder
      R hR 0
  have hAmp :=
    physicalAmplitudeRemainderQ2EnergyBound_of_post789SignedRemainderBound
      hRem R K hR hK
  nlinarith

/-- **Relaxed post-#789 closure corridor.**

For `-1/4 <= A <= 3/2`, the induced correlation coefficient satisfies

  0 <= 2*A + 1 <= 4.

The low-q^2 estimate therefore localizes to the full daughter family and fits
the already-compiled CORR-4 terminal interface. -/
theorem correlationFour_of_post789SignedRemainderBound
    {A C : ℝ}
    (hAlo : -1 / 4 ≤ A) (hAhi : A ≤ 3 / 2) (hC : 0 ≤ C)
    (hRem : LowOwnerPost789SignedCrossDiagonalRemainderBound A C) :
    CanonicalRoughCorrelationFourQ2EnergyStatement := by
  let C0 : ℝ := 2 * (C + 3)
  have hCoeff0 : 0 ≤ 2 * A + 1 := by
    nlinarith
  have hLow :=
    correlationLowQ2Energy_of_post789SignedRemainderBound hRem
  have hFull :
      CanonicalRoughCorrelationQ2EnergyStatementWith (2 * A + 1) C0 := by
    simpa [C0] using correlationLowQ2Energy_implies_full hCoeff0 hLow
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    nlinarith
  refine ⟨C0, hC0, ?_⟩
  intro R K hR hK
  have h := hFull R K hR hK
  have hE : 0 ≤ farFourOddQ2DaughterEnergy R := by
    unfold farFourOddQ2DaughterEnergy
    apply Finset.sum_nonneg
    intro q _hq
    unfold rawQ2ChildEnergyReal
    positivity
  have hCoeff : 2 * A + 1 ≤ 4 := by
    nlinarith
  have hMono :
      (2 * A + 1) * farFourOddQ2DaughterEnergy R ≤
        4 * farFourOddQ2DaughterEnergy R :=
    mul_le_mul_of_nonneg_right hCoeff hE
  exact h.trans (add_le_add_right hMono _)

/-- In the relaxed corridor the post-#789 signed remainder already implies RH.
No complete cancellation of the recursive q^2 daughter energy is required. -/
theorem riemannHypothesis_of_post789CorridorRemainderBound
    {A C : ℝ}
    (hAlo : -1 / 4 ≤ A) (hAhi : A ≤ 3 / 2) (hC : 0 ≤ C)
    (hRem : LowOwnerPost789SignedCrossDiagonalRemainderBound A C) :
    RiemannHypothesis :=
  riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy
    (correlationFour_of_post789SignedRemainderBound
      hAlo hAhi hC hRem)

/-- **Quarter-cancellation closure.**

If the signed cross/diagonal remainder contributes at most minus one quarter of
the recursive q^2 daughter energy (up to the allowed root-scale envelope), then
the daughter energy cancels completely and the final Stokes bound follows with
the same root-scale constant. -/
theorem finalStokesBoundaryBound_of_post789QuarterCancellation
    {C : ℝ}
    (hRem :
      LowOwnerPost789SignedCrossDiagonalRemainderBound (-1 / 4) C) :
    LowOwnerFinalStokesBoundaryBound C := by
  intro R K hR hK
  have h :=
    finalStokesQ2EnergyBound_of_post789SignedRemainderBound hRem
      R K hR hK
  norm_num at h ⊢
  exact h

/-- More generally, any coefficient at most `-1/4` closes the final Stokes
bound; extra negative daughter energy is harmless. -/
theorem finalStokesBoundaryBound_of_post789SubquarterCancellation
    {A C : ℝ} (hA : A ≤ -1 / 4)
    (hRem : LowOwnerPost789SignedCrossDiagonalRemainderBound A C) :
    LowOwnerFinalStokesBoundaryBound C := by
  intro R K hR hK
  have h :=
    finalStokesQ2EnergyBound_of_post789SignedRemainderBound hRem
      R K hR hK
  have hE := canonicalRoughLowQ2DaughterEnergy_nonneg_post789 R
  have hcoef : A + 1 / 4 ≤ 0 := by linarith
  have hnonpos :
      (A + 1 / 4) * canonicalRoughLowQ2DaughterEnergy R ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcoef hE
  linarith

/-- **Sharp sufficient coefficient threshold.**

Any post-#789 signed remainder coefficient `A <= 3/2` is sufficient.  If
`A <= -1/4`, the final Stokes daughter term cancels directly.  Otherwise
`-1/4 < A <= 3/2` lies in the relaxed CORR-4 corridor above. -/
theorem riemannHypothesis_of_post789SignedRemainderBound
    {A C : ℝ} (hA : A ≤ 3 / 2) (hC : 0 ≤ C)
    (hRem : LowOwnerPost789SignedCrossDiagonalRemainderBound A C) :
    RiemannHypothesis := by
  by_cases hQuarter : A ≤ -1 / 4
  · exact riemannHypothesis_of_finalStokesBoundaryBound hC
      (finalStokesBoundaryBound_of_post789SubquarterCancellation
        hQuarter hRem)
  · have hAlo : -1 / 4 ≤ A := by
      exact le_of_lt (not_le.mp hQuarter)
    exact riemannHypothesis_of_post789CorridorRemainderBound
      hAlo hA hC hRem

/-- **Direct RH closure from the post-#789 signed remainder.** -/
theorem riemannHypothesis_of_post789QuarterCancellation
    {C : ℝ} (hC : 0 ≤ C)
    (hRem :
      LowOwnerPost789SignedCrossDiagonalRemainderBound (-1 / 4) C) :
    RiemannHypothesis :=
  riemannHypothesis_of_finalStokesBoundaryBound hC
    (finalStokesBoundaryBound_of_post789QuarterCancellation hRem)

end RHLean.Proof
