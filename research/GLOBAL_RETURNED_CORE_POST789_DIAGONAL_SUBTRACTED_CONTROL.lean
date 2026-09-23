import Mathlib
import «research.GLOBAL_RETURNED_CORE_POST755_AMPLITUDE_CLOSURE»
import «research.GLOBAL_RETURNED_CORE_STOKES_ENDPOINT_AMPLITUDE_IDENTIFICATION»
import «research.GLOBAL_RETURNED_CORE_FINAL_STOKES_RH_BRIDGE»
import «research.GLOBAL_RETURNED_CORE_STOKES_ZERO_TARGET_COVARIANCE»
import «research.GLOBAL_RETURNED_CORE_RECIPROCAL_WALL_DESCENDING_ENERGY»
import «research.LOW_OWNER_RETURNED_AMPLITUDE_CORE»

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

/-- Quantitative target on the coupled returned amplitude core.  This is the
zero-target owner-descent surface: the q-owner physical memory packet is exactly
its negative before the root correction is restored. -/
def LowOwnerReturnedCoreQ2EnergyBound (A C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    ‖lowOwnerReturnedAmplitudeCore R‖ ^ 2 ≤
      A * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- Asymmetric Young inequality tuned so a returned-core coefficient `3/2`
becomes exactly the admissible final-Stokes coefficient `7/4`. -/
private theorem norm_add_sq_le_seven_six_seven (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤
      (7 / 6 : ℝ) * ‖u‖ ^ 2 + 7 * ‖v‖ ^ 2 := by
  have htri : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
  have hnon : 0 ≤ ‖u + v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u‖ + ‖v‖ := by positivity
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg (‖u‖ - 6 * ‖v‖)]

/-- Quantitative final-Stokes target with the recursive q^2 energy kept live. -/
def LowOwnerFinalStokesQ2EnergyBound (B C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerCanonicalSignedStokesFinalBoundary R ≤
      B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- Direct zero-target cross-Gram target.  Since FinalStokes is exactly twice
the off-diagonal target-zero co-partial-minus-divergent excess, this is the
diagonal-free quantitative surface on which first-separation owner descent
should act. -/
def LowOwnerZeroTargetCrossQ2EnergyBound (B C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    (zeroTargetCoPartialCross
        (lowOwnerZeroFrequencyMobiusSite R)
        (squareRootEndpoint R + 1) -
      zeroTargetDivergentCross
        (lowOwnerZeroFrequencyMobiusSite R)
        (squareRootEndpoint R + 1)) ≤
      B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- **Exact coefficient dictionary for the zero-target attack.**

A cross-Gram coefficient `B` is exactly a FinalStokes coefficient `2B`.
No diagonal, root correction, owner norm, or support estimate enters. -/
theorem zeroTargetCrossQ2EnergyBound_iff_finalStokesQ2EnergyBound
    (B C : ℝ) :
    LowOwnerZeroTargetCrossQ2EnergyBound B C ↔
      LowOwnerFinalStokesQ2EnergyBound (2 * B) (2 * C) := by
  constructor
  · intro h R K hR hK
    have hx := h R K hR hK
    rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_two_zeroTargetCrossExcess
      (R := R) (by omega : 2 ≤ R)]
    nlinarith
  · intro h R K hR hK
    have hf := h R K hR hK
    rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_two_zeroTargetCrossExcess
      (R := R) (by omega : 2 ≤ R)] at hf
    nlinarith

/-- **Returned-core 3/2 -> final-Stokes 7/4.**

The exact q-memory identity gives
`AMP_R = -ReturnedCore_R - Root_R`, with `||Root_R|| <= 8 R`.
Applying the tuned Young inequality above sends `3/2` to
`(7/6)*(3/2)=7/4`; the root contribution is only `448 R^2`.
The nonnegative Möbius diagonal is then discarded in the favorable direction.

Thus the zero-target returned-core analysis only needs recursive coefficient
`3/2`, not a root-scale bound and not FAR-3/FAR-4. -/
theorem finalStokesQ2EnergyBound_of_returnedCoreThreeHalves
    {C : ℝ}
    (hCore : LowOwnerReturnedCoreQ2EnergyBound (3 / 2) C) :
    LowOwnerFinalStokesQ2EnergyBound
      (7 / 4) ((7 / 6) * C + 448) := by
  intro R K hR hK
  have hCoreR := hCore R K hR hK
  have hRoot :=
    norm_returnedAmplitudeRootCorrection_le_eight_root R hR
  have hRootSq :
      ‖frozenTopFarRoughRootCorrection R‖ ^ 2 ≤
        64 * (R : ℝ) ^ 2 := by
    have hn : 0 ≤ ‖frozenTopFarRoughRootCorrection R‖ := norm_nonneg _
    have hR0 : 0 ≤ (R : ℝ) := by positivity
    nlinarith [sq_nonneg
      (8 * (R : ℝ) - ‖frozenTopFarRoughRootCorrection R‖)]
  have hYoung :=
    norm_add_sq_le_seven_six_seven
      (-lowOwnerReturnedAmplitudeCore R)
      (-frozenTopFarRoughRootCorrection R)
  simp only [norm_neg] at hYoung
  have hAmpRepr :=
    lowOwnerPhysicalAmplitudeRemainder_zero_eq_neg_returnedCore_sub_root
      R hR
  have hAmp :
      ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 ≤
        (7 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
          ((7 / 6 : ℝ) * C + 448) * (R : ℝ) ^ 2 * K := by
    have hK1 : 1 ≤ K := by
      have h0 := hK.2 0 (by omega)
      have hm0 : mertensSummatoryInt 0 = 0 := by
        simp [mertensSummatoryInt]
      rw [hm0] at h0
      norm_num at h0
      exact h0
    have hYoungAmp :
        ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 ≤
          (7 / 6 : ℝ) * ‖lowOwnerReturnedAmplitudeCore R‖ ^ 2 +
            7 * ‖frozenTopFarRoughRootCorrection R‖ ^ 2 := by
      rw [hAmpRepr]
      simpa [sub_eq_add_neg] using hYoung
    have hR2 : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hdiag0 : 0 ≤ lowOwnerZeroFrequencyMobiusDiagonal R := by
    unfold lowOwnerZeroFrequencyMobiusDiagonal signedBlockEnergy
    apply Finset.sum_nonneg
    intro j _hj
    positivity
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_remainderNormSq_sub_diagonal
    hR]
  linarith

/-- The same target in the exact signed-cell/unique-owner currency.  This is
the quantitative endpoint that the one-sided owner recursion should prove:
the signed cell telescope is allowed a recursive q^2 term instead of being
forced to root scale outright. -/
def LowOwnerSignedCellQ2EnergyAssemblyBound (B C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig) ≤
      B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- The signed-cell target and the final-Stokes target are literally the same
inequality; no estimate or ownerwise norm is used in the transfer. -/
theorem signedCellQ2EnergyAssemblyBound_iff_finalStokesQ2EnergyBound
    (B C : ℝ) :
    LowOwnerSignedCellQ2EnergyAssemblyBound B C ↔
      LowOwnerFinalStokesQ2EnergyBound B C := by
  constructor
  · intro h R K hR hK
    have hs := h R K hR hK
    rw [sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary
      (R := R) (by omega : 2 ≤ R)] at hs
    exact hs
  · intro h R K hR hK
    have hs := h R K hR hK
    rw [← sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary
      (R := R) (by omega : 2 ≤ R)] at hs
    exact hs

/-- A final-Stokes q^2 estimate transfers through the exact AMP identity.
The elementary diagonal costs only `3 R^2 K`. -/
theorem physicalAmplitudeRemainderQ2EnergyBound_of_finalStokesQ2EnergyBound
    {B C : ℝ}
    (hFinal : LowOwnerFinalStokesQ2EnergyBound B C) :
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 ≤
        B * canonicalRoughLowQ2DaughterEnergy R +
          (C + 3) * (R : ℝ) ^ 2 * K := by
  intro R K hR hK
  have h := hFinal R K hR hK
  have hDiag := lowOwnerZeroFrequencyMobiusDiagonal_le_three_root_sq R
  have hK1 : 1 ≤ K := by
    have h0 := hK.2 0 (by omega)
    have hm0 : mertensSummatoryInt 0 = 0 := by
      simp [mertensSummatoryInt]
    rw [hm0] at h0
    norm_num at h0
    exact h0
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
  rw [hIdentity] at h
  nlinarith

/-- Passing a final-Stokes coefficient `B` through AMP gives correlation
coefficient `1/2 + 2B`. -/
theorem correlationLowQ2Energy_of_finalStokesQ2EnergyBound
    {B C : ℝ}
    (hFinal : LowOwnerFinalStokesQ2EnergyBound B C) :
    CanonicalRoughCorrelationLowQ2EnergyStatementWith
      (1 / 2 + 2 * B) (2 * (C + 3)) := by
  intro R K hR hK
  have hCorr :=
    correlation_energy_le_half_lowEnergy_add_twice_physicalRemainder
      R hR 0
  have hAmp :=
    physicalAmplitudeRemainderQ2EnergyBound_of_finalStokesQ2EnergyBound
      hFinal R K hR hK
  nlinarith

/-- **The actual signed-cell coefficient threshold.**

Any globally assembled signed-cell estimate with
`-1/4 <= B <= 7/4` fits the existing CORR-4 consumer.  In particular the
owner recursion only needs coefficient `7/4`; a root-scale-only Stokes bound
is far stronger than necessary. -/
theorem correlationFour_of_finalStokesQ2EnergyBound
    {B C : ℝ}
    (hBlo : -1 / 4 ≤ B) (hBhi : B ≤ 7 / 4) (hC : 0 ≤ C)
    (hFinal : LowOwnerFinalStokesQ2EnergyBound B C) :
    CanonicalRoughCorrelationFourQ2EnergyStatement := by
  let C0 : ℝ := 2 * (C + 3)
  have hCoeff0 : 0 ≤ 1 / 2 + 2 * B := by
    nlinarith
  have hLow :=
    correlationLowQ2Energy_of_finalStokesQ2EnergyBound hFinal
  have hFull :
      CanonicalRoughCorrelationQ2EnergyStatementWith
        (1 / 2 + 2 * B) C0 := by
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
  have hCoeff : 1 / 2 + 2 * B ≤ 4 := by
    nlinarith
  have hMono :
      (1 / 2 + 2 * B) * farFourOddQ2DaughterEnergy R ≤
        4 * farFourOddQ2DaughterEnergy R :=
    mul_le_mul_of_nonneg_right hCoeff hE
  exact h.trans (add_le_add_right hMono _)

/-- A `7/4` signed-cell q^2 assembly bound is already sufficient for RH. -/
theorem riemannHypothesis_of_signedCellQ2EnergyAssemblyBound
    {B C : ℝ}
    (hBlo : -1 / 4 ≤ B) (hBhi : B ≤ 7 / 4) (hC : 0 ≤ C)
    (hCells : LowOwnerSignedCellQ2EnergyAssemblyBound B C) :
    RiemannHypothesis := by
  have hFinal :
      LowOwnerFinalStokesQ2EnergyBound B C :=
    (signedCellQ2EnergyAssemblyBound_iff_finalStokesQ2EnergyBound B C).mp hCells
  exact
    riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy
      (correlationFour_of_finalStokesQ2EnergyBound
        hBlo hBhi hC hFinal)

/-- **Sharp direct zero-target kill target.**

It is enough to prove the globally assembled off-diagonal zero-target excess
with q^2 coefficient `7/8`.  Doubling gives FinalStokes coefficient `7/4`,
which is already inside the compiled CORR-4/RH consumer. -/
theorem riemannHypothesis_of_zeroTargetCrossSevenEighths
    {C : ℝ} (hC : 0 ≤ C)
    (hCross : LowOwnerZeroTargetCrossQ2EnergyBound (7 / 8) C) :
    RiemannHypothesis := by
  have hRaw :=
    (zeroTargetCrossQ2EnergyBound_iff_finalStokesQ2EnergyBound
      (7 / 8) C).mp hCross
  have hFinal :
      LowOwnerFinalStokesQ2EnergyBound (7 / 4) (2 * C) := by
    convert hRaw using 1 <;> norm_num
  have hC2 : 0 ≤ 2 * C := by positivity
  exact
    riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy
      (correlationFour_of_finalStokesQ2EnergyBound
        (B := 7 / 4) (C := 2 * C)
        (by norm_num) (by norm_num) hC2 hFinal)

/-- A nonnegative returned-core `3/2` estimate already implies RH through the
existing `7/4` signed-cell/CORR-4 corridor. -/
theorem riemannHypothesis_of_returnedCoreThreeHalves
    {C : ℝ} (hC : 0 ≤ C)
    (hCore : LowOwnerReturnedCoreQ2EnergyBound (3 / 2) C) :
    RiemannHypothesis := by
  have hFinal :=
    finalStokesQ2EnergyBound_of_returnedCoreThreeHalves hCore
  have hC' : 0 ≤ (7 / 6 : ℝ) * C + 448 := by positivity
  exact
    riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy
      (correlationFour_of_finalStokesQ2EnergyBound
        (B := 7 / 4) (C := (7 / 6) * C + 448)
        (by norm_num) (by norm_num) hC' hFinal)

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
    exact h0
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


/-! ## Exact reciprocal-wall comparison target -/

/-- A direct comparison from the full signed-cell/Stokes ledger to the exact
oriented reciprocal q^2 wall cell Gram.  The exposing wall owner is fixed to
the prime 2; the assembled wall amplitude is independent of that choice, while
this choice makes the quantitative target canonical.

No estimate is asserted here: this is the remaining carrier comparison in the
same raw-parent (p,sig) coordinate. -/
def LowOwnerSignedCellToReciprocalWallCellBound (L C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerSignedCellTelescope R p sig) ≤
      L * (∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerCellGramWith R p sig
            (lowOwnerReciprocalThresholdWallSignedSite R 2)) +
      C * (R : ℝ) ^ 2 * K

/-- **Factor-14 closure criterion.**

The exact oriented reciprocal-wall cell Gram costs at most one eighth of the
recursive q^2 daughter energy.  Hence any nonnegative carrier-comparison loss
L <= 14 gives a FinalStokes coefficient L/8 <= 7/4, exactly inside the compiled
CORR-4/RH consumer.

This makes the remaining quantitative problem explicit: prove the signed
Stokes/raw-parent ledger is at most fourteen times the reciprocal-wall cell
ledger, up to the allowed root-scale lower-envelope remainder. -/
theorem riemannHypothesis_of_signedCellToReciprocalWallCellBound
    {L C : ℝ}
    (hL0 : 0 ≤ L) (hL14 : L ≤ 14) (hC : 0 ≤ C)
    (hBridge : LowOwnerSignedCellToReciprocalWallCellBound L C) :
    RiemannHypothesis := by
  have hCells :
      LowOwnerSignedCellQ2EnergyAssemblyBound (L / 8) C := by
    intro R K hR hK
    have hb := hBridge R K hR hK
    have hw :=
      sum_lowOwnerReciprocalThresholdWall_cellMass_le_eighth_q2Energy
        (R := R) (r := 2) (by norm_num : Nat.Prime 2)
    have hmul :
        L * (∑ p ∈ primesUpTo (squareRootEndpoint R),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerCellGramWith R p sig
              (lowOwnerReciprocalThresholdWallSignedSite R 2)) ≤
          (L / 8) * canonicalRoughLowQ2DaughterEnergy R := by
      have := mul_le_mul_of_nonneg_left hw hL0
      nlinarith
    linarith
  have hBlo : -1 / 4 ≤ L / 8 := by nlinarith
  have hBhi : L / 8 ≤ 7 / 4 := by nlinarith
  exact riemannHypothesis_of_signedCellQ2EnergyAssemblyBound
    hBlo hBhi hC hCells

end RHLean.Proof
