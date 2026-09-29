import Mathlib
import «research.GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT»
import «research.GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE»

/-!
# The prefix-tail mixed remainder is the post-789 remainder

`GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT` isolates the signed
far-tail/mixed cell mass after the reciprocal q² prefix has been paid, and
names `LowOwnerPrefixTailMixedQ2EnergyBound (3/2) C` as a sufficient target.

This file evaluates that remainder exactly.  The global first-owner Fubini for
an arbitrary signed site gives, for the reciprocal prefix `P`,

  2 * PrefixRawCellMass = Q_R^2 - D_P,

where `D_P` is the prefix diagonal on the common clock.  Combined with the
compiled final-Stokes identities this yields

  2 * PrefixTailMixed_R = S_R + D_P,        0 <= D_P <= D_R <= 3 R^2,

with `S_R = G_R^2 + 2 Q_R G_R - D_R` the post-789 signed remainder.

Consequences:

* a prefix-tail mixed bound with coefficient `B` is an `S_R` bound with the
  same coefficient, and conversely up to `+3` in the boundary constant;
* hence coefficient `2` already closes the existing consumer (the compiled
  `S_R` threshold), not only `3/2`;
* every such bound controls the endpoint correlation:
  `(3/4) |corr_R|^2 - E_R - 3 R^2 <= 2 * PrefixTailMixed_R`.

So the prefix-tail mixed remainder is the post-789 remainder plus an explicit
nonnegative root-scale diagonal.  It is not a narrower seam.  No estimate on
Möbius partial sums is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Diagonal of the reciprocal-prefix signed site on the common clock. -/
def lowOwnerReciprocalPrefixDiagonal (R : ℕ) : ℝ :=
  lowOwnerGlobalDiagonalPairMassWith R (lowOwnerReciprocalPrefixSignedSite R)

theorem lowOwnerReciprocalPrefixDiagonal_nonneg (R : ℕ) :
    0 ≤ lowOwnerReciprocalPrefixDiagonal R :=
  lowOwnerGlobalDiagonalPairMassWith_nonneg R _

/-- **Exact prefix cell mass.**  The reciprocal-prefix raw cell mass is the
column square minus the prefix diagonal. -/
theorem two_mul_lowOwnerReciprocalPrefixRawCellMass_eq_column_sq_sub_diagonal
    (R : ℕ) :
    2 * lowOwnerReciprocalPrefixRawCellMass R =
      lowOwnerReciprocalMertensColumnReal R ^ 2 -
        lowOwnerReciprocalPrefixDiagonal R := by
  have h1 :=
    lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_firstOwners R
      (lowOwnerReciprocalPrefixSignedSite R)
  rw [lowOwnerReciprocalPrefix_emptyEnergy_eq_column_sq] at h1
  have h2 :
      (∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerGlobalFirstOwnerPairMassWith R p
          (lowOwnerReciprocalPrefixSignedSite R)) =
        2 * lowOwnerReciprocalPrefixRawCellMass R := by
    unfold lowOwnerReciprocalPrefixRawCellMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    exact lowOwnerGlobalFirstOwnerPairMassWith_eq_two_sum_cells
      (mem_primesUpTo.mp hp).1 _
  unfold lowOwnerReciprocalPrefixDiagonal
  linarith

/-- **The mixed remainder is the post-789 remainder plus the prefix diagonal.** -/
theorem two_mul_lowOwnerPrefixTailMixedRawCellMass_eq_post789Remainder_add_prefixDiagonal
    {R : ℕ} (hR : 56 ≤ R) :
    2 * lowOwnerPrefixTailMixedRawCellMass R =
      lowOwnerPost789SignedCrossDiagonalRemainder R +
        lowOwnerReciprocalPrefixDiagonal R := by
  have hsplit :=
    sum_lowOwnerFirstOwnerSignedCellTelescope_eq_prefix_add_tailMixed R
  rw [sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary
      (by omega : 2 ≤ R),
    lowOwnerCanonicalSignedStokesFinalBoundary_eq_q2Sq_add_post789Remainder hR]
    at hsplit
  have hP :=
    two_mul_lowOwnerReciprocalPrefixRawCellMass_eq_column_sq_sub_diagonal R
  linarith

/-- The prefix site is dominated pointwise by the full AMP site, because both
weights are nonnegative and share the Möbius sign. -/
theorem lowOwnerReciprocalPrefixSignedSite_sq_le_site_sq (R n : ℕ) :
    lowOwnerReciprocalPrefixSignedSite R n ^ 2 ≤
      lowOwnerZeroFrequencyMobiusSite R n ^ 2 := by
  have hw := lowOwnerReciprocalDaughterWeight_nonneg R n
  have hf : 0 ≤ lowOwnerFarTailWeight R n := by
    unfold lowOwnerFarTailWeight
    split_ifs <;> norm_num
  have hextra :
      0 ≤ lowOwnerFarTailWeight R n *
          (lowOwnerFarTailWeight R n + 2 * lowOwnerReciprocalDaughterWeight R n) *
          realMoebiusStep n ^ 2 :=
    mul_nonneg (mul_nonneg hf (by linarith)) (sq_nonneg _)
  unfold lowOwnerReciprocalPrefixSignedSite lowOwnerZeroFrequencyMobiusSite
    lowOwnerZeroFrequencyMobiusWeight
  nlinarith [hextra]

/-- The prefix diagonal is at most the full AMP diagonal. -/
theorem lowOwnerReciprocalPrefixDiagonal_le_zeroFrequencyDiagonal (R : ℕ) :
    lowOwnerReciprocalPrefixDiagonal R ≤
      lowOwnerZeroFrequencyMobiusDiagonal R := by
  unfold lowOwnerReciprocalPrefixDiagonal
  rw [lowOwnerGlobalDiagonalPairMassWith_eq_sum_sq]
  unfold lowOwnerZeroFrequencyMobiusDiagonal signedBlockEnergy
  have hsub : lowOwnerNonzeroMobiusCarrier R ⊆
      Finset.range (squareRootEndpoint R + 1) := by
    intro n hn
    have hnX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    exact Finset.mem_range.mpr (by omega)
  calc
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
        lowOwnerReciprocalPrefixSignedSite R n ^ 2) ≤
      ∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
        lowOwnerZeroFrequencyMobiusSite R n ^ 2 :=
      Finset.sum_le_sum fun n _hn =>
        lowOwnerReciprocalPrefixSignedSite_sq_le_site_sq R n
    _ ≤ ∑ n ∈ Finset.range (squareRootEndpoint R + 1),
        lowOwnerZeroFrequencyMobiusSite R n ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        fun n _hn _hnot => sq_nonneg _

/-- The prefix diagonal is root-scale. -/
theorem lowOwnerReciprocalPrefixDiagonal_le_three_root_sq (R : ℕ) :
    lowOwnerReciprocalPrefixDiagonal R ≤ 3 * (R : ℝ) ^ 2 :=
  (lowOwnerReciprocalPrefixDiagonal_le_zeroFrequencyDiagonal R).trans
    (lowOwnerZeroFrequencyMobiusDiagonal_le_three_root_sq R)

/-- A prefix-tail mixed bound is an `S_R` bound with the same constants. -/
theorem post789SignedRemainderBound_of_prefixTailMixedBound
    {B C : ℝ} (h : LowOwnerPrefixTailMixedQ2EnergyBound B C) :
    LowOwnerPost789SignedCrossDiagonalRemainderBound B C := by
  intro R K hR hK
  have hM := h R K hR hK
  rw [two_mul_lowOwnerPrefixTailMixedRawCellMass_eq_post789Remainder_add_prefixDiagonal
    hR] at hM
  have hD := lowOwnerReciprocalPrefixDiagonal_nonneg R
  linarith

/-- Conversely, an `S_R` bound gives a prefix-tail mixed bound with the same
q² coefficient, paying `3` in the boundary constant. -/
theorem prefixTailMixedBound_of_post789SignedRemainderBound
    {B C : ℝ} (h : LowOwnerPost789SignedCrossDiagonalRemainderBound B C) :
    LowOwnerPrefixTailMixedQ2EnergyBound B (C + 3) := by
  intro R K hR hK
  have hS := h R K hR hK
  rw [two_mul_lowOwnerPrefixTailMixedRawCellMass_eq_post789Remainder_add_prefixDiagonal
    hR]
  have hD := lowOwnerReciprocalPrefixDiagonal_le_three_root_sq R
  have hK1 : 1 ≤ K := by
    have h0 := hK.2 0 (by omega)
    have hm0 : mertensSummatoryInt 0 = 0 := by
      simp [mertensSummatoryInt]
    rw [hm0] at h0
    norm_num at h0
    exact h0
  have hR2 : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
  have hRK : 3 * (R : ℝ) ^ 2 ≤ 3 * (R : ℝ) ^ 2 * K := by
    nlinarith [mul_le_mul_of_nonneg_left hK1 hR2]
  linarith

/-- **Same seam.**  For every q² coefficient `B`, some uniform prefix-tail
mixed bound exists iff some uniform post-789 remainder bound exists. -/
theorem exists_prefixTailMixedBound_iff_exists_post789SignedRemainderBound
    (B : ℝ) :
    (∃ C : ℝ, LowOwnerPrefixTailMixedQ2EnergyBound B C) ↔
      ∃ C : ℝ, LowOwnerPost789SignedCrossDiagonalRemainderBound B C := by
  constructor
  · rintro ⟨C, h⟩
    exact ⟨C, post789SignedRemainderBound_of_prefixTailMixedBound h⟩
  · rintro ⟨C, h⟩
    exact ⟨C + 3, prefixTailMixedBound_of_post789SignedRemainderBound h⟩

/-- Coefficient `2` on the prefix-tail mixed remainder already closes the
existing consumer; the `3/2` threshold is not needed. -/
theorem riemannHypothesis_of_prefixTailMixedTwo
    {C : ℝ} (hC : 0 ≤ C)
    (h : LowOwnerPrefixTailMixedQ2EnergyBound 2 C) :
    RiemannHypothesis :=
  riemannHypothesis_of_post789SignedRemainderBound_two hC
    (post789SignedRemainderBound_of_prefixTailMixedBound h)

/-- Every prefix-tail mixed bound controls the endpoint correlation. -/
theorem threeQuarters_correlationSq_sub_le_two_mul_prefixTailMixed
    {R : ℕ} (hR : 56 ≤ R) :
    (3 / 4 : ℝ) * ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 -
        canonicalRoughLowQ2DaughterEnergy R - 3 * (R : ℝ) ^ 2 ≤
      2 * lowOwnerPrefixTailMixedRawCellMass R := by
  have hS := threeQuarters_correlationSq_sub_le_post789SignedRemainder
    (by omega : 2 ≤ R)
  rw [two_mul_lowOwnerPrefixTailMixedRawCellMass_eq_post789Remainder_add_prefixDiagonal
    hR]
  have hD := lowOwnerReciprocalPrefixDiagonal_nonneg R
  linarith

end RHLean.Proof
