import Mathlib
import «research.GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY»
import «research.CORR4_OAI_RELAXED_REMAINDER_20261024»

/-!
# CORR-4 genuine mixed tail: record obstruction and finite plateau

This file proves arithmetic/deterministic implications, NOT the uniform
signed mixed-tail power saving, the Mertens liminf theorem, or RH.

The record energy is an explicit hypothesis. Its verification from a proposed
normalized record requires genuine Mertens information. The tent-weighted
Eisenstein norm estimates are audited separately on paper.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

/-- The full mixed source, retaining the actual physical diagonal and the
reciprocal-prefix diagonal. No discarded tail/tail term. -/
theorem corr4_mixed_tail_eq_actual_endpoint_gap
    (R : ℕ) (hR : 56 ≤ R) :
    2 * lowOwnerPrefixTailMixedRawCellMass R =
      lowOwnerPost789EndpointGapReal R ^ 2 +
      2 * lowOwnerReciprocalMertensColumnReal R *
        lowOwnerPost789EndpointGapReal R -
      (lowOwnerZeroFrequencyMobiusDiagonal R -
        lowOwnerReciprocalPrefixDiagonal R) := by
  rw [two_mul_lowOwnerPrefixTailMixedRawCellMass_eq_post789Remainder_add_prefixDiagonal
    hR]
  unfold lowOwnerPost789SignedCrossDiagonalRemainder
  ring

/-- The original q^2 column has the sharper 211/900 frame (not merely 1/4). -/
theorem corr4_reciprocal_column_sq_le_211_900_energy (R : ℕ) :
    lowOwnerReciprocalMertensColumnReal R ^ 2 ≤
      (211 / 900 : ℝ) * canonicalRoughLowQ2DaughterEnergy R := by
  have h := lowOwnerCriticalSynthesis_energy_le_twoTermBasel R 0
  rw [lowOwnerCriticalMertensSynthesis_zero_eq_reciprocalColumn R,
    ← lowOwnerReciprocalMertensColumnReal_cast R,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

/-- A record-envelope daughter energy cannot by itself cancel the positive
part of a high-amplitude C_R excursion. The leftover 14/225 is uniform.
The record-envelope condition is NOT asserted for all roots. -/
theorem corr4_mixed_excess_lower_of_record_energy
    (R : ℕ) (hR : 56 ≤ R)
    (hRecord :
      canonicalRoughLowQ2DaughterEnergy R ≤
        (211 / 900 : ℝ) * lowOwnerPost789EndpointGapReal R ^ 2) :
    (14 / 225 : ℝ) * lowOwnerPost789EndpointGapReal R ^ 2 -
      (lowOwnerZeroFrequencyMobiusDiagonal R -
        lowOwnerReciprocalPrefixDiagonal R) ≤
      2 * lowOwnerPrefixTailMixedRawCellMass R -
        2 * canonicalRoughLowQ2DaughterEnergy R := by
  let b : ℝ := 211 / 900
  let c : ℝ := lowOwnerPost789EndpointGapReal R
  let u : ℝ := lowOwnerReciprocalMertensColumnReal R
  let e : ℝ := canonicalRoughLowQ2DaughterEnergy R
  have hu : u ^ 2 ≤ b * e := by
    simpa [b, u, e] using corr4_reciprocal_column_sq_le_211_900_energy R
  have he : e ≤ b * c ^ 2 := by
    simpa [b, e, c] using hRecord
  have hu2 : u ^ 2 ≤ b ^ 2 * c ^ 2 := by
    dsimp [b] at hu he ⊢
    nlinarith
  have hcross : 2 * u * c ≤ 2 * b * c ^ 2 := by
    have hs := sq_nonneg (u - b * c)
    dsimp [b] at hs ⊢
    nlinarith
  have hexact := corr4_mixed_tail_eq_actual_endpoint_gap R hR
  dsimp [b, c, u, e] at *
  nlinarith

/-- Consequently any successful mixed-tail error budget at a record root
must pay for this exact leftover, including the diagonal. -/
theorem corr4_mixed_budget_at_record_forces_amplitude_bound
    (R : ℕ) (hR : 56 ≤ R)
    (hRecord :
      canonicalRoughLowQ2DaughterEnergy R ≤
        (211 / 900 : ℝ) * lowOwnerPost789EndpointGapReal R ^ 2)
    (B : ℝ)
    (hMixed :
      2 * lowOwnerPrefixTailMixedRawCellMass R -
        2 * canonicalRoughLowQ2DaughterEnergy R ≤ B) :
    (14 / 225 : ℝ) * lowOwnerPost789EndpointGapReal R ^ 2 ≤
      B + 3 * (R : ℝ) ^ 2 := by
  have h := corr4_mixed_excess_lower_of_record_energy R hR hRecord
  have hd := lowOwnerZeroFrequencyMobiusDiagonal_le_three_root_sq R
  have hp := lowOwnerReciprocalPrefixDiagonal_nonneg R
  linarith

/-- Literal bounded-step Mertens recurrence, no analytic input. -/
theorem corr4_mertens_summatory_succ (n : ℕ) :
    mertensSummatoryInt (n + 1) =
      mertensSummatoryInt n + ArithmeticFunction.moebius (n + 1) := by
  simp only [mertensSummatoryInt]
  rw [Finset.sum_range_succ]

/-- The integer Mertens function is 1-Lipschitz in its counting argument. -/
theorem corr4_mertens_interval_lipschitz
    (a b : ℕ) (hab : a ≤ b) :
    |mertensSummatoryInt b - mertensSummatoryInt a| ≤
      ((b - a : ℕ) : ℤ) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    have hmu : |ArithmeticFunction.moebius (b + 1)| ≤ (1 : ℤ) :=
      ArithmeticFunction.abs_moebius_le_one (n := b + 1)
    have heq :
        mertensSummatoryInt (b + 1) - mertensSummatoryInt a =
          (mertensSummatoryInt b - mertensSummatoryInt a) +
            ArithmeticFunction.moebius (b + 1) := by
      rw [corr4_mertens_summatory_succ]
      ring
    rw [heq]
    calc
      _ ≤ |mertensSummatoryInt b - mertensSummatoryInt a| +
          |ArithmeticFunction.moebius (b + 1)| := abs_add_le _ _
      _ ≤ ((b - a : ℕ) : ℤ) + 1 := add_le_add ih hmu
      _ = (((b + 1 - a : ℕ) : ℤ)) := by omega

/-- A high Mertens value forces a zero-free plateau through every physical
integer in the window, independently of any covariance hypothesis. -/
theorem corr4_mertens_zero_free_plateau
    (X H : ℕ)
    (hHeight : (H : ℤ) < |mertensSummatoryInt X|)
    (n : ℕ) (hLow : X - H ≤ n) (hHigh : n ≤ X + H) :
    mertensSummatoryInt n ≠ 0 := by
  intro hn
  have hDist :
      |mertensSummatoryInt n - mertensSummatoryInt X| ≤ (H : ℤ) := by
    rcases le_total n X with h | h
    · have hh := corr4_mertens_interval_lipschitz n X h
      rw [abs_sub_comm] at hh
      have hNH : X - n ≤ H := by omega
      exact hh.trans (by exact_mod_cast hNH)
    · have hh := corr4_mertens_interval_lipschitz X n h
      have hNH : n - X ≤ H := by omega
      exact hh.trans (by exact_mod_cast hNH)
  rw [hn, zero_sub, abs_neg] at hDist
  exact (not_le_of_gt hHeight) hDist

#print axioms corr4_mixed_tail_eq_actual_endpoint_gap
#print axioms corr4_reciprocal_column_sq_le_211_900_energy
#print axioms corr4_mixed_excess_lower_of_record_energy
#print axioms corr4_mixed_budget_at_record_forces_amplitude_bound
#print axioms corr4_mertens_interval_lipschitz
#print axioms corr4_mertens_zero_free_plateau

end RHLean.Proof
