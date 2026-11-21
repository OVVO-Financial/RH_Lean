import Mathlib
import RHLean.Analysis.PartialMomentSchurTarget

/-!
# Genuine Alpoge 2I-J Selberg band in NNS / Schur covariance coordinates

The existing source-specific research theorem
  alpogeSelbergPrimeBandRealMatrix_eq_schur
identifies the actual near-root K2 * E(1) kernel as D*(2I-J)*D,
with D_ii=log(p_i) and all prime-square and distinct semiprime
terms accounted for, including the genuine negative offdiagonal.

This module establishes a UNIFORM, UNCONDITIONAL negative payment from
that matrix on a narrow positive log-weight band. The positive
centered Schur covariance and negative principal rank-one mode are
recombined before any estimate. It is NOT an estimate of the entire
K2 recurrence, and no RH conclusion is claimed.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- The source-authentic total double-sum of D*(2I-J)*D.
The source-identification to actual prime products is proved in the
existing research/ALPOGE_SIGNED_SELBERG_INTEGRAL_SCHUR_20261120.lean. -/
def alpogeNNSBandCharge (m : ℕ) (ell : Fin m → ℝ) : ℝ :=
  2 * (∑ i : Fin m, (ell i) ^ 2) -
    (∑ i : Fin m, ell i) ^ 2

/-- Exact scaled Schur covariance of the unit-weight finite NNS sample.
This is target-invariant by finiteTargetScaledSchur_target_invariant. -/
def alpogeNNSBandScaledSchur (m : ℕ) (ell : Fin m → ℝ) : ℝ :=
  (m : ℝ) * (∑ i : Fin m, (ell i) ^ 2) -
    (∑ i : Fin m, ell i) ^ 2

/-- The signed source splits into a positive Schur covariance and the
NEGATIVE principal mean-mode payment. This is an exact equality for
the full D*(2I-J)*D matrix, not a model Gaussian covariance. -/
theorem alpogeNNSBandCharge_schur_decomposition
    (m : ℕ) (ell : Fin m → ℝ) :
    (m : ℝ) * alpogeNNSBandCharge m ell =
      2 * alpogeNNSBandScaledSchur m ell -
        ((m : ℝ) - 2) * (∑ i : Fin m, ell i) ^ 2 := by
  unfold alpogeNNSBandCharge alpogeNNSBandScaledSchur
  ring

/-- The scaled Schur covariance is nonnegative; the sign of the
complete Selberg band is instead controlled by the negative mean
mode and the narrow actual prime-log window. -/
theorem alpogeNNSBandScaledSchur_nonneg
    (m : ℕ) (ell : Fin m → ℝ) :
    0 ≤ alpogeNNSBandScaledSchur m ell := by
  have h :=
    sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := ell)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  unfold alpogeNNSBandScaledSchur
  nlinarith

/-- UNCONDITIONAL NNS SIGNED SAVING on a narrow positive band.

If m >= 3 and every positive coefficient lies in [a,4a/3],
the original full 2I-J band has a STRICT negative principal-mode
payment of order m*(m-8/3)*a^2. All signed offdiagonal entries are
retained: separately bounding the positive diagonal would lose it.

For the ACTUAL near-root prime band 3R/4 <= p < R, take
ell_i=log(p_i), a=(3/4)log R. For R>=4 the elementary
inequality log(p_i)>=(3/4)log R verifies this range.
-/
theorem alpogeNNSBandCharge_le_negative_principal
    (m : ℕ) (ell : Fin m → ℝ) (a : ℝ)
    (hm : 3 ≤ m) (ha : 0 ≤ a)
    (hband : ∀ i : Fin m, a ≤ ell i ∧ ell i ≤ (4 / 3 : ℝ) * a) :
    alpogeNNSBandCharge m ell ≤
      -((m : ℝ) * ((m : ℝ) - 8 / 3) * a ^ 2) := by
  let S : ℝ := ∑ i : Fin m, ell i
  let Q : ℝ := ∑ i : Fin m, (ell i) ^ 2
  have hlow : (m : ℝ) * a ≤ S := by
    have h := Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin m)))
      (fun i _hi => (hband i).1)
    simpa [S, nsmul_eq_mul] using h
  have hquad : Q ≤ (4 / 3 : ℝ) * a * S := by
    calc
      Q ≤ ∑ i : Fin m, ((4 / 3 : ℝ) * a) * ell i := by
        apply Finset.sum_le_sum
        intro i _hi
        have hia : 0 ≤ ell i := le_trans ha (hband i).1
        have hii := mul_le_mul_of_nonneg_right (hband i).2 hia
        nlinarith [hii]
      _ = (4 / 3 : ℝ) * a * S := by
        rw [← Finset.mul_sum]
  have hmreal : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmarginNonneg : 0 ≤ ((m : ℝ) - 8 / 3) * a := by
    apply mul_nonneg
    · linarith
    · exact ha
  have hSnonneg : 0 ≤ S := le_trans (mul_nonneg (by positivity) ha) hlow
  have hmargin :
      ((m : ℝ) - 8 / 3) * a ≤ S - (8 / 3 : ℝ) * a := by
    nlinarith [hlow]
  have hproduct :
      ((m : ℝ) * a) * (((m : ℝ) - 8 / 3) * a) ≤
        S * (S - (8 / 3 : ℝ) * a) := by
    calc
      _ ≤ S * (((m : ℝ) - 8 / 3) * a) :=
        mul_le_mul_of_nonneg_right hlow hmarginNonneg
      _ ≤ S * (S - (8 / 3 : ℝ) * a) :=
        mul_le_mul_of_nonneg_left hmargin hSnonneg
  change 2 * Q - S ^ 2 ≤
    -((m : ℝ) * ((m : ℝ) - 8 / 3) * a ^ 2)
  nlinarith [hquad, hproduct]

/-- The bound is genuinely negative when the original band includes
at least three independent prime owners. -/
theorem alpogeNNSBandCharge_neg
    (m : ℕ) (ell : Fin m → ℝ) (a : ℝ)
    (hm : 3 ≤ m) (ha : 0 < a)
    (hband : ∀ i : Fin m, a ≤ ell i ∧ ell i ≤ (4 / 3 : ℝ) * a) :
    alpogeNNSBandCharge m ell < 0 := by
  have h := alpogeNNSBandCharge_le_negative_principal
    m ell a hm ha.le hband
  have hmreal : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith [sq_pos_of_pos ha]

end RHLean.Analysis
