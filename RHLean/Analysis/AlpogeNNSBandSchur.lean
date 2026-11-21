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
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hgap : (0 : ℝ) < (m : ℝ) - 8 / 3 := by linarith
  have hfactor :
      0 < (m : ℝ) * ((m : ℝ) - 8 / 3) * a ^ 2 := by
    positivity
  exact lt_of_le_of_lt h (neg_lt_zero.mpr hfactor)

/-- A constant target has exactly the stated total mass on Fin m. -/
private theorem alpogeNNSBand_sum_constant
    (m : ℕ) (c : ℝ) :
    (∑ _i : Fin m, c) = (m : ℝ) * c := by
  simp [nsmul_eq_mul]

/-- The target-invariant scalar Schur complement is at most one quarter
of the squared range times the square of the sample count. This is the
sharp deterministic Popoviciu inequality, not a probabilistic model.
The proof works by choosing the MIDRANGE as an auxiliary NNS target:
the Schur projection removes the *entire* first moment at no cost. -/
theorem alpogeNNSBandScaledSchur_le_range
    (m : ℕ) (ell : Fin m → ℝ) (a b : ℝ)
    (hband : ∀ i : Fin m, a ≤ ell i ∧ ell i ≤ b) :
    alpogeNNSBandScaledSchur m ell ≤
      ((m : ℝ) ^ 2 / 4) * (b - a) ^ 2 := by
  let S : ℝ := ∑ i : Fin m, ell i
  let Q : ℝ := ∑ i : Fin m, (ell i) ^ 2
  let c : ℝ := (a + b) / 2
  have hpoint :
      ∀ i : Fin m, (ell i - c) ^ 2 ≤ (b - a) ^ 2 / 4 := by
    intro i
    have hlo : 0 ≤ ell i - a := by linarith [(hband i).1]
    have hhi : 0 ≤ b - ell i := by linarith [(hband i).2]
    have hcross := mul_nonneg hlo hhi
    dsimp [c]
    nlinarith [hcross]
  have hvariance :
      (∑ i : Fin m, (ell i - c) ^ 2) ≤
        (m : ℝ) * ((b - a) ^ 2 / 4) := by
    have h := Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin m)))
      (fun i _hi => hpoint i)
    rw [alpogeNNSBand_sum_constant] at h
    exact h
  have hsum :
      (∑ i : Fin m, ell i - c) =
        S - (m : ℝ) * c := by
    calc
      _ = (∑ i : Fin m, ell i) - (∑ _i : Fin m, c) := Finset.sum_sub_distrib
      _ = S - (m : ℝ) * c := by
        rw [alpogeNNSBand_sum_constant]
        rfl
  have hsumSq :
      (∑ i : Fin m, (ell i - c) ^ 2) =
        Q - 2 * c * S + (m : ℝ) * c ^ 2 := by
    calc
      _ = ∑ i : Fin m,
            ((ell i) ^ 2 - 2 * c * ell i + c ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
      _ = Q - 2 * c * S + (m : ℝ) * c ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, alpogeNNSBand_sum_constant]
  have hscaled :
      alpogeNNSBandScaledSchur m ell =
        (m : ℝ) * (∑ i : Fin m, (ell i - c) ^ 2) -
          (∑ i : Fin m, ell i - c) ^ 2 := by
    unfold alpogeNNSBandScaledSchur
    rw [hsumSq, hsum]
    dsimp [S, Q]
    ring
  calc
    alpogeNNSBandScaledSchur m ell =
        (m : ℝ) * (∑ i : Fin m, (ell i - c) ^ 2) -
          (∑ i : Fin m, ell i - c) ^ 2 := hscaled
    _ ≤ (m : ℝ) * (∑ i : Fin m, (ell i - c) ^ 2) := by
          nlinarith [sq_nonneg (∑ i : Fin m, ell i - c)]
    _ ≤ (m : ℝ) * ((m : ℝ) * ((b - a) ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left hvariance (by positivity)
    _ = ((m : ℝ) ^ 2 / 4) * (b - a) ^ 2 := by ring

/-- A sharper full-signed-source budget: the complete positive Schur
correction costs only ONE HALF of the band size times the squared
logarithmic width. All remaining large contribution is the explicit
NEGATIVE principal mode, not an untracked covariance error.

The statement is scaled by m so no arbitrary epsilon or denominator
is introduced. The result holds for ANY narrow physical positive band. -/
theorem alpogeNNSBandCharge_le_principal_plus_range
    (m : ℕ) (ell : Fin m → ℝ) (a b : ℝ)
    (hband : ∀ i : Fin m, a ≤ ell i ∧ ell i ≤ b) :
    (m : ℝ) * alpogeNNSBandCharge m ell ≤
      -((m : ℝ) - 2) * (∑ i : Fin m, ell i) ^ 2 +
        ((m : ℝ) ^ 2 / 2) * (b - a) ^ 2 := by
  have hschur := alpogeNNSBandScaledSchur_le_range
    m ell a b hband
  rw [alpogeNNSBandCharge_schur_decomposition]
  nlinarith [hschur]

/-- Sharp, fixed-sign NNS positive-part subadditivity when the
Schur variance error is nonnegative. This never replaces the original
complete source by two separately bounded absolute masses. -/
private theorem alpogeNNS_positivePart_add_nonneg_le
    (x v : ℝ) (hv : 0 ≤ v) :
    max (x + v) 0 ≤ max x 0 + v := by
  by_cases hx : 0 ≤ x
  · have hxv : 0 ≤ x + v := add_nonneg hx hv
    rw [max_eq_left hxv, max_eq_left hx]
  · have hxneg : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hxneg]
    by_cases hxv : 0 ≤ x + v
    · rw [max_eq_left hxv]
      linarith
    · rw [max_eq_right (le_of_not_ge hxv)]
      simpa using hv

/-- The genuine one-sided Selberg/NNS CHARGE, with ALL positive
centered covariance paid at O(m^2 * width^2). The only surviving
large dangerous quantity is the complete complement minus its
explicit negative rank-one principal payment. This statement holds
for an ARBITRARY signed complement C (no false sign assumed).

An actual C is defined from the complete signed Selberg recurrence
with the authentic band removed in the companion source bridge. -/
theorem alpogeNNSBandOneSidedCharge_le_principal_overshoot
    (m : ℕ) (ell : Fin m → ℝ) (C a b : ℝ)
    (hband : ∀ i : Fin m, a ≤ ell i ∧ ell i ≤ b) :
    max ((m : ℝ) * (C + alpogeNNSBandCharge m ell)) 0 ≤
      max ((m : ℝ) * C -
        ((m : ℝ) - 2) * (∑ i : Fin m, ell i) ^ 2) 0 +
        ((m : ℝ) ^ 2 / 2) * (b - a) ^ 2 := by
  let S : ℝ := ∑ i : Fin m, ell i
  let H : ℝ := (m : ℝ) * C - ((m : ℝ) - 2) * S ^ 2
  let V : ℝ := 2 * alpogeNNSBandScaledSchur m ell
  let W : ℝ := ((m : ℝ) ^ 2 / 2) * (b - a) ^ 2
  have hidentity :
      (m : ℝ) * (C + alpogeNNSBandCharge m ell) = H + V := by
    dsimp [H, V, S]
    have h := alpogeNNSBandCharge_schur_decomposition m ell
    nlinarith [h]
  have hVnonneg : 0 ≤ V := by
    dsimp [V]
    have hschur := alpogeNNSBandScaledSchur_nonneg m ell
    linarith
  have hVbound : V ≤ W := by
    have hschur := alpogeNNSBandScaledSchur_le_range
      m ell a b hband
    dsimp [V, W]
    nlinarith
  calc
    max ((m : ℝ) * (C + alpogeNNSBandCharge m ell)) 0 =
        max (H + V) 0 := by rw [hidentity]
    _ ≤ max H 0 + V := alpogeNNS_positivePart_add_nonneg_le H V hVnonneg
    _ ≤ max H 0 + W := by linarith [hVbound]
    _ = max ((m : ℝ) * C -
        ((m : ℝ) - 2) * (∑ i : Fin m, ell i) ^ 2) 0 +
        ((m : ℝ) ^ 2 / 2) * (b - a) ^ 2 := rfl

end RHLean.Analysis
