import Mathlib
import «research.EULER_HYBRID_TRIANGULAR_GRAM_20261027»
import RHLean.Analysis.NativePNTMertens

/-!
# Exact original Möbius fractional Euler bilinear and divisor-row subtraction

X_R = R^2 - 1. We use rational fractional parts to retain the exact
integer root corner without analytic approximations. The original floor
bilinear, its continuous rank-one part, and its fractional signed source
are finite arithmetic objects. No estimate on the signed off-diagonal
source, finite-C hypothesis, improved exponent or RH is asserted.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- The **actual** integer Möbius coefficient, embedded in rationals. -/
def eulerMuQ (n : ℕ) : ℚ := ((μ n : ℤ) : ℚ)

/-- Historical reciprocal Möbius prefix. -/
def eulerReciprocalHistoricalQ (R : ℕ) : ℚ :=
  ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a / (a : ℚ)

/-- Full self-dual original floor kernel, at the exact integer cutoff. -/
def eulerFloorQ (R a b : ℕ) : ℚ :=
  ((squareRootEndpoint R / (a * b) : ℕ) : ℚ)

/-- Its complete continuous kernel, *before* replacing floors. -/
def eulerContinuousQ (R a b : ℕ) : ℚ :=
  (squareRootEndpoint R : ℚ) / ((a : ℚ) * (b : ℚ))

/-- The exact sawtooth difference; on positive a,b it is {X/(ab)}. -/
def eulerFractionQ (R a b : ℕ) : ℚ :=
  eulerContinuousQ R a b - eulerFloorQ R a b

/-- The original double Möbius bilinear, with rational rather than complex coefficients. -/
def eulerFloorBilinearQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a * eulerFloorQ R a b

/-- The signed continuous rank-one double source. -/
def eulerContinuousBilinearQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a * eulerContinuousQ R a b

/-- The **complete** original signed fractional double source; no absolute values. -/
def eulerFractionBilinearQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a * eulerFractionQ R a b

/-- Fractional diagonal, with original Möbius squarefree zero coefficients. -/
def eulerFractionDiagonalQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1),
    eulerMuQ b ^ 2 * eulerFractionQ R b b

/-- Original strict signed off-diagonal fractional Gram; no arbitrary weights. -/
def eulerFractionOffQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (b - 1), eulerMuQ a * eulerFractionQ R a b

/-- One exact finite-mode decomposition; neither source is bounded separately. -/
theorem eulerFloorBilinearQ_eq_continuous_sub_fractional (R : ℕ) :
    eulerFloorBilinearQ R =
      eulerContinuousBilinearQ R - eulerFractionBilinearQ R := by
  unfold eulerFloorBilinearQ eulerContinuousBilinearQ eulerFractionBilinearQ
  calc
    (∑ b ∈ Finset.Icc 1 (R - 1),
      eulerMuQ b * ∑ a ∈ Finset.Icc 1 (R - 1),
        eulerMuQ a * eulerFloorQ R a b) =
      ∑ b ∈ Finset.Icc 1 (R - 1),
        eulerMuQ b * ∑ a ∈ Finset.Icc 1 (R - 1),
          eulerMuQ a * (eulerContinuousQ R a b - eulerFractionQ R a b) := by
            apply Finset.sum_congr rfl
            intro b _hb
            congr 1
            apply Finset.sum_congr rfl
            intro a _ha
            unfold eulerFractionQ
            ring
    _ = (∑ b ∈ Finset.Icc 1 (R - 1),
          eulerMuQ b * ∑ a ∈ Finset.Icc 1 (R - 1),
            eulerMuQ a * eulerContinuousQ R a b) -
        (∑ b ∈ Finset.Icc 1 (R - 1),
          eulerMuQ b * ∑ a ∈ Finset.Icc 1 (R - 1),
            eulerMuQ a * eulerFractionQ R a b) := by
          simp_rw [mul_sub, Finset.sum_sub_distrib]
          simp_rw [mul_sub, Finset.sum_sub_distrib]

/-- The continuous bilinear is an *exact rank-one square*. -/
theorem eulerContinuousBilinearQ_eq_reciprocal_square (R : ℕ) :
    eulerContinuousBilinearQ R =
      (squareRootEndpoint R : ℚ) * eulerReciprocalHistoricalQ R ^ 2 := by
  unfold eulerContinuousBilinearQ eulerReciprocalHistoricalQ
  let S := Finset.Icc 1 (R - 1)
  have hterm (a b : ℕ) :
      eulerMuQ b * (eulerMuQ a * eulerContinuousQ R a b) =
        ((squareRootEndpoint R : ℚ) * (eulerMuQ b / (b : ℚ))) *
          (eulerMuQ a / (a : ℚ)) := by
    unfold eulerContinuousQ
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  calc
    (∑ b ∈ S, eulerMuQ b * ∑ a ∈ S,
      eulerMuQ a * eulerContinuousQ R a b) =
      ∑ b ∈ S, ((squareRootEndpoint R : ℚ) * (eulerMuQ b / (b : ℚ))) *
        ∑ a ∈ S, eulerMuQ a / (a : ℚ) := by
          apply Finset.sum_congr rfl
          intro b _hb
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _ha
          exact hterm a b
    _ = (squareRootEndpoint R : ℚ) *
        (∑ n ∈ S, eulerMuQ n / (n : ℚ)) ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          ring

/-- The original rational floor form is literally the #1034 complex source. -/
theorem eulerFloorBilinearQ_cast_eq_original (R : ℕ) :
    ((eulerFloorBilinearQ R : ℚ) : ℂ) = eulerSelfDualBilinear R := by
  unfold eulerFloorBilinearQ eulerSelfDualBilinear
  simp [eulerMuQ, eulerFloorQ, eulerSelfDualFloor, Rat.cast_sum, Rat.cast_mul]


/-- Exact Euclidean rational fractional part on positive physical indices. -/
theorem eulerFractionQ_eq_mod_div {R a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) :
    eulerFractionQ R a b =
      ((squareRootEndpoint R % (a * b) : ℕ) : ℚ) / ((a * b : ℕ) : ℚ) := by
  let X : ℕ := squareRootEndpoint R
  let d : ℕ := a * b
  have hd : 0 < d := Nat.mul_pos ha hb
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hmod : X % d + d * (X / d) = X := Nat.mod_add_div X d
  have hrat :
      ((X % d : ℕ) : ℚ) + (d : ℚ) * ((X / d : ℕ) : ℚ) = (X : ℚ) := by
    exact_mod_cast hmod
  unfold eulerFractionQ eulerContinuousQ eulerFloorQ
  have hmul : (a : ℚ) * (b : ℚ) = ((a * b : ℕ) : ℚ) := by push_cast; ring
  rw [hmul]
  change (X : ℚ) / (d : ℚ) - ((X / d : ℕ) : ℚ) =
    ((X % d : ℕ) : ℚ) / (d : ℚ)
  field_simp [hd0]
  linarith [hrat]

/-- Exact fractional range; there is NO probabilistic equidistribution premise. -/
theorem eulerFractionQ_nonneg_lt_one {R a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) :
    0 ≤ eulerFractionQ R a b ∧ eulerFractionQ R a b < 1 := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have hcast : (0 : ℚ) < ((a * b : ℕ) : ℚ) := by exact_mod_cast hab
  have hmod : ((squareRootEndpoint R % (a * b) : ℕ) : ℚ) <
      ((a * b : ℕ) : ℚ) := by
    exact_mod_cast (Nat.mod_lt (squareRootEndpoint R) hab)
  rw [eulerFractionQ_eq_mod_div ha hb]
  constructor
  · positivity
  · exact (div_lt_iff₀ hcast).2 (by simpa using hmod)

/-- Generic finite signed symmetric square: diagonal plus BOTH strict triangles. -/
private theorem eulerFractionSymmetricSquareQ (N : ℕ) (c : ℕ → ℚ)
    (F : ℕ → ℕ → ℚ) (hF : ∀ a b, F a b = F b a) :
    (∑ b ∈ Finset.Icc 1 N,
      c b * (∑ a ∈ Finset.Icc 1 N, c a * F a b)) =
      (∑ b ∈ Finset.Icc 1 N, c b ^ 2 * F b b) +
      2 * ∑ b ∈ Finset.Icc 1 N,
        c b * (∑ a ∈ Finset.Icc 1 (b - 1), c a * F a b) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hswap :
          (∑ b ∈ Finset.Icc 1 N, c b * (c (N + 1) * F (N + 1) b)) =
          c (N + 1) * (∑ a ∈ Finset.Icc 1 N, c a * F a (N + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _hb
        rw [hF (N + 1) b]
        ring
      have hQ :
          (∑ b ∈ Finset.Icc 1 (N + 1),
            c b * (∑ a ∈ Finset.Icc 1 (N + 1), c a * F a b)) =
          (∑ b ∈ Finset.Icc 1 N,
            c b * (∑ a ∈ Finset.Icc 1 N, c a * F a b)) +
          2 * c (N + 1) *
            (∑ a ∈ Finset.Icc 1 N, c a * F a (N + 1)) +
          c (N + 1) ^ 2 * F (N + 1) (N + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        simp_rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, hswap]
        ring
      have hD :
          (∑ b ∈ Finset.Icc 1 (N + 1), c b ^ 2 * F b b) =
          (∑ b ∈ Finset.Icc 1 N, c b ^ 2 * F b b) +
            c (N + 1) ^ 2 * F (N + 1) (N + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      have hB :
          (∑ b ∈ Finset.Icc 1 (N + 1),
            c b * (∑ a ∈ Finset.Icc 1 (b - 1), c a * F a b)) =
          (∑ b ∈ Finset.Icc 1 N,
            c b * (∑ a ∈ Finset.Icc 1 (b - 1), c a * F a b)) +
          c (N + 1) * (∑ a ∈ Finset.Icc 1 N, c a * F a (N + 1)) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        simp [show N + 1 - 1 = N by omega]
      rw [hQ, hD, hB, ih]
      ring

/-- Fully weighted fractional Gram: the original strict off-diagonal is
NOT replaced by an artificial coefficient vector. -/
theorem eulerFractionBilinearQ_eq_diagonal_add_twice_off (R : ℕ) :
    eulerFractionBilinearQ R =
      eulerFractionDiagonalQ R + 2 * eulerFractionOffQ R := by
  have hsym (a b : ℕ) :
      eulerFractionQ R a b = eulerFractionQ R b a := by
    simp [eulerFractionQ, eulerContinuousQ, eulerFloorQ, Nat.mul_comm]
  exact eulerFractionSymmetricSquareQ (R - 1) eulerMuQ
    (eulerFractionQ R) hsym

/-- The fractional diagonal is completely paid at the root scale, WITHOUT K. -/
theorem eulerFractionDiagonalQ_bounds (R : ℕ) (hR : 2 ≤ R) :
    0 ≤ eulerFractionDiagonalQ R ∧
      eulerFractionDiagonalQ R ≤ (R - 1 : ℕ) := by
  have hterm (b : ℕ) (hb : b ∈ Finset.Icc 1 (R - 1)) :
      0 ≤ eulerMuQ b ^ 2 * eulerFractionQ R b b ∧
        eulerMuQ b ^ 2 * eulerFractionQ R b b ≤ 1 := by
    have hbpos : 0 < b := (Finset.mem_Icc.mp hb).1
    obtain ⟨hf0, hf1⟩ := eulerFractionQ_nonneg_lt_one
      (R := R) hbpos hbpos
    have hc : 0 ≤ eulerMuQ b ^ 2 ∧ eulerMuQ b ^ 2 ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or b with h | h | h <;>
        simp [eulerMuQ, h]
    constructor
    · exact mul_nonneg hc.1 hf0
    · calc
        eulerMuQ b ^ 2 * eulerFractionQ R b b ≤
          (1 : ℚ) * eulerFractionQ R b b :=
            mul_le_mul_of_nonneg_right hc.2 hf0
        _ ≤ 1 := by nlinarith
  constructor
  · unfold eulerFractionDiagonalQ
    apply Finset.sum_nonneg
    intro b hb
    exact (hterm b hb).1
  · unfold eulerFractionDiagonalQ
    calc
      (∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b ^ 2 * eulerFractionQ R b b) ≤
        ∑ b ∈ Finset.Icc 1 (R - 1), (1 : ℚ) := by
          apply Finset.sum_le_sum
          intro b hb
          exact (hterm b hb).2
      _ = (R - 1 : ℕ) := by simp [Nat.card_Icc]

/-- The exact original triad, with no corner loss and with the full mixed term. -/
theorem eulerFloorBilinearQ_eq_continuous_sub_diag_sub_twice_off (R : ℕ) :
    eulerFloorBilinearQ R =
      (squareRootEndpoint R : ℚ) * eulerReciprocalHistoricalQ R ^ 2 -
      eulerFractionDiagonalQ R - 2 * eulerFractionOffQ R := by
  rw [eulerFloorBilinearQ_eq_continuous_sub_fractional,
    eulerContinuousBilinearQ_eq_reciprocal_square,
    eulerFractionBilinearQ_eq_diagonal_add_twice_off]
  ring

#print axioms eulerFloorBilinearQ_eq_continuous_sub_fractional
#print axioms eulerContinuousBilinearQ_eq_reciprocal_square
#print axioms eulerFloorBilinearQ_eq_continuous_sub_diag_sub_twice_off
#print axioms eulerFractionDiagonalQ_bounds

end RHLean.Proof
