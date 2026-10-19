import Mathlib
import RHLean.Analysis.BlockCovarianceDecomposition
import «research.SQUARE_SHELL_TRAPEZOID_ENDPOINT_TELESCOPE_20261019»

/-!
# Long-lag signed square-shell covariance: a direct 5/6 attack

This module keeps the coherent sum of H consecutive signed shells as the
primary object. Bounding each individual shell's L2 energy by H^(7/3) is
sufficient for Mertens 5/6, but NOT a necessary condition for that endpoint
growth. The exact Green--Kubo square admits an inexpensive diagonal and a
short-lag packet bounded solely by the physical shell length.

For shell block indices j=0,...,H-1, the near range in the row j is
i in [j-L,j), and the remaining far range is i in [0,j-L). This is an
EXACT partition without a lossy absolute value on the far signed pair sum.
The long-lag signed bound itself is OPEN, not asserted or manufactured by
defining a normalized target.

The finite source is arbitrary real numbers f(H+j); a later arithmetic
bridge must instantiate f with the genuine Mobius square-block increments
and pay the large-gcd subset independently.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Coherent dyadic shell row, with j=0,...,H-1. -/
def shellLagDyadicRow (f : ℕ → ℝ) (H : ℕ) : ℕ → ℝ :=
  fun j => f (H + j)

/-- Lower-order block-pair sum with shell-index separation at most L.
The truncated difference j-L is natural-number subtraction. -/
def shellLagNear (f : ℕ → ℝ) (H L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range H,
    ∑ i ∈ Finset.Ico (j - L) j, f (H + i) * f (H + j)

/-- The complementary *long-lag* signed covariance.
No absolute value is taken, and the same support is counted once. -/
def shellLagFar (f : ℕ → ℝ) (H L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range H,
    ∑ i ∈ Finset.range (j - L), f (H + i) * f (H + j)

/-- The actual far/near split is the same physical off-diagonal Gram
that the main library calls signedBlockCrossCovariance. -/
theorem shellLagCrossCovariance_eq_near_add_far
    (f : ℕ → ℝ) (H L : ℕ) :
    signedBlockCrossCovariance (shellLagDyadicRow f H) H =
      shellLagNear f H L + shellLagFar f H L := by
  rw [signedBlockCrossCovariance_eq_doubleSum]
  unfold shellLagDyadicRow shellLagNear shellLagFar
  calc
    (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range j,
      f (H + i) * f (H + j)) =
        ∑ j ∈ Finset.range H,
          ((∑ i ∈ Finset.Ico (j - L) j, f (H + i) * f (H + j)) +
           (∑ i ∈ Finset.range (j - L), f (H + i) * f (H + j))) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hsplit := Finset.sum_range_add_sum_Ico
              (f := fun i => f (H + i) * f (H + j))
              (Nat.sub_le j L)
            simpa only [add_comm] using hsplit.symm
    _ = (∑ j ∈ Finset.range H, ∑ i ∈ Finset.Ico (j - L) j,
           f (H + i) * f (H + j)) +
          (∑ j ∈ Finset.range H, ∑ i ∈ Finset.range (j - L),
           f (H + i) * f (H + j)) := by
            rw [Finset.sum_add_distrib]

/-- Exact dyadic Green--Kubo decomposition with the near / far cutoff. -/
theorem shellLagDyadicBlock_sq_eq_diagonal_add_near_add_far
    (f : ℕ → ℝ) (H L : ℕ) :
    signedBlockPrefix (shellLagDyadicRow f H) H ^ 2 =
      signedBlockEnergy (shellLagDyadicRow f H) H +
        2 * shellLagNear f H L + 2 * shellLagFar f H L := by
  rw [signedBlockPrefix_sq_eq_energy_add_two_mul_cross,
    shellLagCrossCovariance_eq_near_add_far]
  ring

/-- Bounded signed atoms on the whole dyadic family.
For true Mobius square shells, K=4H is a deterministic choice. -/
def ShellLagAtomsBounded (f : ℕ → ℝ) (H : ℕ) (K : ℝ) : Prop :=
  ∀ j : ℕ, j < H → |f (H + j)| ≤ K

/-- All near indices are in [0,j) and there are at most L of them. -/
private theorem shellLagNearIndex_card_le (j L : ℕ) :
    (Finset.Ico (j - L) j).card ≤ L := by
  simp only [Nat.card_Ico]
  omega

/-- The diagonal is paid by individual shell length; no arithmetic cancellation. -/
theorem shellLagDiagonal_le
    (f : ℕ → ℝ) (H : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (hb : ShellLagAtomsBounded f H K) :
    signedBlockEnergy (shellLagDyadicRow f H) H ≤
      (H : ℝ) * K ^ 2 := by
  unfold signedBlockEnergy shellLagDyadicRow
  calc
    (∑ j ∈ Finset.range H, f (H + j) ^ 2) ≤
        ∑ _j ∈ Finset.range H, K ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have h := hb j (Finset.mem_range.mp hj)
      have hs := (sq_le_sq₀ (abs_nonneg _) hK).2 h
      simpa only [sq_abs] using hs
    _ = (H : ℝ) * K ^ 2 := by simp

/-- Uniform absolute bound on each nonzero near pair. -/
private theorem shellLagTerm_abs_le_sq
    (f : ℕ → ℝ) (H j i : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (hb : ShellLagAtomsBounded f H K)
    (hj : j < H) (hi : i < j) :
    |f (H + i) * f (H + j)| ≤ K ^ 2 := by
  have ha := hb i (lt_trans hi hj)
  have hb' := hb j hj
  rw [abs_mul]
  calc
    |f (H + i)| * |f (H + j)| ≤ K * K := by
      exact mul_le_mul ha hb' (abs_nonneg _) hK
    _ = K ^ 2 := by ring

/-- Short-lag cost is at most H*L*K^2 without Mobius cancellation.
This estimate, unlike the far-lag upper bound, is PROVED. -/
theorem shellLagNear_abs_le
    (f : ℕ → ℝ) (H L : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (hb : ShellLagAtomsBounded f H K) :
    |shellLagNear f H L| ≤ (H : ℝ) * (L : ℝ) * K ^ 2 := by
  have hrow :
      ∀ j ∈ Finset.range H,
        |∑ i ∈ Finset.Ico (j - L) j, f (H + i) * f (H + j)| ≤
          (L : ℝ) * K ^ 2 := by
    intro j hj
    calc
      |∑ i ∈ Finset.Ico (j - L) j, f (H + i) * f (H + j)| ≤
          ∑ i ∈ Finset.Ico (j - L) j,
            |f (H + i) * f (H + j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.Ico (j - L) j, K ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          exact shellLagTerm_abs_le_sq f H j i K hK hb
            (Finset.mem_range.mp hj) (Finset.mem_Ico.mp hi).2
      _ = (((Finset.Ico (j - L) j).card : ℝ)) * K ^ 2 := by
          simp
      _ ≤ (L : ℝ) * K ^ 2 := by
          have hc : (((Finset.Ico (j - L) j).card : ℝ)) ≤ (L : ℝ) := by
            exact_mod_cast shellLagNearIndex_card_le j L
          exact mul_le_mul_of_nonneg_right hc (sq_nonneg K)
  unfold shellLagNear
  calc
    |∑ j ∈ Finset.range H,
        ∑ i ∈ Finset.Ico (j - L) j, f (H + i) * f (H + j)| ≤
        ∑ j ∈ Finset.range H,
          |∑ i ∈ Finset.Ico (j - L) j,
            f (H + i) * f (H + j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range H, ((L : ℝ) * K ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hrow j hj
    _ = (H : ℝ) * (L : ℝ) * K ^ 2 := by
        simp
        ring

/-- Exact conditional coherent block criterion. The only unbounded term is
the complete signed long-lag covariance; the diagonal and all near pairs
have already been paid by deterministic geometry. -/
theorem shellLagDyadicBlock_sq_le_far_pay
    (f : ℕ → ℝ) (H L : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (hb : ShellLagAtomsBounded f H K) :
    signedBlockPrefix (shellLagDyadicRow f H) H ^ 2 ≤
      (H : ℝ) * K ^ 2 +
        2 * (H : ℝ) * (L : ℝ) * K ^ 2 +
        2 * shellLagFar f H L := by
  have hident := shellLagDyadicBlock_sq_eq_diagonal_add_near_add_far f H L
  have hdiag := shellLagDiagonal_le f H K hK hb
  have hnear := shellLagNear_abs_le f H L K hK hb
  have hnearUpper : shellLagNear f H L ≤ (H : ℝ) * (L : ℝ) * K ^ 2 :=
    (le_abs_self _).trans hnear
  linarith

/-- Genuine Mobius block alias, without positive-density substitution. -/
def shellLagActualMobius (H j : ℕ) : ℝ :=
  realSquareBlockMass (H + j)

/-- These aliases re-use the existing exact physical square-block carrier. -/
theorem shellLagDyadicRow_realSquareBlockMass (H : ℕ) :
    shellLagDyadicRow realSquareBlockMass H = shellLagActualMobius H := rfl

#print axioms shellLagCrossCovariance_eq_near_add_far
#print axioms shellLagNear_abs_le
#print axioms shellLagDyadicBlock_sq_le_far_pay

end RHLean.Analysis
