import Mathlib
import «research.OFF_CRITICAL_ZERO_HIGH_VF_BRIDGE_20261029»
import «research.OFF_CRITICAL_ZERO_REALIFIED_SCALE_20261029»

/-!
# Exact finite theta Mellin coarsening, INCLUDING its discretization defect

For any complex sequence A and real square-root q, the coarse Mellin sum is
NOT an exact multiple of the original fine Mellin sum: it also includes
an infinite collection of WITHIN-BLOCK kernel corrections in the limit.

This module proves the finite identity first, with no convergence claim,
and specializes it to the genuine square-block theta shortage.

For the infinite residue conclusion one must separately show the series
of defects is holomorphic on Re(s)>1/2. That estimate is NOT replaced
by a paper assumption or an axiom.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Complex Mellin kernel with the real positive logarithm, avoiding
multivalued complex-power branch conventions. -/
def offcriticalSquareMellinKernel (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp ((-2 * s) * ((Real.log (n : ℝ) : ℝ) : ℂ))

/-- Fine-to-coarse multiplicative Mellin scale q^(2s). -/
def offcriticalFineMellinScale (s : ℂ) (q : ℕ) : ℂ :=
  Complex.exp ((2 * s) * ((Real.log (q : ℝ) : ℝ) : ℂ))

/-- The exact local WITHIN-BLOCK discretization defect: the original
fine endpoints j+1 are not equal to q*(R+1). -/
def offcriticalLocalMellinDefect
    (a : ℕ → ℂ) (q R : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.Ico (q * R) (q * (R + 1)),
    a j * (offcriticalSquareMellinKernel s (R + 1) -
      offcriticalFineMellinScale s q *
        offcriticalSquareMellinKernel s (j + 1))

/-- Finite weighted coarsening identity BEFORE division by q. -/
theorem offcriticalMellin_block_identity
    (a : ℕ → ℂ) (q R : ℕ) (s : ℂ) :
    (∑ j ∈ Finset.Ico (q * R) (q * (R + 1)), a j) *
        offcriticalSquareMellinKernel s (R + 1) =
      offcriticalFineMellinScale s q *
        (∑ j ∈ Finset.Ico (q * R) (q * (R + 1)),
          a j * offcriticalSquareMellinKernel s (j + 1)) +
        offcriticalLocalMellinDefect a q R s := by
  unfold offcriticalLocalMellinDefect
  rw [Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Exact one-block Mellin formula for normalized q-coarsening.
No analytic estimate or finite-boundary-only simplification is used. -/
theorem offcriticalMellin_coarsen_one_block
    (a : ℕ → ℂ) (q R : ℕ) (s : ℂ) :
    offcriticalComplexCoarsen q a R *
        offcriticalSquareMellinKernel s (R + 1) =
      (offcriticalFineMellinScale s q / (q : ℂ)) *
        (∑ j ∈ Finset.Ico (q * R) (q * (R + 1)),
          a j * offcriticalSquareMellinKernel s (j + 1)) +
        offcriticalLocalMellinDefect a q R s / (q : ℂ) := by
  unfold offcriticalComplexCoarsen
  calc
    ((∑ j ∈ Finset.Ico (q * R) (q * (R + 1)), a j) /
        (q : ℂ)) * offcriticalSquareMellinKernel s (R + 1) =
        ((∑ j ∈ Finset.Ico (q * R) (q * (R + 1)), a j) *
          offcriticalSquareMellinKernel s (R + 1)) / (q : ℂ) := by
            ring
    _ = (offcriticalFineMellinScale s q *
        (∑ j ∈ Finset.Ico (q * R) (q * (R + 1)),
          a j * offcriticalSquareMellinKernel s (j + 1)) +
          offcriticalLocalMellinDefect a q R s) / (q : ℂ) := by
            rw [offcriticalMellin_block_identity]
    _ = (offcriticalFineMellinScale s q / (q : ℂ)) *
        (∑ j ∈ Finset.Ico (q * R) (q * (R + 1)),
          a j * offcriticalSquareMellinKernel s (j + 1)) +
        offcriticalLocalMellinDefect a q R s / (q : ℂ) := by
          ring

/-- Finite sum of coarse blocks retains every within-block correction. -/
theorem offcriticalMellin_coarsen_finite
    (a : ℕ → ℂ) (q A B : ℕ) (s : ℂ) :
    (∑ R ∈ Finset.Ico A B,
      offcriticalComplexCoarsen q a R *
        offcriticalSquareMellinKernel s (R + 1)) =
      (offcriticalFineMellinScale s q / (q : ℂ)) *
        (∑ R ∈ Finset.Ico A B,
          ∑ j ∈ Finset.Ico (q * R) (q * (R + 1)),
            a j * offcriticalSquareMellinKernel s (j + 1)) +
        (∑ R ∈ Finset.Ico A B,
          offcriticalLocalMellinDefect a q R s / (q : ℂ)) := by
  simp_rw [offcriticalMellin_coarsen_one_block]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The same exact relation on the physical theta-shortage sequence,
not an altered Euler product or a synthetic VF staircase. -/
theorem offcriticalActualTheta_Mellin_coarsen_finite
    (q A B : ℕ) (s : ℂ) :
    (∑ R ∈ Finset.Ico A B,
      offcriticalComplexCoarsen q
        (fun j => (actualThetaSquareShortage j : ℂ)) R *
          offcriticalSquareMellinKernel s (R + 1)) =
      (offcriticalFineMellinScale s q / (q : ℂ)) *
        (∑ R ∈ Finset.Ico A B,
          ∑ j ∈ Finset.Ico (q * R) (q * (R + 1)),
            (actualThetaSquareShortage j : ℂ) *
              offcriticalSquareMellinKernel s (j + 1)) +
        (∑ R ∈ Finset.Ico A B,
          offcriticalLocalMellinDefect
            (fun j => (actualThetaSquareShortage j : ℂ)) q R s /
              (q : ℂ)) := by
  exact offcriticalMellin_coarsen_finite
    (fun j => (actualThetaSquareShortage j : ℂ)) q A B s

end RHLean.Analysis
