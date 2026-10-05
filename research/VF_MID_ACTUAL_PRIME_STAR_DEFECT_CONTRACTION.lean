import Mathlib
import «research.VF_MID_ACTUAL_PRIME_ROOT_SQUARE_CONTRACTION»
import «research.VF_MID_PROXY_ENERGY_PULL»

/-!
# Actual-prime protected star: summed physical-defect contraction

The root-square attack already proves the exact fixed-parent star identity

  v(m) + sum_q v(m*q)
    = (1 - sum_q 1/q) * v(m) + sum_q D(m,q),

while the proxy-energy file proves the missing pointwise physical estimate

  |D(m,q)| <= (1/q) * |v(m)|.

This file composes those two compiled facts before any new carrier change.
Consequently the *whole signed defect star* costs at most the same reciprocal
owner mass, and every star is nonexpansive whenever its reciprocal owner mass
is at most one.

No PNT replacement, packet inheritance, or independence assumption enters.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The complete signed physical-defect star is paid by exactly the reciprocal
mass of its actual prime owners. -/
theorem abs_vfMidActualHighPrimeProtectedStarDefectMass_le
    (R m : ℕ) (hR : 3 ≤ R) (hm : 1 ≤ m) :
    |vfMidActualHighPrimeProtectedStarDefectMass R m| ≤
      vfMidActualHighPrimeStarReciprocalMass R m *
        |nativePNTSignedSquareBlockCorrelationReciprocalSummand
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| := by
  unfold vfMidActualHighPrimeProtectedStarDefectMass
    vfMidActualHighPrimeStarReciprocalMass
  calc
    |∑ q ∈ vfMidActualHighPrimeStarSet R m,
        nativePNTSignedSquareBlockFreshPrimePhysicalDefect
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m q| ≤
      ∑ q ∈ vfMidActualHighPrimeStarSet R m,
        |nativePNTSignedSquareBlockFreshPrimePhysicalDefect
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ vfMidActualHighPrimeStarSet R m,
        (1 / (q : ℝ)) *
          |nativePNTSignedSquareBlockCorrelationReciprocalSummand
            ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| := by
      apply Finset.sum_le_sum
      intro q hq
      have hqData := Finset.mem_filter.mp hq
      have hcarrier := Finset.mem_filter.mp hqData.1
      have hqPrime : q.Prime := hcarrier.2
      exact
        vfMidProtectedBlockFreshPrimePhysicalDefect_abs_le_inv_mul_parent
          (M := R ^ 2) (L := (R + 1) ^ 2)
          (m := m) (p := q)
          (by nlinarith : (R + 1) ^ 2 < 2 * R ^ 2)
          (by omega : 0 < m) hqPrime
    _ = (∑ q ∈ vfMidActualHighPrimeStarSet R m, 1 / (q : ℝ)) *
        |nativePNTSignedSquareBlockCorrelationReciprocalSummand
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| := by
      rw [Finset.sum_mul]

/-- **Complete actual-prime high-owner star contraction.**

If the legal star has reciprocal mass at most one, the retained-parent part and
the summed signed physical defects exactly fill complementary fractions of the
same parent absolute mass. -/
theorem abs_vfMidActualHighPrimeProtectedStarMass_le_parent
    (R m : ℕ) (hR : 3 ≤ R) (hm : 1 ≤ m)
    (hmass : vfMidActualHighPrimeStarReciprocalMass R m ≤ 1) :
    |vfMidActualHighPrimeProtectedStarMass R m| ≤
      |nativePNTSignedSquareBlockCorrelationReciprocalSummand
        ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| := by
  rw [vfMidActualHighPrimeProtectedStarMass_eq R m
    (by omega : 2 ≤ R) hm]
  have hS0 : 0 ≤ vfMidActualHighPrimeStarReciprocalMass R m := by
    unfold vfMidActualHighPrimeStarReciprocalMass
    apply Finset.sum_nonneg
    intro q hq
    have hqPrime :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqPrime.pos
    positivity
  have hcoef0 :
      0 ≤ 1 - vfMidActualHighPrimeStarReciprocalMass R m :=
    sub_nonneg.mpr hmass
  have hdef :=
    abs_vfMidActualHighPrimeProtectedStarDefectMass_le R m hR hm
  calc
    |(1 - vfMidActualHighPrimeStarReciprocalMass R m) *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand
            ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m +
        vfMidActualHighPrimeProtectedStarDefectMass R m| ≤
      |(1 - vfMidActualHighPrimeStarReciprocalMass R m) *
          nativePNTSignedSquareBlockCorrelationReciprocalSummand
            ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| +
        |vfMidActualHighPrimeProtectedStarDefectMass R m| :=
      abs_add_le _ _
    _ = (1 - vfMidActualHighPrimeStarReciprocalMass R m) *
          |nativePNTSignedSquareBlockCorrelationReciprocalSummand
            ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| +
        |vfMidActualHighPrimeProtectedStarDefectMass R m| := by
      rw [abs_mul, abs_of_nonneg hcoef0]
    _ ≤ (1 - vfMidActualHighPrimeStarReciprocalMass R m) *
          |nativePNTSignedSquareBlockCorrelationReciprocalSummand
            ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| +
        vfMidActualHighPrimeStarReciprocalMass R m *
          |nativePNTSignedSquareBlockCorrelationReciprocalSummand
            ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| :=
      add_le_add_left hdef _
    _ = |nativePNTSignedSquareBlockCorrelationReciprocalSummand
          ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| := by
      ring

/-- The complete root-to-square reciprocal owner bound is sufficient for every
fixed-parent star. -/
theorem abs_vfMidActualHighPrimeProtectedStarMass_le_parent_of_rootMass
    (R m : ℕ) (hR : 3 ≤ R) (hm : 1 ≤ m)
    (hroot : vfMidActualRootSquareReciprocalPrimeMass R ≤ 1) :
    |vfMidActualHighPrimeProtectedStarMass R m| ≤
      |nativePNTSignedSquareBlockCorrelationReciprocalSummand
        ((R + 1) ^ 2) (R ^ 2) ((R + 1) ^ 2) m| := by
  apply abs_vfMidActualHighPrimeProtectedStarMass_le_parent R m hR hm
  exact
    (vfMidActualHighPrimeStarReciprocalMass_le_rootSquare R m).trans hroot

end RHLean.Proof
