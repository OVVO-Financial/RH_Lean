import Mathlib
import «research.CORR4_ZERO_CUT_QUOTIENT_SUPPORT_20261026»
import «research.CORR4_BRANCHII_OWNER_ANTI_CIRCULAR_20261026»

/-!
# CORR-4: genuine T-free source under a period-36 zero-cut

If L=36q+1 and LT+(H-1)<=X, all source coefficients m<=T
vanish exactly after summing over the actual difference decoder u<L.
This removes the T-gate at the source level, not just after
asymptotic bounding. No assumption on signed Mobius cancellation.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- The full contribution of m<=T vanishes after the actual
physical tent and the literal #919 period-36 quotient decoder. -/
theorem corr4_aligned_low_u_below_T_exactly_zero
    (X H L q T : ℕ)
    (hH : 0 < H) (hL : L = 36 * q + 1)
    (hgate : L * T + (H - 1) ≤ X) :
    (∑ u ∈ Finset.Icc 1 (L - 1),
      corr4SharpQuotientDifference u *
        (∑ m ∈ Finset.Icc 1 T,
          vf919ExcludedNormCoefficients m *
            (corr4TentRamp X H (u * m) : ℂ))) = 0 := by
  have hswap :
      (∑ u ∈ Finset.Icc 1 (L - 1),
        corr4SharpQuotientDifference u *
          (∑ m ∈ Finset.Icc 1 T,
            vf919ExcludedNormCoefficients m *
              (corr4TentRamp X H (u * m) : ℂ))) =
      (∑ m ∈ Finset.Icc 1 T,
        vf919ExcludedNormCoefficients m *
          (∑ u ∈ Finset.Icc 1 (L - 1),
            corr4SharpQuotientDifference u *
              (corr4TentRamp X H (u * m) : ℂ))) := by
    calc
      _ = ∑ u ∈ Finset.Icc 1 (L - 1),
            ∑ m ∈ Finset.Icc 1 T,
              corr4SharpQuotientDifference u *
                (vf919ExcludedNormCoefficients m *
                  (corr4TentRamp X H (u * m) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.mul_sum]
      _ = ∑ m ∈ Finset.Icc 1 T,
            ∑ u ∈ Finset.Icc 1 (L - 1),
              corr4SharpQuotientDifference u *
                (vf919ExcludedNormCoefficients m *
                  (corr4TentRamp X H (u * m) : ℂ)) := Finset.sum_comm
      _ = ∑ m ∈ Finset.Icc 1 T,
            vf919ExcludedNormCoefficients m *
              (∑ u ∈ Finset.Icc 1 (L - 1),
                corr4SharpQuotientDifference u *
                  (corr4TentRamp X H (u * m) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          ring
  rw [hswap]
  apply Finset.sum_eq_zero
  intro m hm
  have hmT : m ≤ T := (Finset.mem_Icc.mp hm).2
  have hdeep : L * m + (H - 1) ≤ X := by
    exact (add_le_add_right (Nat.mul_le_mul_left L hmT) (H - 1)).trans hgate
  rw [corr4_low_quotient_tent_zero_for_small_norm
    X H L q m hH hL hdeep, mul_zero]

/-- The literal low-u high-norm source does not depend on its
auxiliary lower cutoff T when T is behind the 36-aligned gate.
The full source still retains all coefficients and all collars. -/
theorem corr4_aligned_low_u_T_free
    (X H L q T : ℕ)
    (hH : 0 < H) (hL : L = 36 * q + 1)
    (hgate : L * T + (H - 1) ≤ X)
    (hTY : T ≤ X + H - 1) :
    (∑ u ∈ Finset.Icc 1 (L - 1),
      corr4SharpQuotientDifference u *
        (∑ m ∈ Finset.Ioc T (X + H - 1),
          vf919ExcludedNormCoefficients m *
            (corr4TentRamp X H (u * m) : ℂ))) =
    (∑ u ∈ Finset.Icc 1 (L - 1),
      corr4SharpQuotientDifference u *
        (∑ m ∈ Finset.Icc 1 (X + H - 1),
          vf919ExcludedNormCoefficients m *
            (corr4TentRamp X H (u * m) : ℂ))) := by
  let Y := X + H - 1
  have hset :
      Finset.Icc 1 Y = Finset.Icc 1 T ∪ Finset.Ioc T Y := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 T) (Finset.Ioc T Y) := by
    apply Finset.disjoint_left.mpr
    intro m hm1 hm2
    have h1 := (Finset.mem_Icc.mp hm1).2
    have h2 := (Finset.mem_Ioc.mp hm2).1
    omega
  have hsplit (u : ℕ) :
      (∑ m ∈ Finset.Icc 1 Y,
        vf919ExcludedNormCoefficients m *
          (corr4TentRamp X H (u * m) : ℂ)) =
      (∑ m ∈ Finset.Icc 1 T,
        vf919ExcludedNormCoefficients m *
          (corr4TentRamp X H (u * m) : ℂ)) +
      (∑ m ∈ Finset.Ioc T Y,
        vf919ExcludedNormCoefficients m *
          (corr4TentRamp X H (u * m) : ℂ)) := by
    rw [hset, Finset.sum_union hdisj]
  have hsmall := corr4_aligned_low_u_below_T_exactly_zero
    X H L q T hH hL hgate
  change (∑ u ∈ Finset.Icc 1 (L - 1),
      corr4SharpQuotientDifference u *
        (∑ m ∈ Finset.Ioc T Y,
          vf919ExcludedNormCoefficients m *
            (corr4TentRamp X H (u * m) : ℂ))) =
    (∑ u ∈ Finset.Icc 1 (L - 1),
      corr4SharpQuotientDifference u *
        (∑ m ∈ Finset.Icc 1 Y,
          vf919ExcludedNormCoefficients m *
            (corr4TentRamp X H (u * m) : ℂ)))
  calc
    _ = (∑ u ∈ Finset.Icc 1 (L - 1),
          corr4SharpQuotientDifference u *
            (∑ m ∈ Finset.Icc 1 Y,
              vf919ExcludedNormCoefficients m *
                (corr4TentRamp X H (u * m) : ℂ))) -
        (∑ u ∈ Finset.Icc 1 (L - 1),
          corr4SharpQuotientDifference u *
            (∑ m ∈ Finset.Icc 1 T,
              vf919ExcludedNormCoefficients m *
                (corr4TentRamp X H (u * m) : ℂ))) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro u hu
            rw [hsplit u]
            ring
    _ = _ := by rw [hsmall]; ring

#print axioms corr4_aligned_low_u_below_T_exactly_zero
#print axioms corr4_aligned_low_u_T_free

end RHLean.Analysis
