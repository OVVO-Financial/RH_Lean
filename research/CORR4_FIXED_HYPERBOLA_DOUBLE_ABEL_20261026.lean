import Mathlib
import «research.VF_MID_919_QUOTIENT_SIGNED_RETURN»

/-!
# CORR-4: exact fixed-owner hyperbola and second quotient Abel transport

Finite identities only. No signed source power saving, zero-free-region
short-interval estimate, global Mertens exponent, or RH theorem is asserted.

The first quotient-kernel primitive and its sharp [-4,4] range are ALREADY
certified by VF_MID_919_QUOTIENT_SIGNED_RETURN. We reuse those declarations.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Universal first discrete Abel identity for a difference kernel,
including its *upper* boundary term. It is valid at N=0. -/
theorem corr4_difference_kernel_signed_abel
    (N : ℕ) (k b : ℕ → ℂ) (hk0 : k 0 = 0) :
    (∑ t ∈ Finset.Icc 1 N, (k t - k (t - 1)) * b t) =
      (∑ t ∈ Finset.Icc 1 N, k t * (b t - b (t + 1))) +
        k N * b (N + 1) := by
  induction N with
  | zero =>
      simp [hk0]
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      rw [ih, show N + 1 - 1 = N by omega]
      ring

/-- The original #919 quotient kernel starts at zero; an indispensable
lower boundary fact in its difference-kernel Abel identity. -/
theorem corr4_sharp_quotient_kernel_zero :
    (vf919SharpQuotientKernel36 0 : ℂ) = 0 := by
  norm_num [vf919SharpQuotientKernel36,
    vf919IntegerCharacterPrefix_eq_residue]

/-- Two exact Abel transformations for the *actual* 36-period kernel.
The terminating quotient buckets B(N+1), B(N+2) are explicitly zero:
without them, the two boundary terms must be retained.

The bounded primitive on the right is the already-compiled literal
vf919QuotientKernelPrimitive36, not a new probabilistic cancellation. -/
theorem corr4_sharp_quotient_double_abel
    (N : ℕ) (b : ℕ → ℂ)
    (hend1 : b (N + 1) = 0) (hend2 : b (N + 2) = 0) :
    (∑ t ∈ Finset.Icc 1 N,
      ((vf919SharpQuotientKernel36 t : ℂ) -
        (vf919SharpQuotientKernel36 (t - 1) : ℂ)) * b t) =
      ∑ t ∈ Finset.Icc 1 N,
        (vf919QuotientKernelPrimitive36 t : ℂ) *
          (b t - 2 * b (t + 1) + b (t + 2)) := by
  have hfirst :=
    corr4_difference_kernel_signed_abel N
      (fun t => (vf919SharpQuotientKernel36 t : ℂ))
      b corr4_sharp_quotient_kernel_zero
  have hsecond :=
    vf919QuotientKernel36_signed_abel N
      (fun t => b t - b (t + 1))
  have hterminal : b (N + 1) - b (N + 1 + 1) = 0 := by
    rw [show N + 1 + 1 = N + 2 by omega, hend1, hend2]
    ring
  calc
    _ = ∑ t ∈ Finset.Icc 1 N,
        (vf919SharpQuotientKernel36 t : ℂ) * (b t - b (t + 1)) := by
        rw [hfirst, hend1]
        ring
    _ = ∑ t ∈ Finset.Icc 1 N,
        (vf919QuotientKernelPrimitive36 t : ℂ) *
          ((b t - b (t + 1)) - (b (t + 1) - b (t + 1 + 1))) := by
        rw [hterminal] at hsecond
        simpa using hsecond
    _ = ∑ t ∈ Finset.Icc 1 N,
        (vf919QuotientKernelPrimitive36 t : ℂ) *
          (b t - 2 * b (t + 1) + b (t + 2)) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [show t + 1 + 1 = t + 2 by omega]
        ring

/-- A cutoff-independent finite hyperbola *owner partition*.
Applying it with the finite hyperbola domain ab≤Y, then evaluating the
inner b- and a-prefix sums, produces the asymmetric Dirichlet formula.
No square-root cutoff is present; this is an unconditional identity. -/
theorem corr4_fixed_owner_hyperbola_partition
    (Y y0 : ℕ) (f g : ℕ → ℂ) :
    (∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
      if a * b ≤ Y then f a * g b else 0) =
      (∑ a ∈ Finset.Icc 1 Y,
        if a ≤ y0 then
          (∑ b ∈ Finset.Icc 1 Y,
            if a * b ≤ Y then f a * g b else 0)
        else 0) +
      (∑ b ∈ Finset.Icc 1 Y, ∑ a ∈ Finset.Icc 1 Y,
        if y0 < a ∧ a * b ≤ Y then f a * g b else 0) := by
  calc
    (∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
        if a * b ≤ Y then f a * g b else 0) =
      (∑ a ∈ Finset.Icc 1 Y,
        (∑ b ∈ Finset.Icc 1 Y,
          if a ≤ y0 then (if a * b ≤ Y then f a * g b else 0) else 0) +
        (∑ b ∈ Finset.Icc 1 Y,
          if y0 < a ∧ a * b ≤ Y then f a * g b else 0)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b hb
        by_cases h : a ≤ y0
        · simp [h, Nat.not_lt.mpr h]
        · have hgt : y0 < a := by omega
          simp [h, hgt]
    _ = (∑ a ∈ Finset.Icc 1 Y,
          if a ≤ y0 then
            (∑ b ∈ Finset.Icc 1 Y,
              if a * b ≤ Y then f a * g b else 0)
          else 0) +
        (∑ b ∈ Finset.Icc 1 Y, ∑ a ∈ Finset.Icc 1 Y,
          if y0 < a ∧ a * b ≤ Y then f a * g b else 0) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro a ha
          by_cases h : a ≤ y0 <;> simp [h]
        · exact Finset.sum_comm

#print axioms corr4_difference_kernel_signed_abel
#print axioms corr4_sharp_quotient_double_abel
#print axioms corr4_fixed_owner_hyperbola_partition

end RHLean.Analysis
