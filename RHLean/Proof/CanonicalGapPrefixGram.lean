import Mathlib
import RHLean.Proof.BalancedCanonicalGap

open scoped BigOperators

namespace RHLean.Proof

namespace CanonicalGapPrefixGram

/-!
# Prefix Gram identities for the balanced/extreme split

The arithmetic module `BalancedCanonicalGap.lean` produces two integer block-increment
sequences: the balanced part and the extreme part.  This file records the exact finite
prefix-energy algebra.  No analytic estimate is assumed.
-/

/-- Prefix sum inside a fixed window of length `H`.  The value at `r` uses all
indices `i < H` with `i ≤ r`. -/
def prefixSum (H : ℕ) (a : ℕ → ℤ) (r : ℕ) : ℤ :=
  ∑ i in Finset.range H, if i ≤ r then a i else 0

/-- Bilinear prefix Gram form. -/
def prefixCrossEnergy (H : ℕ) (a b : ℕ → ℤ) : ℤ :=
  ∑ r in Finset.range H, prefixSum H a r * prefixSum H b r

/-- Quadratic prefix energy. -/
def prefixEnergy (H : ℕ) (a : ℕ → ℤ) : ℤ :=
  prefixCrossEnergy H a a

/-- Number of prefixes in a length-`H` window containing both coordinates `i` and
`j`. -/
def prefixKernelCount (H i j : ℕ) : ℕ :=
  ((Finset.range H).filter fun r => i ≤ r ∧ j ≤ r).card

/-- Explicit kernel-weighted bilinear form. -/
def kernelCrossEnergy (H : ℕ) (a b : ℕ → ℤ) : ℤ :=
  ∑ i in Finset.range H, ∑ j in Finset.range H,
    (prefixKernelCount H i j : ℤ) * a i * b j

/-- Prefix sums are additive. -/
theorem prefixSum_add (H : ℕ) (a b : ℕ → ℤ) (r : ℕ) :
    prefixSum H (fun i => a i + b i) r = prefixSum H a r + prefixSum H b r := by
  unfold prefixSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hir : i ≤ r <;> simp [hir]

/-- The exact balanced/extreme prefix-energy ledger. -/
theorem prefixEnergy_add (H : ℕ) (a b : ℕ → ℤ) :
    prefixEnergy H (fun i => a i + b i) =
      prefixEnergy H a + 2 * prefixCrossEnergy H a b + prefixEnergy H b := by
  unfold prefixEnergy prefixCrossEnergy
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [prefixSum_add]
  ring

/-- Counting a terminal interval in `range H`. -/
theorem card_filter_ge (H t : ℕ) :
    ((Finset.range H).filter fun r => t ≤ r).card = H - t := by
  induction H with
  | zero => simp
  | succ H ih =>
      by_cases h : t ≤ H
      · simp [Finset.range_succ, h, ih]
        omega
      · have hHt : H < t := by omega
        simp [Finset.range_succ, h, ih]
        omega

/-- The prefix Gram kernel has the closed form `H - max i j`. -/
theorem prefixKernelCount_eq_sub_max (H i j : ℕ) :
    prefixKernelCount H i j = H - max i j := by
  unfold prefixKernelCount
  have hfilter :
      (Finset.range H).filter (fun r => i ≤ r ∧ j ≤ r) =
        (Finset.range H).filter (fun r => max i j ≤ r) := by
    apply Finset.filter_congr
    intro r hr
    omega
  rw [hfilter, card_filter_ge]

/-- Expansion of one prefix product into coordinate pairs. -/
theorem prefixSum_mul_prefixSum (H : ℕ) (a b : ℕ → ℤ) (r : ℕ) :
    prefixSum H a r * prefixSum H b r =
      ∑ i in Finset.range H, ∑ j in Finset.range H,
        if i ≤ r ∧ j ≤ r then a i * b j else 0 := by
  unfold prefixSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hir : i ≤ r <;> by_cases hjr : j ≤ r <;> simp [hir, hjr]

/-- The prefix-summation energy is exactly the Gram form with kernel counting the
common future prefixes. -/
theorem prefixCrossEnergy_eq_kernelCrossEnergy
    (H : ℕ) (a b : ℕ → ℤ) :
    prefixCrossEnergy H a b = kernelCrossEnergy H a b := by
  classical
  unfold prefixCrossEnergy kernelCrossEnergy
  simp_rw [prefixSum_mul_prefixSum]
  calc
    (∑ r in Finset.range H, ∑ i in Finset.range H, ∑ j in Finset.range H,
        if i ≤ r ∧ j ≤ r then a i * b j else 0) =
        ∑ i in Finset.range H, ∑ r in Finset.range H, ∑ j in Finset.range H,
          if i ≤ r ∧ j ≤ r then a i * b j else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ i in Finset.range H, ∑ j in Finset.range H, ∑ r in Finset.range H,
          if i ≤ r ∧ j ≤ r then a i * b j else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_comm]
    _ = ∑ i in Finset.range H, ∑ j in Finset.range H,
          (prefixKernelCount H i j : ℤ) * a i * b j := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_filter]
            simp [prefixKernelCount]

/-- Closed-form kernel identity. -/
theorem prefixCrossEnergy_eq_sub_max_kernel
    (H : ℕ) (a b : ℕ → ℤ) :
    prefixCrossEnergy H a b =
      ∑ i in Finset.range H, ∑ j in Finset.range H,
        ((H - max i j : ℕ) : ℤ) * a i * b j := by
  rw [prefixCrossEnergy_eq_kernelCrossEnergy]
  unfold kernelCrossEnergy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [prefixKernelCount_eq_sub_max]

/-- Instantiation of the exact ledger for the arithmetic balanced/extreme block
increments. -/
theorem balanced_extreme_prefix_energy_ledger
    (H N K : ℕ) :
    prefixEnergy H
        (fun r =>
          BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K +
          BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K) =
      prefixEnergy H
          (fun r => BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K) +
      2 * prefixCrossEnergy H
          (fun r => BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K)
          (fun r => BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K) +
      prefixEnergy H
          (fun r => BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K) := by
  exact prefixEnergy_add H
    (fun r => BalancedCanonicalGap.balancedHighBandBlockIncrement (N + r) K)
    (fun r => BalancedCanonicalGap.extremeHighBandBlockIncrement (N + r) K)

end CanonicalGapPrefixGram

end RHLean.Proof
