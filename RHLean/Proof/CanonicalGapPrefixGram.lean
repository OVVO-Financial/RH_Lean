import Mathlib
import RHLean.Proof.BalancedCanonicalGap

open scoped BigOperators

namespace RHLean.Proof

namespace CanonicalGapPrefixGram

/-!
# Prefix Gram identities for the balanced/extreme split

The arithmetic module `BalancedCanonicalGap.lean` produces two integer block-increment
sequences: the balanced part and the extreme part. This file records the exact finite
prefix-energy algebra. No analytic estimate is assumed.
-/

/-- Prefix sum inside a fixed window of length `H`. The value at `r` uses all
indices `i < H` with `i ≤ r`. -/
def prefixSum (H : ℕ) (a : ℕ → ℤ) (r : ℕ) : ℤ :=
  ∑ i ∈ Finset.range H, if i ≤ r then a i else 0

/-- Bilinear prefix Gram form. -/
def prefixCrossEnergy (H : ℕ) (a b : ℕ → ℤ) : ℤ :=
  ∑ r ∈ Finset.range H, prefixSum H a r * prefixSum H b r

/-- Quadratic prefix energy. -/
def prefixEnergy (H : ℕ) (a : ℕ → ℤ) : ℤ :=
  prefixCrossEnergy H a a

/-- Number of prefixes in a length-`H` window containing both coordinates `i` and
`j`. -/
def prefixKernelCount (H i j : ℕ) : ℕ :=
  ((Finset.range H).filter fun r => i ≤ r ∧ j ≤ r).card

/-- Explicit kernel-weighted bilinear form. -/
def kernelCrossEnergy (H : ℕ) (a b : ℕ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
    (prefixKernelCount H i j : ℤ) * a i * b j

/-- Prefix sums are additive. -/
theorem prefixSum_add (H : ℕ) (a b : ℕ → ℤ) (r : ℕ) :
    prefixSum H (fun i => a i + b i) r = prefixSum H a r + prefixSum H b r := by
  unfold prefixSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hir : i ≤ r <;> simp [hir]

/-- The prefix Gram form is additive in its first argument. -/
theorem prefixCrossEnergy_add_left
    (H : ℕ) (a b c : ℕ → ℤ) :
    prefixCrossEnergy H (fun i => a i + b i) c =
      prefixCrossEnergy H a c + prefixCrossEnergy H b c := by
  unfold prefixCrossEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [prefixSum_add]
  ring

/-- The prefix Gram form is additive in its second argument. -/
theorem prefixCrossEnergy_add_right
    (H : ℕ) (a b c : ℕ → ℤ) :
    prefixCrossEnergy H a (fun i => b i + c i) =
      prefixCrossEnergy H a b + prefixCrossEnergy H a c := by
  unfold prefixCrossEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [prefixSum_add]
  ring

/-- The prefix Gram form is symmetric. -/
theorem prefixCrossEnergy_comm (H : ℕ) (a b : ℕ → ℤ) :
    prefixCrossEnergy H a b = prefixCrossEnergy H b a := by
  unfold prefixCrossEnergy
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- The exact balanced/extreme prefix-energy ledger. -/
theorem prefixEnergy_add (H : ℕ) (a b : ℕ → ℤ) :
    prefixEnergy H (fun i => a i + b i) =
      prefixEnergy H a + 2 * prefixCrossEnergy H a b + prefixEnergy H b := by
  unfold prefixEnergy
  rw [prefixCrossEnergy_add_left]
  simp_rw [prefixCrossEnergy_add_right]
  rw [prefixCrossEnergy_comm H b a]
  ring

/-- Counting a terminal interval in `range H`. -/
theorem card_filter_ge (H t : ℕ) :
    ((Finset.range H).filter fun r => t ≤ r).card = H - t := by
  have hset :
      (Finset.range H).filter (fun r => t ≤ r) = Finset.Ico t H := by
    ext r
    simp [and_comm]
  rw [hset]
  simp

/-- The prefix Gram kernel has the closed form `H - max i j`. -/
theorem prefixKernelCount_eq_sub_max (H i j : ℕ) :
    prefixKernelCount H i j = H - max i j := by
  unfold prefixKernelCount
  have hfilter :
      (Finset.range H).filter (fun r => i ≤ r ∧ j ≤ r) =
        (Finset.range H).filter (fun r => max i j ≤ r) := by
    apply Finset.filter_congr
    intro r _hr
    omega
  rw [hfilter, card_filter_ge]

/-- Expansion of one prefix product into coordinate pairs. -/
theorem prefixSum_mul_prefixSum (H : ℕ) (a b : ℕ → ℤ) (r : ℕ) :
    prefixSum H a r * prefixSum H b r =
      ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        if i ≤ r ∧ j ≤ r then a i * b j else 0 := by
  unfold prefixSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
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
    (∑ r ∈ Finset.range H, ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        if i ≤ r ∧ j ≤ r then a i * b j else 0) =
        ∑ i ∈ Finset.range H, ∑ r ∈ Finset.range H, ∑ j ∈ Finset.range H,
          if i ≤ r ∧ j ≤ r then a i * b j else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, ∑ r ∈ Finset.range H,
          if i ≤ r ∧ j ≤ r then a i * b j else 0 := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
          (prefixKernelCount H i j : ℤ) * a i * b j := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            rw [← Finset.sum_filter]
            simp [prefixKernelCount, mul_assoc]

/-- Closed-form kernel identity. -/
theorem prefixCrossEnergy_eq_sub_max_kernel
    (H : ℕ) (a b : ℕ → ℤ) :
    prefixCrossEnergy H a b =
      ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        ((H - max i j : ℕ) : ℤ) * a i * b j := by
  rw [prefixCrossEnergy_eq_kernelCrossEnergy]
  unfold kernelCrossEnergy
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
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
