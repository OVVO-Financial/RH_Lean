import Mathlib
import RHLean.Proof.BalancedCanonicalGap

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

namespace CanonicalGapPrefixGram

/-!
# Canonical-gap prefix energy ledger

The high canonical-gap increment is the exact sum of its balanced and extreme
parts.  This file records the corresponding exact prefix-energy decomposition.
It is pure finite algebra: no cancellation estimate is asserted.
-/

/-- Prefix sum through index `r`, inclusive. -/
def prefix (a : ℕ → ℤ) (r : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (r + 1), a j

/-- Prefix energy over `H` successive prefixes. -/
def prefixEnergy (H : ℕ) (a : ℕ → ℤ) : ℤ :=
  ∑ r ∈ Finset.range H, prefix a r ^ 2

/-- Twice the signed cross energy of two prefix paths. -/
def twicePrefixCross (H : ℕ) (a b : ℕ → ℤ) : ℤ :=
  ∑ r ∈ Finset.range H, 2 * prefix a r * prefix b r

@[simp] theorem prefix_add (a b : ℕ → ℤ) (r : ℕ) :
    prefix (fun j => a j + b j) r = prefix a r + prefix b r := by
  simp [prefix, Finset.sum_add_distrib]

/-- The signed cross energy is symmetric. -/
theorem twicePrefixCross_comm (H : ℕ) (a b : ℕ → ℤ) :
    twicePrefixCross H a b = twicePrefixCross H b a := by
  unfold twicePrefixCross
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Exact two-channel prefix-energy ledger. -/
theorem prefixEnergy_add (H : ℕ) (a b : ℕ → ℤ) :
    prefixEnergy H (fun j => a j + b j) =
      prefixEnergy H a + twicePrefixCross H a b + prefixEnergy H b := by
  unfold prefixEnergy twicePrefixCross
  calc
    (∑ r ∈ Finset.range H, prefix (fun j => a j + b j) r ^ 2) =
        ∑ r ∈ Finset.range H,
          (prefix a r ^ 2 + 2 * prefix a r * prefix b r + prefix b r ^ 2) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [prefix_add]
      ring
    _ = (∑ r ∈ Finset.range H, prefix a r ^ 2) +
          (∑ r ∈ Finset.range H, 2 * prefix a r * prefix b r) +
          (∑ r ∈ Finset.range H, prefix b r ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

open BalancedCanonicalGap

/-- The high canonical-gap increment on the shifted block window. -/
def highWindowIncrement (K : ℕ → ℕ) (N r : ℕ) : ℤ :=
  highBandBlockIncrement (N + r) (K (N + r))

/-- The balanced high canonical-gap increment on the shifted block window. -/
def balancedWindowIncrement (K : ℕ → ℕ) (N r : ℕ) : ℤ :=
  balancedHighBandBlockIncrement (N + r) (K (N + r))

/-- The extreme high canonical-gap increment on the shifted block window. -/
def extremeWindowIncrement (K : ℕ → ℕ) (N r : ℕ) : ℤ :=
  extremeHighBandBlockIncrement (N + r) (K (N + r))

/-- Pointwise balanced/extreme reconstruction on a shifted window. -/
theorem highWindowIncrement_eq_balanced_add_extreme
    (K : ℕ → ℕ) (N r : ℕ) :
    highWindowIncrement K N r =
      balancedWindowIncrement K N r + extremeWindowIncrement K N r := by
  exact highBandBlockIncrement_eq_balanced_add_extreme
    (N + r) (K (N + r))

/-- Exact balanced/extreme prefix-energy decomposition for every finite window. -/
theorem canonicalGapPrefixEnergy_decomposition
    (K : ℕ → ℕ) (N H : ℕ) :
    prefixEnergy H (highWindowIncrement K N) =
      prefixEnergy H (balancedWindowIncrement K N) +
      twicePrefixCross H (balancedWindowIncrement K N)
        (extremeWindowIncrement K N) +
      prefixEnergy H (extremeWindowIncrement K N) := by
  have hfun : highWindowIncrement K N =
      fun r => balancedWindowIncrement K N r + extremeWindowIncrement K N r := by
    funext r
    exact highWindowIncrement_eq_balanced_add_extreme K N r
  rw [hfun]
  exact prefixEnergy_add H (balancedWindowIncrement K N)
    (extremeWindowIncrement K N)

end CanonicalGapPrefixGram

end RHLean.Proof
