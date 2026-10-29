import Mathlib
import RHLean.Analysis.CanonicalLowOccupancy

/-!
# Off-critical LOW/HIGH: genuine integer coefficients and absolute LOW occupancy

The canonical signed height cut partitions each ACTUAL Mobius coefficient.
This module first proves a global, all-integer positive-mass census for LOW,
not just a signed square-prefix estimate. It is an unconditional arithmetic
input for the later LOW Dirichlet-series half-plane.

No zeta-zero assumption, conjectural cancellation, or project axiom occurs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The literal canonical LOW Mobius coefficient at every natural integer. -/
def offcriticalLowCoefficient (Lambda : ℝ) (m : ℕ) : ℂ :=
  if IsCanonicalLowHeight Lambda (Nat.sqrt m) m then
    canonicalMoebiusWeight m else 0

/-- The literal complementary canonical HIGH Mobius coefficient. -/
def offcriticalHighCoefficient (Lambda : ℝ) (m : ℕ) : ℂ :=
  if IsCanonicalHighHeight Lambda (Nat.sqrt m) m then
    canonicalMoebiusWeight m else 0

/-- Coefficient-level LOW plus HIGH equals the original Mobius atom. -/
theorem offcriticalLow_add_high_eq_moebius
    (Lambda : ℝ) (m : ℕ) :
    offcriticalLowCoefficient Lambda m +
      offcriticalHighCoefficient Lambda m =
        canonicalMoebiusWeight m := by
  by_cases h : IsCanonicalLowHeight Lambda (Nat.sqrt m) m
  · simp [offcriticalLowCoefficient, offcriticalHighCoefficient,
      IsCanonicalHighHeight, h]
  · simp [offcriticalLowCoefficient, offcriticalHighCoefficient,
      IsCanonicalHighHeight, h]

/-- The genuine nonzero LOW support up to EVERY integer N. -/
def offcriticalLowSupportUpTo (Lambda : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun m =>
    μ m ≠ 0 ∧ IsCanonicalLowHeight Lambda (Nat.sqrt m) m

/-- The support of a LOW atom lies in its UNIQUE integer square block. -/
theorem offcriticalLowSupport_mem_squareBlock
    {Lambda : ℝ} {N m : ℕ}
    (hm : m ∈ offcriticalLowSupportUpTo Lambda N) :
    m ∈ canonicalLowSupport Lambda (Nat.sqrt m) := by
  classical
  rcases Finset.mem_filter.mp hm with ⟨_hmN, hmMu, hmLow⟩
  have hmBlock :
      m ∈ canonicalSquareBlock (Nat.sqrt m) := by
    change m ∈ Finset.Ico ((Nat.sqrt m) ^ 2) ((Nat.sqrt m + 1) ^ 2)
    exact Finset.mem_Ico.mpr ⟨Nat.sqrt_le' m, Nat.lt_succ_sqrt' m⟩
  exact Finset.mem_filter.mpr ⟨hmBlock, hmMu, hmLow⟩

/-- At any natural cutoff N, the number of nonzero LOW coefficients grows
at most at square-root scale, with the EXACT fixed-height occupancy constant.
No Mobius cancellation is needed. -/
theorem offcriticalLowSupport_card_le
    (Lambda : ℝ) (N : ℕ) :
    (offcriticalLowSupportUpTo Lambda N).card ≤
      (Nat.sqrt N + 1) * (Nat.floor Lambda + 1) := by
  classical
  let cover : Finset ℕ :=
    (Finset.range (Nat.sqrt N + 1)).biUnion
      (canonicalLowSupport Lambda)
  have hsub : offcriticalLowSupportUpTo Lambda N ⊆ cover := by
    intro m hm
    have hmrange :
        m ∈ Finset.range (N + 1) :=
      (Finset.mem_filter.mp hm).1
    have hmle : m ≤ N := by
      have hmlt := Finset.mem_range.mp hmrange
      omega
    have hroot : Nat.sqrt m ≤ Nat.sqrt N :=
      Nat.sqrt_le_sqrt hmle
    exact Finset.mem_biUnion.mpr
      ⟨Nat.sqrt m, Finset.mem_range.mpr (by omega),
       offcriticalLowSupport_mem_squareBlock hm⟩
  calc
    (offcriticalLowSupportUpTo Lambda N).card ≤ cover.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (Nat.sqrt N + 1),
          (canonicalLowSupport Lambda j).card := by
            exact Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (Nat.sqrt N + 1),
          (Nat.floor Lambda + 1) := by
            apply Finset.sum_le_sum
            intro j _hj
            exact card_canonicalLowSupport_le_floor_add_one Lambda j
    _ = (Nat.sqrt N + 1) * (Nat.floor Lambda + 1) := by simp

/-- All-integer absolute LOW mass satisfies the same unconditional
square-root occupancy estimate. This is STRONGER than a signed prefix bound,
and is the correct input for absolute Dirichlet-series convergence. -/
theorem offcriticalLow_normSum_le
    (Lambda : ℝ) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1),
      ‖offcriticalLowCoefficient Lambda m‖) ≤
        (((Nat.sqrt N + 1) * (Nat.floor Lambda + 1) : ℕ) : ℝ) := by
  classical
  calc
    (∑ m ∈ Finset.range (N + 1),
        ‖offcriticalLowCoefficient Lambda m‖) ≤
      ∑ m ∈ Finset.range (N + 1),
        if μ m ≠ 0 ∧ IsCanonicalLowHeight Lambda (Nat.sqrt m) m
        then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro m _hm
          by_cases hmMu : μ m = 0
          · simp [offcriticalLowCoefficient, canonicalMoebiusWeight, hmMu]
          · by_cases hmLow : IsCanonicalLowHeight Lambda (Nat.sqrt m) m
            · simpa [offcriticalLowCoefficient, hmMu, hmLow] using
                norm_canonicalMoebiusWeight_le_one m
            · simp [offcriticalLowCoefficient, hmLow]
    _ = ((offcriticalLowSupportUpTo Lambda N).card : ℝ) := by
          simp [offcriticalLowSupportUpTo]
    _ ≤ (((Nat.sqrt N + 1) * (Nat.floor Lambda + 1) : ℕ) : ℝ) := by
          exact_mod_cast offcriticalLowSupport_card_le Lambda N

end RHLean.Proof
