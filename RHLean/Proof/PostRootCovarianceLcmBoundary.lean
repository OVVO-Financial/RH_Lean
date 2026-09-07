import Mathlib
import RHLean.Analysis.BlockCovarianceRefinement
import RHLean.Proof.EndpointCubeAnalyticClosure

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# LCM boundary for the post-root covariance remainder

PR #593 exposed the exact physical pair carrier of the post-root covariance
remainder and the triangular first-separation owner descent on that carrier.
The parent map is necessarily many-to-one.  This file keeps the full pair
geometry instead: first split the remainder by whether the complete squarefree
pair cube fits below the physical endpoint, using the pair lcm as the intrinsic
cube product coordinate.

The interior class has `lcm(m,n) <= W`; the complementary class is the literal
multiplicative boundary `W < lcm(m,n)`.  The split is exact and signed.

The existing fresh-prime four-corner theorem is also specialized to the prefix
cutoff `W+1`: whenever the lower mixed corner `p*m` is already at most `W`, the
complete swapped pair cube has zero boundary mass.  This is the local identity
that the one-parent multiplicity formula suppresses.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Pairs in the post-root remainder whose complete squarefree pair product
coordinate still fits below the physical endpoint. -/
def postRootCovarianceRemainderInteriorLcmCarrier
    (W : ℕ) : Finset (ℕ × ℕ) :=
  (postRootCovarianceRemainderPhysicalPairCarrier W).filter fun mn =>
    Nat.lcm mn.1 mn.2 ≤ W

/-- The literal multiplicative boundary left after the complete-lcm interior is
removed.  These are exactly the remainder pairs with `W < lcm(m,n)`. -/
def postRootCovarianceRemainderBoundaryLcmCarrier
    (W : ℕ) : Finset (ℕ × ℕ) :=
  (postRootCovarianceRemainderPhysicalPairCarrier W).filter fun mn =>
    ¬ Nat.lcm mn.1 mn.2 ≤ W

@[simp] theorem mem_postRootCovarianceRemainderInteriorLcmCarrier
    {W : ℕ} {mn : ℕ × ℕ} :
    mn ∈ postRootCovarianceRemainderInteriorLcmCarrier W ↔
      mn ∈ postRootCovarianceRemainderPhysicalPairCarrier W ∧
        Nat.lcm mn.1 mn.2 ≤ W := by
  simp [postRootCovarianceRemainderInteriorLcmCarrier]

@[simp] theorem mem_postRootCovarianceRemainderBoundaryLcmCarrier
    {W : ℕ} {mn : ℕ × ℕ} :
    mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W ↔
      mn ∈ postRootCovarianceRemainderPhysicalPairCarrier W ∧
        W < Nat.lcm mn.1 mn.2 := by
  simp [postRootCovarianceRemainderBoundaryLcmCarrier]

/-- Exact signed partition of the #593 physical remainder carrier into complete
lcm fibres and the super-endpoint multiplicative boundary. -/
theorem postRootCovarianceRemainder_lcm_partition
    (W : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ postRootCovarianceRemainderInteriorLcmCarrier W, f mn) +
        (∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W, f mn) =
      ∑ mn ∈ postRootCovarianceRemainderPhysicalPairCarrier W, f mn := by
  unfold postRootCovarianceRemainderInteriorLcmCarrier
    postRootCovarianceRemainderBoundaryLcmCarrier
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- The scalar post-root remainder is exactly the sum of its complete-lcm
interior and its multiplicative boundary, with Möbius signs retained. -/
theorem postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm
    (W : ℕ) :
    postRootCovarianceRemainder W =
      (∑ mn ∈ postRootCovarianceRemainderInteriorLcmCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) +
      ∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
  rw [postRootCovarianceRemainder_eq_physicalPairCarrier]
  exact (postRootCovarianceRemainder_lcm_partition W
    (fun mn : ℕ × ℕ =>
      realMoebiusStep mn.1 * realMoebiusStep mn.2)).symm

/-- **A complete owner pair cube cancels before any norm.**  At prefix cutoff
`W+1`, if the lower mixed corner `p*m` is already physical, the top-escape
indicator in the existing four-corner recombination is false.  Hence the two
orientations of the entire fresh-prime pair cube sum to zero exactly. -/
theorem realMoebiusPairFourCornerMass_add_swap_eq_zero_of_lowerCorner
    {p W m n : ℕ} (hp : p.Prime) (hmn : m < n)
    (hpm : ¬ p ∣ m) (hpn : ¬ p ∣ n)
    (hlower : p * m ≤ W) :
    realMoebiusPairFourCornerMass p (W + 1) m n +
        realMoebiusPairFourCornerMass p (W + 1) n m = 0 := by
  rw [realMoebiusPairFourCornerMass_add_swap_eq_topEscape
    hp hmn hpm hpn]
  have hnot : ¬ W + 1 ≤ p * m := by omega
  simp [hnot]

end RHLean.Proof
