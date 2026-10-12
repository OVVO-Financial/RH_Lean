import Mathlib
import «research.VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_CONTINUATION_LEDGER»

/-!
# Original VF clipped/admitted carrier is disjoint from sector-six admitted pairs

The original first-bad weighted returned source has literal support on
  clippedBase(R+1,p,sig) × admittedBase(R+1,p,sig).
The generic Dirichlet greatest-owner / sector-six descent begins instead on
  admittedBase(R+1,p,sig) × admittedBase(R+1,p,sig).

They are disjoint for each original first-owner cell: p*a cannot be
simultaneously greater than the physical cutoff and at most the cutoff.
Thus no identity-on-pairs or zero-extension shortcut can turn the original
VF mixed clipped/admitted boundary into a paid admitted/admitted sector-six
contribution. A legal bridge must transport a HISTORICAL counterpart,
preserving signed weights, multiplicities, both walls and the full anchor.

These are elementary carrier theorems, not the open quantitative payment.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Literal original VF returned pairs cannot also be admitted/admitted
pairs of the same first owner and lower-prime signature. -/
theorem vfMidActiveReturnedPairCarrier_disjoint_admittedPairs
    (R p : ℕ) (sig : Finset ℕ) :
    Disjoint
      (vfMidActiveReturnedPairCarrier R p sig)
      (lowOwnerFirstOwnerAdmittedPairCarrier (R + 1) p sig) := by
  rw [Finset.disjoint_left]
  intro ab hclip hBoth
  rcases Finset.mem_product.mp hclip with ⟨haClip, _⟩
  rcases Finset.mem_product.mp hBoth with ⟨haAdmitted, _⟩
  have hhi :
      squareRootEndpoint (R + 1) < p * ab.1 :=
    (Finset.mem_filter.mp haClip).2
  have hlo :
      p * ab.1 ≤ squareRootEndpoint (R + 1) :=
    (Finset.mem_filter.mp haAdmitted).2
  omega

/-- Every admitted positive-lag pair lies outside the literal weighted VF
clipped/admitted source. The positive-lag sector-six subset cannot be paid
by treating its signed Dirichlet mass as a second copy of the VF source. -/
theorem vfMidActiveReturnedPairWeight_eq_zero_of_admittedPositive
    (R p : ℕ) (sig : Finset ℕ) (ab : ℕ × ℕ)
    (had :
      ab ∈ lowOwnerFirstOwnerAdmittedPositivePairCarrier (R + 1) p sig) :
    vfMidActiveReturnedPairWeight R p sig ab = 0 := by
  have hadPair :
      ab ∈ lowOwnerFirstOwnerAdmittedPairCarrier (R + 1) p sig :=
    (Finset.mem_filter.mp had).1
  have hnot :
      ab ∉ vfMidActiveReturnedPairCarrier R p sig := by
    intro hclip
    exact (Finset.disjoint_left.mp
      (vfMidActiveReturnedPairCarrier_disjoint_admittedPairs R p sig))
      hclip hadPair
  simp [vfMidActiveReturnedPairWeight, hnot]

/-- Stronger same-cell no-go: the original VF returned weight is identically
zero on the entire admitted-positive pair ledger, regardless of its signed
Dirichlet sector-six classification. This says NOTHING about an externally
transported historical return, which is the still-open physical bridge. -/
theorem sum_vfMidActiveReturnedPairWeight_admittedPositive_eq_zero
    (R p : ℕ) (sig : Finset ℕ) :
    (∑ ab ∈ lowOwnerFirstOwnerAdmittedPositivePairCarrier (R + 1) p sig,
      vfMidActiveReturnedPairWeight R p sig ab) = 0 := by
  apply Finset.sum_eq_zero
  intro ab hab
  exact vfMidActiveReturnedPairWeight_eq_zero_of_admittedPositive
    R p sig ab hab

end RHLean.Analysis
