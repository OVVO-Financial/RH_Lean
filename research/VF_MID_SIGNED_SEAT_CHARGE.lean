import Mathlib
import «research.VF_MID_FRACTIONAL_PRIME_CLUSTER»
import «research.VF_MID_ODD_FRACTIONAL_CLUSTER»

/-!
# Signed VF charge on the parity owner tree

This file puts the VF reference and the actual 0/1 prime configuration on the
same physical odd carrier.

For the R-th square block, write

  w_R = V_R / R,

where V_R is the complete VF midpoint mass and R is the exact number of odd
candidate seats after the fixed owner 2 has acted.  Give each odd candidate
seat the signed charge

  w_R - 1_Prime(n).

Thus a composite seat carries +w_R, while a prime seat carries -(1-w_R).
Summed across the odd carrier this is exactly V_R-P_R, the canonical VF
tracking defect.

FTA then allocates every positive composite charge uniquely to its least-prime
owner.  The negative charge stays on the actual prime seats.  The result is an
exact signed terminal/recursive owner-tree decomposition with no Li object and
no arbitrary allocation of the VF reference.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Signed VF-minus-actual charge on one parity-surviving integer seat. -/
def vfMidOddSignedSeatCharge (R n : ℕ) : ℝ :=
  vfMidOddFractionalPrimeSeatWeight R - vfMidActualPrimeSeatMass n

/-- A prime candidate seat carries the negative complementary VF charge. -/
theorem vfMidOddSignedSeatCharge_of_prime
    (R n : ℕ) (hn : n.Prime) :
    vfMidOddSignedSeatCharge R n =
      -(1 - vfMidOddFractionalPrimeSeatWeight R) := by
  simp [vfMidOddSignedSeatCharge, vfMidActualPrimeSeatMass, hn]

/-- A composite/nonprime candidate seat carries the positive VF charge. -/
theorem vfMidOddSignedSeatCharge_of_not_prime
    (R n : ℕ) (hn : ¬ n.Prime) :
    vfMidOddSignedSeatCharge R n =
      vfMidOddFractionalPrimeSeatWeight R := by
  simp [vfMidOddSignedSeatCharge, vfMidActualPrimeSeatMass, hn]

/-- Filtering the parity carrier to actual primes gives exactly the physical
prime set of the square block. -/
theorem vfMidOddCandidateSeats_filter_prime
    (R : ℕ) (hR : 2 ≤ R) :
    (vfMidOddCandidateSeats R).filter Nat.Prime =
      vfMidSquareWheelPrimes R := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hnOdd, hnPrime⟩
    change n ∈ vfMidSquarePrefixWheelSurvivors 2 R at hnOdd
    rcases Finset.mem_filter.mp hnOdd with ⟨hnSite, _hnSurv⟩
    exact Finset.mem_filter.mpr ⟨hnSite, hnPrime⟩
  · intro hn
    have hnPrime : n.Prime := (Finset.mem_filter.mp hn).2
    have hnOdd :=
      vfMidSquareWheelPrimes_subset_prefixWheelSurvivors
        hR (by omega : 2 ≤ R) hn
    apply Finset.mem_filter.mpr
    constructor
    · exact hnOdd
    · exact hnPrime

/-- The 0/1 prime mass on the odd carrier is exactly the square-block prime
supply. -/
theorem vfMidActualPrimeSeatMass_sum_oddCandidates
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ n ∈ vfMidOddCandidateSeats R, vfMidActualPrimeSeatMass n) =
      (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  unfold vfMidActualPrimeSeatMass
  rw [← Finset.sum_filter]
  rw [vfMidOddCandidateSeats_filter_prime R hR]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard :
      (vfMidSquareWheelPrimes R).card =
        vfMidIntegerBlockPrimeSupply R := by
    unfold vfMidIntegerBlockPrimeSupply
    rw [vfMidDirectPrimeBand_eq_squareWheelPrimes]
  exact_mod_cast hcard

/-- **Exact signed-seat identity.**
The sum of the VF-minus-actual charges on the parity carrier is precisely the
canonical composite tracking defect V_R-P_R. -/
theorem vfMidOddSignedSeatCharge_sum
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ n ∈ vfMidOddCandidateSeats R, vfMidOddSignedSeatCharge R n) =
      vfMidOddCompositeTrackingDefect R := by
  unfold vfMidOddSignedSeatCharge
  rw [Finset.sum_sub_distrib,
    vfMidOddFractionalPrimeSeatWeight_sum R hR,
    vfMidActualPrimeSeatMass_sum_oddCandidates R hR]
  rw [vfMidOddCompositeTrackingDefect_eq_neg_bandError R hR]
  unfold vfMidSquareBandError
  rw [vfMidSquareBandPrimes_card_eq_integerBlockPrimeSupply R]
  ring

/-- The uniform seat weight times the exact parity population recovers the
whole VF midpoint mass. -/
theorem vfMidOddFractionalPrimeSeatWeight_mul_population
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddFractionalPrimeSeatWeight R * (R : ℝ) =
      vfMidBandMass R := by
  unfold vfMidOddFractionalPrimeSeatWeight
  have hR0 : (R : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Prime/composite charge split.**
The block defect is the positive VF charge carried by parity-surviving
composites minus the complementary negative charge carried by actual primes. -/
theorem vfMidOddCompositeTrackingDefect_eq_compositeCharge_sub_primeCharge
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddCompositeTrackingDefect R =
      vfMidOddFractionalPrimeSeatWeight R *
          ((vfMidSquareBandPrefixCompositeSurvivors 2 R).card : ℝ) -
        (1 - vfMidOddFractionalPrimeSeatWeight R) *
          (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  have hpart :=
    vfMidOddActualComposite_card_add_primeSupply R hR
  have hpartR :
      ((vfMidSquareBandPrefixCompositeSurvivors 2 R).card : ℝ) +
          (vfMidIntegerBlockPrimeSupply R : ℝ) =
        (R : ℝ) := by
    exact_mod_cast hpart
  have hmass :=
    vfMidOddFractionalPrimeSeatWeight_mul_population R hR
  unfold vfMidOddCompositeTrackingDefect
    vfMidOddFractionalCompositeReference
  rw [← hmass]
  rw [← hpartR]
  ring

/-- **FTA signed owner decomposition.**
Every positive composite charge is allocated by its unique least-prime owner;
the negative prime charge remains ungrouped. -/
theorem vfMidOddCompositeTrackingDefect_eq_ownerCharges_sub_primeCharge
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddCompositeTrackingDefect R =
      (∑ p ∈ vfMidSquareBandLateOwnerPrimes 2 R,
        vfMidOddFractionalPrimeSeatWeight R *
          ((vfMidSquareBandCompositeOwner R p).card : ℝ)) -
      (1 - vfMidOddFractionalPrimeSeatWeight R) *
        (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  rw [vfMidOddCompositeTrackingDefect_eq_compositeCharge_sub_primeCharge R hR]
  have howners :=
    vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards 2 R hR
  have hownersR :
      ((vfMidSquareBandPrefixCompositeSurvivors 2 R).card : ℝ) =
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes 2 R,
          ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
    exact_mod_cast howners
  rw [hownersR, Finset.mul_sum]

/-- **Terminal/recursive signed charge split.**
This is the same VF tracking defect on the exact owner partition already
constructed in #848. -/
theorem vfMidOddCompositeTrackingDefect_eq_terminal_recursive_charges
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddCompositeTrackingDefect R =
      (∑ p ∈ vfMidSquareBandLateTerminalOwners R,
        vfMidOddFractionalPrimeSeatWeight R *
          ((vfMidSquareBandCompositeOwner R p).card : ℝ)) +
      (∑ p ∈ vfMidSquareBandLateRecursiveOwners R,
        vfMidOddFractionalPrimeSeatWeight R *
          ((vfMidSquareBandCompositeOwner R p).card : ℝ)) -
      (1 - vfMidOddFractionalPrimeSeatWeight R) *
        (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  rw [vfMidOddCompositeTrackingDefect_eq_ownerCharges_sub_primeCharge R hR,
    vfMidSquareBandLateOwnerPrimes_eq_terminal_union_recursive,
    Finset.sum_union
      (vfMidSquareBandLateTerminal_recursive_disjoint R)]

/-- Weighted terminal-owner charge is unchanged when the owner is stripped:
the child map preserves cardinality exactly. -/
theorem vfMidOdd_terminalOwnerCharges_eq_childCharges
    (R : ℕ) :
    (∑ p ∈ vfMidSquareBandLateTerminalOwners R,
      vfMidOddFractionalPrimeSeatWeight R *
        ((vfMidSquareBandCompositeOwner R p).card : ℝ)) =
      ∑ p ∈ vfMidSquareBandLateTerminalOwners R,
        vfMidOddFractionalPrimeSeatWeight R *
          ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ) := by
  apply Finset.sum_congr rfl
  intro p _hp
  rw [vfMidSquareBandCompositeOwnerChildren_card]

/-- Weighted recursive-owner charge can be written on the exact rough-child
carrier. -/
theorem vfMidOdd_recursiveOwnerCharges_eq_roughChildCharges
    (R : ℕ) (hR : 3 ≤ R) :
    (∑ p ∈ vfMidSquareBandLateRecursiveOwners R,
      vfMidOddFractionalPrimeSeatWeight R *
        ((vfMidSquareBandCompositeOwner R p).card : ℝ)) =
      ∑ p ∈ vfMidSquareBandLateRecursiveOwners R,
        vfMidOddFractionalPrimeSeatWeight R *
          ((vfMidSquareBandOwnerRoughChildren R p).card : ℝ) := by
  apply Finset.sum_congr rfl
  intro p hp
  have hpLate : p ∈ vfMidSquareBandLateOwnerPrimes 2 R :=
    (Finset.mem_filter.mp hp).1
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (Finset.mem_filter.mp hpLate).1
  rw [← vfMidSquareBandCompositeOwnerChildren_card R p,
    vfMidSquareBandCompositeOwnerChildren_eq_rough hR hpOwner]

/-- **Exact signed VF child tree.**
The direct block discrepancy is now a sum on the same child carriers used by
the chronological descent: terminal prime children, recursive rough children,
and the negative actual-prime charge.  No absolute value has been taken. -/
theorem vfMidOddCompositeTrackingDefect_eq_signed_child_tree
    (R : ℕ) (hR : 3 ≤ R) :
    vfMidOddCompositeTrackingDefect R =
      (∑ p ∈ vfMidSquareBandLateTerminalOwners R,
        vfMidOddFractionalPrimeSeatWeight R *
          ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ)) +
      (∑ p ∈ vfMidSquareBandLateRecursiveOwners R,
        vfMidOddFractionalPrimeSeatWeight R *
          ((vfMidSquareBandOwnerRoughChildren R p).card : ℝ)) -
      (1 - vfMidOddFractionalPrimeSeatWeight R) *
        (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  rw [vfMidOddCompositeTrackingDefect_eq_terminal_recursive_charges R
      (by omega),
    vfMidOdd_terminalOwnerCharges_eq_childCharges R,
    vfMidOdd_recursiveOwnerCharges_eq_roughChildCharges R hR]

end RHLean.Analysis
