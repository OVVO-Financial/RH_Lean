import Mathlib
import «research.GLOBAL_RETURNED_CORE_UNIQUE_GREATEST_OWNER_FUBINI»
import «research.GLOBAL_RETURNED_CORE_GREATEST_OWNER_CONTINUATION»

/-!
# Unique-owner continuation ledger inside one compensated cell

The greatest-owner Fubini is an ordered-pair partition.  The existing physical
continuation theorem is stated on positive-lag pairs.  This file orients the
owner fibres by `m < n` and proves the exact carrier classification needed for
the global signed induction.

At the physical endpoint `W = squareRootEndpoint R`, a positive admitted pair
is either already in a complete post-root family or lies in the post-root
remainder.  In the remainder, its unique greatest fresh owner invokes the
compiled five-way continuation theorem:

* equal-parent terminal;
* clipped owner exit;
* complete post-root family at the lower endpoint;
* existing terminal at the lower endpoint;
* lower-rank recursive remainder.

No sixth/fifth unnamed residual class is introduced and no energy estimate is
used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Positive-lag part of one unique greatest-owner fibre. -/
def lowOwnerFirstOwnerGreatestOwnerPositivePairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerPairFiber R p sig r).filter fun mn =>
    mn.1 < mn.2

/-- A positive pair in a greatest-owner fibre lies on the literal positive
physical pair carrier at the square-root endpoint. -/
theorem lowOwnerFirstOwnerGreatestOwnerPositivePair_mem_physical
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r) :
    (m, n) ∈ mertensPositivePhysicalPairCarrier (squareRootEndpoint R) := by
  rcases Finset.mem_filter.mp hmn with ⟨hownerFiber, hlt⟩
  have hoff := (Finset.mem_filter.mp hownerFiber).1
  have hpair := (Finset.mem_filter.mp hoff).1
  rcases Finset.mem_product.mp hpair with ⟨hmAd, hnAd⟩
  have hmBase := (Finset.mem_filter.mp hmAd).1
  have hnBase := (Finset.mem_filter.mp hnAd).1
  have hmCar := (Finset.mem_filter.mp hmBase).1
  have hnCar := (Finset.mem_filter.mp hnBase).1
  rcases Finset.mem_filter.mp hmCar with ⟨hmIcc, _hmMu⟩
  rcases Finset.mem_filter.mp hnCar with ⟨hnIcc, _hnMu⟩
  rcases Finset.mem_Icc.mp hmIcc with ⟨hm1, hmW⟩
  rcases Finset.mem_Icc.mp hnIcc with ⟨hn1, hnW⟩
  exact mem_mertensPositivePhysicalPairCarrier.mpr
    ⟨hm1, hmW, hn1, hnW, hlt⟩

/-- Membership in the unique-owner fibre exposes the actual greatest-owner
predicate. -/
theorem lowOwnerFirstOwnerGreatestOwnerPositivePair_owner
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r) :
    IsSquarefreePairGreatestFreshPrimeOwner r m n := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmn).1).2

/-- The unique owner of a positive admitted cell pair is a prime strictly above
the current first owner. -/
theorem lowOwnerFirstOwnerGreatestOwnerPositivePair_owner_data
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r) :
    r.Prime ∧ p < r ∧ r ≤ squareRootEndpoint R := by
  have howner := lowOwnerFirstOwnerGreatestOwnerPositivePair_owner hmn
  have hoff := (Finset.mem_filter.mp (Finset.mem_filter.mp hmn).1).1
  have hpair := (Finset.mem_filter.mp hoff).1
  rcases Finset.mem_product.mp hpair with ⟨hmAd, hnAd⟩
  have hmBase := (Finset.mem_filter.mp hmAd).1
  have hnBase := (Finset.mem_filter.mp hnAd).1
  have hmCar := (Finset.mem_filter.mp hmBase).1
  have hnCar := (Finset.mem_filter.mp hnBase).1
  have hrData := freshPrime_of_nonzeroPhysicalPair hmCar hnCar howner.1
  have hpr := lowOwnerFirstOwnerAdmittedPair_freshPrime_gt_owner
    hp hmAd hnAd howner.1
  exact ⟨hrData.1, hpr, hrData.2⟩

/-- The owner predicate gives the descending crossing packet needed by the
reversed continuation theorem. -/
theorem lowOwnerFirstOwnerGreatestOwnerPositivePair_mem_descendingCross
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r) :
    (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R r) r := by
  have hrData := lowOwnerFirstOwnerGreatestOwnerPositivePair_owner_data hp hmn
  have howner := lowOwnerFirstOwnerGreatestOwnerPositivePair_owner hmn
  have hoff := (Finset.mem_filter.mp (Finset.mem_filter.mp hmn).1).1
  have hpair := (Finset.mem_filter.mp hoff).1
  rcases Finset.mem_product.mp hpair with ⟨hmAd, hnAd⟩
  have hmCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hmAd).1).1
  have hnCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hnAd).1).1
  exact greatestFreshOwner_descendingCrossPair hrData.1 hmCar hnCar howner

/-- **Exact unique-owner continuation classification.**  A positive pair in one
unique greatest-owner fibre is either already removed by a complete post-root
family at the current endpoint, or its unique owner enters exactly one of the
five named continuation alternatives. -/
theorem lowOwnerFirstOwnerGreatestOwnerPositivePair_namedContinuation
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r) :
    let W := squareRootEndpoint R
    let parent := squarefreePairPrimeOrderedParent r m n
    (m, n) ∈ postRootPrimePhysicalPairUnion W ∨
      SquarefreePairPrimeParentsEqual r (m, n) ∨
      W < r * parent.2 ∨
      parent ∈ postRootPrimePhysicalPairUnion (W / r) ∨
      parent ∈ postRootCovarianceRemainderTerminalPairCarrier (W / r) ∨
      (parent ∈ postRootCovarianceRemainderRecursivePairCarrier (W / r) ∧
        (squarefreePairFreshPrimeSet parent.1 parent.2).card + 1 =
          (squarefreePairFreshPrimeSet m n).card ∧
        ∀ q ∈ squarefreePairFreshPrimeSet parent.1 parent.2, q < r) := by
  dsimp only
  let W := squareRootEndpoint R
  have hphys : (m, n) ∈ mertensPositivePhysicalPairCarrier W := by
    simpa [W] using lowOwnerFirstOwnerGreatestOwnerPositivePair_mem_physical hmn
  by_cases hfamily : (m, n) ∈ postRootPrimePhysicalPairUnion W
  · exact Or.inl hfamily
  · right
    have hrem : (m, n) ∈ postRootCovarianceRemainderPhysicalPairCarrier W :=
      mem_postRootCovarianceRemainderPhysicalPairCarrier.mpr ⟨hphys, hfamily⟩
    have hrData := lowOwnerFirstOwnerGreatestOwnerPositivePair_owner_data hp hmn
    have hcross :=
      lowOwnerFirstOwnerGreatestOwnerPositivePair_mem_descendingCross hp hmn
    have hcont := descendingGreatestOwner_continuation_has_no_residual_class
      hrData.1 hcross hrem
    dsimp only at hcont
    exact hcont

end RHLean.Proof
