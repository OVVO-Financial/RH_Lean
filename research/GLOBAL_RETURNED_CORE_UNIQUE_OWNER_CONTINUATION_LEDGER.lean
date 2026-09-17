import Mathlib
import «research.GLOBAL_RETURNED_CORE_UNIQUE_GREATEST_OWNER_FUBINI»
import «research.GLOBAL_RETURNED_CORE_GREATEST_OWNER_CONTINUATION»
import «research.GLOBAL_RETURNED_CORE_GREATEST_OWNER_CONGESTION»

/-!
# Unique-owner continuation ledger inside one compensated cell

The greatest-owner Fubini is an ordered-pair partition.  The existing physical
continuation theorem is stated on positive-lag pairs.  This file orients the
owner fibres by `m < n` and proves the exact carrier classification needed for
the global signed induction.

At the physical endpoint `W = squareRootEndpoint R`, a positive admitted pair
is either already in a complete post-root family or lies in the post-root
remainder.  In the remainder, its unique greatest fresh owner invokes the
compiled five-way continuation theorem.

The same pair is also shown to lie in the literal greatest-owner fixed-parent
child fibre for its stripped ordered parent.  Thus the unique-owner assembly
and the local reciprocal contraction use exactly the same graph.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Positive-lag admitted pairs in one compensated cell. -/
def lowOwnerFirstOwnerAdmittedPositivePairCarrier
    (R p : ℕ) (sig : Finset ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerAdmittedPairCarrier R p sig).filter fun mn =>
    mn.1 < mn.2

/-- Positive-lag part of one unique greatest-owner fibre. -/
def lowOwnerFirstOwnerGreatestOwnerPositivePairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerPairFiber R p sig r).filter fun mn =>
    mn.1 < mn.2

/-- Positive greatest-owner fibres are pairwise disjoint. -/
theorem lowOwnerFirstOwnerGreatestOwnerPositivePairFiber_pairwiseDisjoint
    (R p : ℕ) (sig : Finset ℕ) :
    Set.PairwiseDisjoint (↑(lowOwnerRevealedPrimesAbove R p))
      (lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig) := by
  intro r _hr s _hs hrs
  change Disjoint
    (lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r)
    (lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig s)
  rw [Finset.disjoint_left]
  intro mn hmr hms
  have hro := (Finset.mem_filter.mp (Finset.mem_filter.mp hmr).1).2
  have hso := (Finset.mem_filter.mp (Finset.mem_filter.mp hms).1).2
  exact hrs (squarefreePairGreatestFreshPrimeOwner_unique hro hso)

/-- **Positive-lag unique-owner partition.**  Every positive admitted pair is
charged to exactly one greatest remaining fresh owner. -/
theorem lowOwnerFirstOwnerGreatestOwnerPositivePairFiber_biUnion
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (lowOwnerRevealedPrimesAbove R p).biUnion
        (lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig) =
      lowOwnerFirstOwnerAdmittedPositivePairCarrier R p sig := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨r, _hr, hmn⟩
    rcases Finset.mem_filter.mp hmn with ⟨howner, hlt⟩
    have hpair := (Finset.mem_filter.mp (Finset.mem_filter.mp howner).1).1
    exact Finset.mem_filter.mpr ⟨hpair, hlt⟩
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hpair, hlt⟩
    have hoff : (m, n) ∈
        lowOwnerFirstOwnerAdmittedOffDiagonalPairCarrier R p sig :=
      Finset.mem_filter.mpr ⟨hpair, ne_of_lt hlt⟩
    rcases lowOwnerFirstOwnerAdmittedOffDiagonalPair_has_greatestOwner
      hp hoff with ⟨r, hr, howner⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hr, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hoff, howner⟩, hlt⟩

/-- **Positive-lag unique-owner signed Fubini.** -/
theorem sum_lowOwnerFirstOwnerAdmittedPositive_eq_sum_greatestOwnerFibers
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime)
    (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerFirstOwnerAdmittedPositivePairCarrier R p sig,
        f mn) =
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        ∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r,
          f mn := by
  rw [← lowOwnerFirstOwnerGreatestOwnerPositivePairFiber_biUnion hp]
  exact Finset.sum_biUnion
    (lowOwnerFirstOwnerGreatestOwnerPositivePairFiber_pairwiseDisjoint R p sig)

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

/-- The unique owner is prime, strictly above the current first owner, and on
the physical clock. -/
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

/-- **Graph compatibility.** -/
theorem lowOwnerFirstOwnerGreatestOwnerPositivePair_mem_fixedParentChildFiber
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r) :
    (m, n) ∈ lowOwnerGreatestOwnerFixedParentChildFiber R
      (squarefreePairPrimeOrderedParent r m n) r := by
  have hcross :=
    lowOwnerFirstOwnerGreatestOwnerPositivePair_mem_descendingCross hp hmn
  have hlt := (Finset.mem_filter.mp hmn).2
  unfold lowOwnerGreatestOwnerFixedParentChildFiber
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨hcross, hlt⟩, rfl⟩

/-- **Exact unique-owner continuation classification.** -/
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
