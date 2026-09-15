import Mathlib
import «research.GLOBAL_RETURNED_CORE_ZERO_TARGET_COVARIANCE»

/-!
# No residual carrier class in the critical continuation

The critical owner square leaves only a quadratic continuation and a clipped
exit after the favorable first crossing.  This file identifies where every
non-clipped continuation can go.

For an actual nonzero recursive covariance child, strip its least separating
prime `p`.  If the companion corner is clipped, we are already on the named
clipped exit.  Otherwise both stripped-parent coordinates lie below `W / p`.
At that lower endpoint the parent is forced into exactly one of:

* a complete post-root prime family;
* the nonpositive equal-parent terminal class;
* the recursive remainder class, whose separation rank is exactly one lower.

There is no fourth carrier.  This is a finite structural statement only; no
norm or magnitude estimate is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Every positive-lag physical pair at an endpoint belongs either to the
post-root family union or to its literal complement.  This small lemma is kept
named because it is the endpoint partition used after each continuation step. -/
theorem lowerEndpointPhysicalPair_remainder_or_postRootFamily
    {Y a b : ℕ}
    (ha1 : 1 ≤ a) (haY : a ≤ Y)
    (hb1 : 1 ≤ b) (hbY : b ≤ Y) (hab : a < b) :
    (a, b) ∈ postRootCovarianceRemainderPhysicalPairCarrier Y ∨
      (a, b) ∈ postRootPrimePhysicalPairUnion Y := by
  have hphysical : (a, b) ∈ mertensPositivePhysicalPairCarrier Y :=
    mem_mertensPositivePhysicalPairCarrier.mpr
      ⟨ha1, haY, hb1, hbY, hab⟩
  by_cases hfamily : (a, b) ∈ postRootPrimePhysicalPairUnion Y
  · exact Or.inr hfamily
  · exact Or.inl
      (mem_postRootCovarianceRemainderPhysicalPairCarrier.mpr
        ⟨hphysical, hfamily⟩)

/-- **No residual class after one critical continuation step.**

For every nonzero recursive pair at endpoint `W`, let `p` be its least
separating owner and let `parent` be the canonically ordered stripped pair.
Exactly one of the following stopping/continuation alternatives is available:

1. the companion `p * parent.2` is clipped;
2. the parent enters a complete post-root family at the lower endpoint `W/p`;
3. the parent is terminal there;
4. the parent remains recursive there, and its separation rank has dropped by
   exactly one.

The disjunction is intentionally carrier-level: it proves that no unnamed
cross-owner population can appear between owner steps. -/
theorem postRootCovarianceRecursivePair_continuation_has_no_residual_class
    {W m n : ℕ}
    (hpair : (m, n) ∈ postRootCovarianceRemainderRecursivePairCarrier W)
    (hweight : realMoebiusStep m * realMoebiusStep n ≠ 0) :
    let p := squarefreePairFreshPrimeOwner m n
    let parent := squarefreePairFreshPrimeOrderedParent m n
    W < p * parent.2 ∨
      parent ∈ postRootPrimePhysicalPairUnion (W / p) ∨
      parent ∈ postRootCovarianceRemainderTerminalPairCarrier (W / p) ∨
      (parent ∈ postRootCovarianceRemainderRecursivePairCarrier (W / p) ∧
        (squarefreePairFreshPrimeSet parent.1 parent.2).card + 1 =
          (squarefreePairFreshPrimeSet m n).card) := by
  rcases Finset.mem_filter.mp hpair with ⟨hremainder, _hparentNe⟩
  have hphysical :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hremainder).1
  rcases mem_mertensPositivePhysicalPairCarrier.mp hphysical with
    ⟨hm1, _hmW, hn1, _hnW, hmnlt⟩
  have hmstep : realMoebiusStep m ≠ 0 := by
    intro hmzero
    exact hweight (by rw [hmzero, zero_mul])
  have hnstep : realMoebiusStep n ≠ 0 := by
    intro hnzero
    exact hweight (by rw [hnzero, mul_zero])
  have hmsq : Squarefree m := squarefree_of_realMoebiusStep_ne_zero hmstep
  have hnsq : Squarefree n := squarefree_of_realMoebiusStep_ne_zero hnstep
  have hp : (squarefreePairFreshPrimeOwner m n).Prime :=
    squarefreePairFreshPrimeOwner_prime hmsq hnsq (ne_of_lt hmnlt)
  have hdesc :=
    postRootCovarianceRemainderRecursivePair_owner_descent hpair hweight
  dsimp only at hdesc ⊢
  let parent := squarefreePairFreshPrimeOrderedParent m n
  have hparentMem : parent ∈ postRootCovarianceRemainderPhysicalPairCarrier W := by
    simpa [parent] using hdesc.1
  have hparentPhysical :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hparentMem).1
  rcases mem_mertensPositivePhysicalPairCarrier.mp hparentPhysical with
    ⟨ha1, _haW, hb1, _hbW, hab⟩
  by_cases hclip : W < squarefreePairFreshPrimeOwner m n * parent.2
  · exact Or.inl hclip
  · have hcomplete :
        squarefreePairFreshPrimeOwner m n * parent.2 ≤ W :=
      Nat.le_of_not_gt hclip
    have hlower :=
      zeroTargetCriticalCompleteParent_le_lowerEndpoint
        hp.pos (Nat.le_of_lt hab) hcomplete
    have hpartition :=
      lowerEndpointPhysicalPair_remainder_or_postRootFamily
        ha1 hlower.1 hb1 hlower.2 hab
    rcases hpartition with hrem | hfamily
    · by_cases hterminal : SquarefreePairFreshPrimeParentsEqual parent
      · exact Or.inr (Or.inr (Or.inl
          (Finset.mem_filter.mpr ⟨hrem, hterminal⟩)))
      · have hrecursive :
            parent ∈ postRootCovarianceRemainderRecursivePairCarrier
              (W / squarefreePairFreshPrimeOwner m n) :=
          Finset.mem_filter.mpr ⟨hrem, hterminal⟩
        have hrank :
            (squarefreePairFreshPrimeSet parent.1 parent.2).card + 1 =
              (squarefreePairFreshPrimeSet m n).card := by
          simpa [parent] using hdesc.2.2.1
        exact Or.inr (Or.inr (Or.inr ⟨hrecursive, hrank⟩))
    · exact Or.inr (Or.inl hfamily)

end RHLean.Proof
