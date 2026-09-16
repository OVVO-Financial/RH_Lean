import Mathlib
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_RANK_DESCENT»
import «research.GLOBAL_RETURNED_CORE_COMPLETED_POLARIZATION_AGGREGATE»

/-!
# Exact unique-greatest-owner Fubini on one compensated cell

Before any recursive estimate, the admitted Cartesian square is partitioned
exactly into

  diagonal pairs
    union
  the disjoint owner-labelled fibres indexed by the unique greatest remaining
  fresh prime.

The theorem is stated for an arbitrary signed atom `f`.  Consequently it can be
instantiated by the compensated AMP four-corner mass without changing signs or
introducing absolute values.

This is the finite Fubini needed by the rank induction.  In particular, it
prevents both owner duplication and sibling-parent duplication from being hidden
inside a later inequality.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Diagonal admitted pairs have no fresh owner. -/
def lowOwnerFirstOwnerAdmittedDiagonalPairCarrier
    (R p : ℕ) (sig : Finset ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerAdmittedPairCarrier R p sig).filter fun mn =>
    mn.1 = mn.2

/-- Off-diagonal admitted pairs are exactly the pairs which require a fresh
owner in the finite descent. -/
def lowOwnerFirstOwnerAdmittedOffDiagonalPairCarrier
    (R p : ℕ) (sig : Finset ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerAdmittedPairCarrier R p sig).filter fun mn =>
    mn.1 ≠ mn.2

/-- Literal union of all unique-greatest-owner pair fibres. -/
def lowOwnerFirstOwnerAdmittedGreatestOwnerPairUnion
    (R p : ℕ) (sig : Finset ℕ) : Finset (ℕ × ℕ) :=
  (primesUpTo (squareRootEndpoint R)).biUnion fun r =>
    lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r

/-- Owner fibres are pairwise disjoint on the physical owner set. -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber_pairwiseDisjoint
    (R p : ℕ) (sig : Finset ℕ) :
    Set.PairwiseDisjoint (↑(primesUpTo (squareRootEndpoint R)))
      (lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig) := by
  intro r _hr s _hs hrs
  exact lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber_disjoint hrs

/-- The owner union is exactly the off-diagonal admitted pair carrier. -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwnerPairUnion_eq_offDiagonal
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerAdmittedGreatestOwnerPairUnion R p sig =
      lowOwnerFirstOwnerAdmittedOffDiagonalPairCarrier R p sig := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro hmn
    rcases Finset.mem_biUnion.mp hmn with ⟨r, hr, hrfiber⟩
    rcases mem_lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber.mp hrfiber with
      ⟨hpair, howner⟩
    apply Finset.mem_filter.mpr
    refine ⟨hpair, ?_⟩
    intro heq
    have hmnEq : m = n := by simpa using heq
    subst n
    have hfresh := howner.1
    simp [squarefreePairFreshPrimeSet] at hfresh
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hpair, hmne⟩
    rcases lowOwnerFirstOwnerAdmittedPair_exists_greatestOwner hp hpair hmne with
      ⟨r, hr, _hpr, hrfiber⟩
    exact Finset.mem_biUnion.mpr ⟨r, hr, hrfiber⟩

/-- Signed sum over the owner union is the iterated sum over owner-labelled
fibres, with every off-diagonal pair appearing exactly once. -/
theorem sum_lowOwnerFirstOwnerAdmittedGreatestOwnerPairUnion
    (R p : ℕ) (sig : Finset ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerFirstOwnerAdmittedGreatestOwnerPairUnion R p sig, f mn) =
      ∑ r ∈ primesUpTo (squareRootEndpoint R),
        ∑ mn ∈ lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r,
          f mn := by
  unfold lowOwnerFirstOwnerAdmittedGreatestOwnerPairUnion
  exact Finset.sum_biUnion
    (lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber_pairwiseDisjoint R p sig)

/-- **Exact unique-owner pair Fubini.**  The full admitted pair sum is diagonal
plus a disjoint sum over the unique greatest remaining owner.  No norm or
magnitude estimate is used. -/
theorem lowOwnerFirstOwnerAdmittedPair_sum_eq_diagonal_add_greatestOwners
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime)
    (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerFirstOwnerAdmittedPairCarrier R p sig, f mn) =
      (∑ mn ∈ lowOwnerFirstOwnerAdmittedDiagonalPairCarrier R p sig, f mn) +
      ∑ r ∈ primesUpTo (squareRootEndpoint R),
        ∑ mn ∈ lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r,
          f mn := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := lowOwnerFirstOwnerAdmittedPairCarrier R p sig)
    (p := fun mn : ℕ × ℕ => mn.1 = mn.2)
    (f := f)
  have hoff :
      (lowOwnerFirstOwnerAdmittedPairCarrier R p sig).filter
          (fun mn : ℕ × ℕ => ¬ mn.1 = mn.2) =
        lowOwnerFirstOwnerAdmittedOffDiagonalPairCarrier R p sig := by
    rfl
  have hunion := lowOwnerFirstOwnerAdmittedGreatestOwnerPairUnion_eq_offDiagonal
    (R := R) (p := p) (sig := sig) hp
  have hsumUnion := sum_lowOwnerFirstOwnerAdmittedGreatestOwnerPairUnion
    R p sig f
  unfold lowOwnerFirstOwnerAdmittedDiagonalPairCarrier at *
  rw [hoff] at hsplit
  rw [← hunion] at hsplit
  rw [hsumUnion] at hsplit
  exact hsplit.symm

end RHLean.Proof
