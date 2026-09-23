import Mathlib
import «research.GLOBAL_RETURNED_CORE_GLOBAL_DESCENDING_SITE_FUBINI»
import RHLean.Analysis.PrimeWheelRunOthelloBoundary

/-!
# Global least-owner Fubini for an arbitrary signed site

The raw-parent chronology fixes the *least* fresh prime first owner and only
then descends through larger owners.  The greatest-owner Fubini is therefore
not, by itself, the correct outer coordinate for the raw-parent proof.

This file gives the matching global partition.  On the common nonzero-Mobius
clock, every off-diagonal ordered pair has exactly one least fresh-prime owner.
For any signed site v, its entire off-diagonal pair mass is therefore the
disjoint sum of the first-owner fibres.  Together with the nonnegative diagonal,

  sum_p FirstOwnerMass_v(p) <= E_v(empty).

No estimate beyond diagonal nonnegativity is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Global ordered off-diagonal fibre with least fresh-prime owner p. -/
def lowOwnerGlobalFirstOwnerPairFiber
    (R p : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerGlobalOffDiagonalPairCarrier R).filter fun mn =>
    IsSquarefreePairFreshPrimeOwner p mn.1 mn.2

/-- Two least fresh-prime owners of one pair are equal. -/
theorem squarefreePairFreshPrimeOwner_unique_public
    {p q m n : ℕ}
    (hp : IsSquarefreePairFreshPrimeOwner p m n)
    (hq : IsSquarefreePairFreshPrimeOwner q m n) :
    p = q := by
  have hpq : p ≤ q := hp.2 q hq.1
  have hqp : q ≤ p := hq.2 p hp.1
  omega

/-- Every physical off-diagonal pair has a unique least owner on the physical
prime clock. -/
theorem lowOwnerGlobalOffDiagonalPair_has_firstOwner
    {R m n : ℕ}
    (hmn : (m, n) ∈ lowOwnerGlobalOffDiagonalPairCarrier R) :
    ∃ p ∈ primesUpTo (squareRootEndpoint R),
      IsSquarefreePairFreshPrimeOwner p m n := by
  rcases Finset.mem_filter.mp hmn with ⟨hpair, hne⟩
  rcases Finset.mem_product.mp hpair with ⟨hmCar, hnCar⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with
    ⟨hmSq, _hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with
    ⟨hnSq, _hnPos⟩
  rcases existsUnique_squarefreePairFreshPrimeOwner hmSq hnSq hne with
    ⟨p, hpOwner, _hpUnique⟩
  have hpData :=
    freshPrime_of_nonzeroPhysicalPair hmCar hnCar hpOwner.1
  exact ⟨p, mem_primesUpTo.mpr hpData, hpOwner⟩

/-- First-owner fibres are pairwise disjoint. -/
theorem lowOwnerGlobalFirstOwnerPairFiber_pairwiseDisjoint
    (R : ℕ) :
    Set.PairwiseDisjoint (↑(primesUpTo (squareRootEndpoint R)))
      (lowOwnerGlobalFirstOwnerPairFiber R) := by
  intro p _hp q _hq hpq
  change Disjoint
    (lowOwnerGlobalFirstOwnerPairFiber R p)
    (lowOwnerGlobalFirstOwnerPairFiber R q)
  rw [Finset.disjoint_left]
  intro mn hmp hmq
  have hpOwner := (Finset.mem_filter.mp hmp).2
  have hqOwner := (Finset.mem_filter.mp hmq).2
  exact hpq (squarefreePairFreshPrimeOwner_unique_public hpOwner hqOwner)

/-- The first-owner fibres cover exactly the full off-diagonal common-clock
carrier. -/
theorem lowOwnerGlobalFirstOwnerPairFiber_biUnion
    (R : ℕ) :
    (primesUpTo (squareRootEndpoint R)).biUnion
        (lowOwnerGlobalFirstOwnerPairFiber R) =
      lowOwnerGlobalOffDiagonalPairCarrier R := by
  ext mn
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨p, _hp, hmn⟩
    exact (Finset.mem_filter.mp hmn).1
  · intro hmn
    rcases mn with ⟨m, n⟩
    rcases lowOwnerGlobalOffDiagonalPair_has_firstOwner hmn with
      ⟨p, hp, hpOwner⟩
    exact Finset.mem_biUnion.mpr
      ⟨p, hp, Finset.mem_filter.mpr ⟨hmn, hpOwner⟩⟩

/-- Signed pair mass on one global least-owner fibre. -/
def lowOwnerGlobalFirstOwnerPairMassWith
    (R p : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ mn ∈ lowOwnerGlobalFirstOwnerPairFiber R p,
    v mn.1 * v mn.2

/-- **Global first-owner signed Fubini for any site.** -/
theorem sum_lowOwnerGlobalOffDiagonal_eq_firstOwnerFibers
    (R : ℕ) (v : ℕ → ℝ) :
    (∑ mn ∈ lowOwnerGlobalOffDiagonalPairCarrier R,
      v mn.1 * v mn.2) =
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerGlobalFirstOwnerPairMassWith R p v := by
  rw [← lowOwnerGlobalFirstOwnerPairFiber_biUnion R]
  rw [Finset.sum_biUnion
    (lowOwnerGlobalFirstOwnerPairFiber_pairwiseDisjoint R)]
  rfl

/-- **Exact empty-energy decomposition in first-owner currency.** -/
theorem lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_firstOwners
    (R : ℕ) (v : ℕ → ℝ) :
    lowOwnerRevealedPairMassWith R ∅ v =
      lowOwnerGlobalDiagonalPairMassWith R v +
        ∑ p ∈ primesUpTo (squareRootEndpoint R),
          lowOwnerGlobalFirstOwnerPairMassWith R p v := by
  rw [lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_offDiagonal,
    sum_lowOwnerGlobalOffDiagonal_eq_firstOwnerFibers]

/-- The complete ordered first-owner mass costs at most the one assembled
empty-state energy. -/
theorem sum_lowOwnerGlobalFirstOwnerPairMassWith_le_emptyEnergy
    (R : ℕ) (v : ℕ → ℝ) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerGlobalFirstOwnerPairMassWith R p v) ≤
      lowOwnerRevealedPairMassWith R ∅ v := by
  have h :=
    lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_firstOwners R v
  have hd := lowOwnerGlobalDiagonalPairMassWith_nonneg R v
  linarith

end RHLean.Proof
