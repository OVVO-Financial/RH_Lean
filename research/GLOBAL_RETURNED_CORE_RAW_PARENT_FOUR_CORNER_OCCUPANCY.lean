import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_ORBIT_PARTITION»

/-!
# Exact four-corner occupancy on one raw-parent orbit

This file stays entirely in the signed carrier layer.

For a fixed cell `(p,sig)`, owner `r`, and one of the already-defined raw
parents, the current owner fibre supplies the odd-parity corners.  The
post-`r` survivor supplies the even-parity corners whose raw parent occurs under
the owner fibre.  No energy is introduced.

The only new bookkeeping is a fixed-raw-parent filter of the existing
orbit-even survivor.  It proves that every physical orbit point is literally
one of

  (a,b), (r*a,b), (a,r*b), (r*a,r*b).

The owner fibre and orbit-even survivor then admit one common raw-parent Fubini.
This is the exact physical occupancy statement needed before completed cubes
are selected and the incidence summand is sent through the energy gate.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Orbit-even survivor pairs with one orientation-preserving raw parent fixed. -/
def lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ)
    (parent : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig S r).filter fun mn =>
    lowOwnerFirstOwnerPolarizationRawParent r mn = parent

/-- Fixed even fibres are pairwise disjoint because the raw parent is a
function. -/
theorem lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber_pairwiseDisjoint
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ) :
    Set.PairwiseDisjoint
      (↑(lowOwnerFirstOwnerPolarizationRawParentSet R p sig r))
      (lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber R p sig S r) := by
  intro parent _hp other _ho hne
  change Disjoint
    (lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber R p sig S r parent)
    (lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber R p sig S r other)
  rw [Finset.disjoint_left]
  intro mn hmp hmo
  have hpEq := (Finset.mem_filter.mp hmp).2
  have hoEq := (Finset.mem_filter.mp hmo).2
  exact hne (hpEq.symm.trans hoEq)

/-- **Exact even-orbit raw-parent partition.** -/
theorem lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber_biUnion
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ) :
    (lowOwnerFirstOwnerPolarizationRawParentSet R p sig r).biUnion
        (lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber R p sig S r) =
      lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig S r := by
  ext mn
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨parent, _hparent, hmn⟩
    exact (Finset.mem_filter.mp hmn).1
  · intro hmn
    have hparent := (Finset.mem_filter.mp hmn).2
    exact Finset.mem_biUnion.mpr
      ⟨lowOwnerFirstOwnerPolarizationRawParent r mn, hparent,
        Finset.mem_filter.mpr ⟨hmn, rfl⟩⟩

/-- Exact signed Fubini of the orbit-even survivor by the same raw-parent labels
already used by the owner fibre. -/
theorem sum_lowOwnerFirstOwnerRawParentOrbitEven_eq_rawParents
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ)
    (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig S r,
        f mn) =
      ∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
        ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber
            R p sig S r parent,
          f mn := by
  rw [← lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber_biUnion]
  exact Finset.sum_biUnion
    (lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber_pairwiseDisjoint
      R p sig S r)

/-- **Even-corner occupancy.**  A same-branch point with fixed raw parent is
literally either the zero-r corner `(a,b)` or the double-r corner `(r*a,r*b)`.
There is no third even point in one raw-parent orbit. -/
theorem lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber_child_even
    {R p r : ℕ} {sig S : Finset ℕ} {parent child : ℕ × ℕ}
    (hchild : child ∈
      lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber
        R p sig S r parent) :
    child = parent ∨
      child = (r * parent.1, r * parent.2) := by
  rcases child with ⟨m, n⟩
  rcases Finset.mem_filter.mp hchild with ⟨heven, hparent⟩
  have hcellSame := (Finset.mem_filter.mp heven).1
  have hsame := (Finset.mem_filter.mp hcellSame).1
  have hiff := (Finset.mem_filter.mp hsame).2.2
  have hparent' :
      (squarefreePrimeFamilyParent r m,
        squarefreePrimeFamilyParent r n) = parent := by
    simpa [lowOwnerFirstOwnerPolarizationRawParent] using hparent
  by_cases hrm : r ∣ m
  · have hrn : r ∣ n := hiff.mp hrm
    right
    rcases parent with ⟨a, b⟩
    simp only [Prod.mk.injEq] at hparent' ⊢
    unfold squarefreePrimeFamilyParent at hparent'
    simp only [hrm, hrn, if_true] at hparent'
    rcases hparent' with ⟨ha, hb⟩
    exact ⟨
      (Nat.mul_div_cancel' hrm).symm.trans
        (congrArg (fun z => r * z) ha),
      (Nat.mul_div_cancel' hrn).symm.trans
        (congrArg (fun z => r * z) hb)⟩
  · have hrn : ¬ r ∣ n := by
      intro h
      exact hrm (hiff.mpr h)
    left
    unfold squarefreePrimeFamilyParent at hparent'
    simp only [hrm, hrn, if_false] at hparent'
    exact hparent'

/-- The odd and even physical points over one raw parent occupy only the four
literal Boolean corners. -/
theorem lowOwnerFirstOwnerRawParentPhysicalOrbit_child_fourCorner
    {R p r : ℕ} {sig S : Finset ℕ} {parent child : ℕ × ℕ}
    (hchild :
      child ∈ lowOwnerFirstOwnerPolarizationFixedRawParentFiber
          R p sig r parent ∨
      child ∈ lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber
          R p sig S r parent) :
    child = parent ∨
      child = (r * parent.1, parent.2) ∨
      child = (parent.1, r * parent.2) ∨
      child = (r * parent.1, r * parent.2) := by
  rcases hchild with hmixed | heven
  · rcases lowOwnerFirstOwnerPolarizationFixedRawParentFiber_child_mixed
      hmixed with hleft | hright
    · exact Or.inr (Or.inl hleft)
    · exact Or.inr (Or.inr (Or.inl hright))
  · rcases lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber_child_even
      heven with hbase | hdouble
    · exact Or.inl hbase
    · exact Or.inr (Or.inr (Or.inr hdouble))

/-- **Common raw-parent orbit Fubini.**  The current owner fibre (odd corners)
and the orbit-covered part of the post-r survivor (even corners) are grouped by
exactly the same duplicate-free raw-parent labels.  This is an identity of
signed atoms for an arbitrary weight `f`. -/
theorem sum_lowOwnerFirstOwnerOwnerFiber_add_orbitEven_eq_rawParentOrbits
    (R p : ℕ) (sig S : Finset ℕ) (r : ℕ)
    (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r,
        f mn) +
      (∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitEvenCarrier R p sig S r,
        f mn) =
      ∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
        ((∑ mn ∈ lowOwnerFirstOwnerPolarizationFixedRawParentFiber
              R p sig r parent,
            f mn) +
          ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitEvenFixedFiber
              R p sig S r parent,
            f mn) := by
  rw [sum_lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber_eq_rawParents,
    sum_lowOwnerFirstOwnerRawParentOrbitEven_eq_rawParents,
    ← Finset.sum_add_distrib]

end RHLean.Proof
