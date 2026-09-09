import Mathlib
import RHLean.Proof.LowWheelFrozenSecondContactWindowDescent
import RHLean.Proof.ComplexVerticalFiberSpacing

/-!
# Cross-column reassembly of the saturated frozen second-contact ledger

The child-owner columns of #629 are an exact signed reindex, but numerically
norming those columns loses the full remaining power.  This file therefore
forgets the column tag before any norm is taken.

The common coordinate is the physical squarefree child integer.  On the frozen
second-contact source the child map is injective because it is injective on the
complete ordered Euler-cut carrier, and adjoining the active crossing prime
reverses the Möbius sign exactly.  Hence the complete source ledger, and thus
the complete signed sum of child-owner columns, is one ordinary Möbius sum on a
single literal finite carrier of integers.

No absolute value, owner count, packet norm, PNT input, Mertens hypothesis, or
asymptotic estimate is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The single physical integer population underlying all #629 child-owner
columns.  The column label is deliberately forgotten. -/
def lowWheelFrozenSecondContactCrossColumnChildCarrier (R : ℕ) : Finset ℕ :=
  (lowWheelCanonicalRepeatedFrozenSecondContactPart R).image
    orderedEulerCutChildInteger

@[simp] theorem mem_lowWheelFrozenSecondContactCrossColumnChildCarrier
    {R n : ℕ} :
    n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R ↔
      ∃ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
        orderedEulerCutChildInteger y = n := by
  simp [lowWheelFrozenSecondContactCrossColumnChildCarrier]

private theorem frozenSecondContact_mem_orderedEulerCutCarrier
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    y ∈ orderedEulerCutCarrier R :=
  lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier
    (Finset.mem_filter.mp hy).1

/-- **Global signed flattening.**  Before any norm, the original saturated
second-contact source ledger is exactly the negative ordinary Möbius mass of
its physical child-integer population. -/
theorem lowWheelFrozenSecondContactSource_sum_eq_neg_crossColumnChildMass
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      -∑ n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R,
        canonicalMoebiusWeight n := by
  calc
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
        ∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
          -canonicalMoebiusWeight (orderedEulerCutChildInteger y) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hcar := frozenSecondContact_mem_orderedEulerCutCarrier hy
      have hshape := orderedEulerCutShape_of_mem_carrier hcar
      have hflip := orderedEulerCutChildWeight_eq_neg hshape
      change orderedEulerCutWeight y =
        -canonicalMoebiusWeight (orderedEulerCutChildInteger y)
      rw [hflip]
      simp
    _ = -(∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
          canonicalMoebiusWeight (orderedEulerCutChildInteger y)) := by
      rw [Finset.sum_neg_distrib]
    _ = -∑ n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R,
          canonicalMoebiusWeight n := by
      congr 1
      unfold lowWheelFrozenSecondContactCrossColumnChildCarrier
      rw [Finset.sum_image]
      intro y hy z hz hchild
      exact orderedEulerCutChildInteger_injective_on_carrier
        (frozenSecondContact_mem_orderedEulerCutCarrier hy)
        (frozenSecondContact_mem_orderedEulerCutCarrier hz)
        hchild

/-- **Cross-column reassembly on one carrier.**  The sum of all #629 child-owner
columns is the ordinary Möbius mass of the common physical child population.
There is no per-column absolute value anywhere in the identity. -/
theorem lowWheelFrozenSecondContactChildOwnerColumns_eq_crossColumnChildMass
    (R : ℕ) :
    ((∑ r ∈ primesUpTo (R - 1),
        lowWheelFrozenSecondContactChildOwnerColumn R r : ℤ) : ℂ) =
      ∑ n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R,
        canonicalMoebiusWeight n := by
  have hchild :=
    lowWheelFrozenSecondContactSource_sum_eq_neg_crossColumnChildMass R
  have hcols := lowWheelFrozenSecondContactSource_sum_eq_neg_childOwnerColumns R
  have hneg :
      -((∑ r ∈ primesUpTo (R - 1),
          lowWheelFrozenSecondContactChildOwnerColumn R r : ℤ) : ℂ) =
        -(∑ n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R,
          canonicalMoebiusWeight n) := by
    exact hcols.symm.trans hchild
  have h := congrArg (fun z : ℂ => -z) hneg
  simpa using h

/-- Integer-valued form of the same exact reassembly. -/
theorem lowWheelFrozenSecondContactChildOwnerColumns_eq_crossColumnMobiusSum
    (R : ℕ) :
    (∑ r ∈ primesUpTo (R - 1),
      lowWheelFrozenSecondContactChildOwnerColumn R r) =
      ∑ n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R, μ n := by
  have h := lowWheelFrozenSecondContactChildOwnerColumns_eq_crossColumnChildMass R
  have hcast :
      (((∑ r ∈ primesUpTo (R - 1),
          lowWheelFrozenSecondContactChildOwnerColumn R r) : ℤ) : ℂ) =
        (((∑ n ∈ lowWheelFrozenSecondContactCrossColumnChildCarrier R,
          μ n) : ℤ) : ℂ) := by
    simpa [canonicalMoebiusWeight] using h
  exact_mod_cast hcast

end RHLean.Proof
