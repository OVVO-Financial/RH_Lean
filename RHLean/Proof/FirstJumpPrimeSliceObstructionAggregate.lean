import Mathlib
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Proof.FirstJumpPrimeSliceObstructionCore

/-!
# Exact upper-half first-jump prime-slice aggregate

This module completes the obstruction isolated in
`FirstJumpPrimeSliceObstructionCore`.

For `R / 2 < p <= R`, the fixed first-jump-prime slice has no hidden local
cancellation.  Nontrivial high cofactors vanish, while every actual unit-
cofactor owner contributes exactly `-1`.  Hence the whole `p`-slice is the
negative cardinality of the later-prime owner interval

`p < k <= (R^2 - 1) / p`.

This is the opposite of an `R / p` seat bound: in the upper half `R / p = 1`,
but the owner interval can contain linearly many primes on the PNT scale.
No norm is taken until after the exact signed aggregate has been identified.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

attribute [local instance] Classical.propDecidable

/-- A unit-cofactor high-owner state outside the canonical later-prime owner
interval cannot contain the fixed first-jump prime `p`: either `p` is not in the
owner prefix or the physical upper endpoint is already below `p`. -/
theorem upperHalfFirstJumpPrimeStateSlice_eq_zero_unit_of_not_owner
    {R p k : ℕ}
    (hx : (1, k) ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R)
    (hkNot : k ∉ upperHalfFirstJumpOwnerSet R p) :
    signedFirstJumpPrimeStateSlice R p (1, k) = 0 := by
  classical
  unfold signedFirstJumpPrimeStateSlice
  split_ifs with hstate hpMem
  · have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
    have hne := hxData.2
    have hkPivot : k = lowWheelCanonicalDowncrossPivot (1, k) :=
      lowWheelCanonicalDowncrossOrientedChargingFaces_quotient_eq_pivot hne
    have hkRoot : Nat.sqrt R < k := by
      simpa only [← hkPivot] using hstate.2
    have hshape := highOwner_orientedState_shape hx hkRoot
    have hpData := mem_primesUpTo.mp hpMem
    have hpLtK : p < k := by
      have hpLe : p ≤ k - 1 := by
        simpa only [← hkPivot] using hpData.2
      omega
    have hkNotLe : ¬ k ≤ squareRootEndpoint R / p := by
      intro hkLe
      apply hkNot
      exact mem_upperHalfFirstJumpOwnerSet.mpr ⟨hshape.1, hpLtK, hkLe⟩
    have hXpLtK : squareRootEndpoint R / p < k :=
      Nat.lt_of_not_ge hkNotLe
    have hXlt : squareRootEndpoint R < k * p :=
      (Nat.div_lt_iff_lt_mul hpData.1.pos).1 hXpLtK
    have hdiv : squareRootEndpoint R / k < p := by
      apply (Nat.div_lt_iff_lt_mul hshape.1.pos).2
      simpa [Nat.mul_comm] using hXlt
    have hdiv' : squareRootEndpoint R / (1 * k) < p := by
      simpa using hdiv
    have hupper : lowWheelCanonicalDowncrossOwnershipUpper R 1 k < p := by
      unfold lowWheelCanonicalDowncrossOwnershipUpper
      exact (min_le_right _ _).trans_lt hdiv'
    rw [predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_upper_lt hupper]
    simp
  · rfl
  · rfl

/-- Exact statewise classification in the upper half.  A state contributes to
this fixed `p`-slice iff it is the unit-cofactor state of an owner in the later-
prime interval, and every such contribution is `-1`. -/
theorem upperHalfFirstJumpPrimeStateSlice_classification
    {R p c k : ℕ}
    (hR : 9 ≤ R)
    (hpSet : p ∈ signedFirstJumpPostRootPrimeSet R)
    (hhalf : R / 2 < p)
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R) :
    signedFirstJumpPrimeStateSlice R p (c, k) =
      if c = 1 ∧ k ∈ upperHalfFirstJumpOwnerSet R p then -1 else 0 := by
  by_cases hc : c = 1
  · subst c
    by_cases hk : k ∈ upperHalfFirstJumpOwnerSet R p
    · rw [upperHalfFirstJumpOwner_stateSlice_eq_neg_one
        (by omega) hpSet hhalf hk]
      simp [hk]
    · rw [upperHalfFirstJumpPrimeStateSlice_eq_zero_unit_of_not_owner hx hk]
      simp [hk]
  · rw [upperHalfFirstJumpPrimeStateSlice_eq_zero_of_cofactor_ne_one
      hR hhalf hx hc]
    simp [hc]

/-- Physical states belonging to the surviving upper-half owner column. -/
def upperHalfFirstJumpOwnerStateSet (R p : ℕ) :
    Finset LowWheelCofactorQuotientState :=
  (upperHalfFirstJumpOwnerSet R p).image fun k => (1, k)

/-- Every owner-column state is an actual member of the oriented state carrier. -/
theorem upperHalfFirstJumpOwnerStateSet_subset_carrier
    {R p : ℕ}
    (hR : 3 ≤ R)
    (hpSet : p ∈ signedFirstJumpPostRootPrimeSet R)
    (hhalf : R / 2 < p) :
    upperHalfFirstJumpOwnerStateSet R p ⊆
      lowWheelCanonicalDowncrossOrientedStateCarrier R := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  exact upperHalfFirstJumpOwner_state_mem hR hpSet hhalf hk

/-- The owner-state embedding `k |-> (1,k)` is injective. -/
theorem upperHalfFirstJumpOwnerStateSet_card (R p : ℕ) :
    (upperHalfFirstJumpOwnerStateSet R p).card =
      (upperHalfFirstJumpOwnerSet R p).card := by
  unfold upperHalfFirstJumpOwnerStateSet
  rw [Finset.card_image_of_injective _
    (fun a b hab => congrArg Prod.snd hab)]

/-- **Exact upper-half fixed-prime aggregate.**

For `R >= 9` and `R/2 < p <= R`, every non-owner state vanishes and every
owner contributes the same signed atom `-1`.  Thus the complete signed slice is
not controlled by `R/p`; it is literally the negative owner-prime count. -/
theorem signedFirstJumpPrimeSliceAggregate_eq_neg_upperHalfOwnerCard
    {R p : ℕ}
    (hR : 9 ≤ R)
    (hpSet : p ∈ signedFirstJumpPostRootPrimeSet R)
    (hhalf : R / 2 < p) :
    signedFirstJumpPrimeSliceAggregate R p =
      -((upperHalfFirstJumpOwnerSet R p).card : ℂ) := by
  classical
  have hsub :
      upperHalfFirstJumpOwnerStateSet R p ⊆
        lowWheelCanonicalDowncrossOrientedStateCarrier R :=
    upperHalfFirstJumpOwnerStateSet_subset_carrier (by omega) hpSet hhalf
  have hrestrict :
      (∑ x ∈ upperHalfFirstJumpOwnerStateSet R p,
          signedFirstJumpPrimeStateSlice R p x) =
        ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
          signedFirstJumpPrimeStateSlice R p x := by
    refine Finset.sum_subset hsub ?_
    intro x hxCarrier hxNotOwner
    rcases x with ⟨c, k⟩
    by_cases hc : c = 1
    · subst c
      by_cases hk : k ∈ upperHalfFirstJumpOwnerSet R p
      · exfalso
        apply hxNotOwner
        exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
      · exact upperHalfFirstJumpPrimeStateSlice_eq_zero_unit_of_not_owner
          hxCarrier hk
    · exact upperHalfFirstJumpPrimeStateSlice_eq_zero_of_cofactor_ne_one
        hR hhalf hxCarrier hc
  unfold signedFirstJumpPrimeSliceAggregate
  calc
    (∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        signedFirstJumpPrimeStateSlice R p x) =
      ∑ x ∈ upperHalfFirstJumpOwnerStateSet R p,
        signedFirstJumpPrimeStateSlice R p x := hrestrict.symm
    _ = ∑ _x ∈ upperHalfFirstJumpOwnerStateSet R p, (-1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      exact upperHalfFirstJumpOwner_stateSlice_eq_neg_one
        (by omega) hpSet hhalf hk
    _ = -((upperHalfFirstJumpOwnerStateSet R p).card : ℂ) := by simp
    _ = -((upperHalfFirstJumpOwnerSet R p).card : ℂ) := by
      rw [upperHalfFirstJumpOwnerStateSet_card]

/-- Norm form of the exact identity. -/
theorem norm_signedFirstJumpPrimeSliceAggregate_eq_upperHalfOwnerCard
    {R p : ℕ}
    (hR : 9 ≤ R)
    (hpSet : p ∈ signedFirstJumpPostRootPrimeSet R)
    (hhalf : R / 2 < p) :
    ‖signedFirstJumpPrimeSliceAggregate R p‖ =
      ((upperHalfFirstJumpOwnerSet R p).card : ℝ) := by
  rw [signedFirstJumpPrimeSliceAggregate_eq_neg_upperHalfOwnerCard
    hR hpSet hhalf]
  simp

/-- The owner cardinality is exactly the ordinary prime count in
`(p, (R^2-1)/p]`, written additively to avoid natural-number subtraction. -/
theorem upperHalfFirstJumpOwnerSet_card_add_primeCounting_eq
    {R p : ℕ}
    (hle : p ≤ squareRootEndpoint R / p) :
    (upperHalfFirstJumpOwnerSet R p).card + Nat.primeCounting p =
      Nat.primeCounting (squareRootEndpoint R / p) := by
  have hset :
      upperHalfFirstJumpOwnerSet R p =
        (Finset.Ioc p (squareRootEndpoint R / p)).filter Nat.Prime := by
    ext k
    simp [upperHalfFirstJumpOwnerSet, mem_frozenPrimeUniverseHighPrimeSet]
  rw [hset]
  exact primeCard_Ioc_add_primeCounting_eq hle

end RHLean.Proof
