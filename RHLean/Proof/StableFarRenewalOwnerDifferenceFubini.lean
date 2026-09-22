import Mathlib
import RHLean.Proof.StableFarRenewalChildFarCancellation

/-!
# Global Fubini of the stable-far owner-difference tower

After the exact odd ChildFar cancellation, the only odd returned-owner term is

  stableFarRenewalOddOwnerDifferenceTower.

This file proves that this live tower is exactly the production two-shell
physical boundary from StableFarRenewalGlobalBoundary.

The proof keeps the order:

1. discard no nonzero Mobius atom: nonsquarefree odd cofactors vanish natively;
2. Fubini the actual returned-coordinate carrier;
3. Fubini old owner against returned state;
4. remove zero owner changes;
5. use the globally injective squarefree transport.

No norm, triangle inequality, asymptotic estimate, PNT input, or RH hypothesis
is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Actual returned q2 states that occur as odd parents after owner two has
been split off. -/
def stableFarRenewalProductionReturnedTriples
    (R : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFarPrimeQ2DescendedTriples R).filter fun y =>
    y.1 ≠ 2 ∧ Odd y.2.1

@[simp] theorem mem_stableFarRenewalProductionReturnedTriples
    {R : ℕ} {y : ℕ × (ℕ × ℕ)} :
    y ∈ stableFarRenewalProductionReturnedTriples R ↔
      y ∈ lowWheelFarPrimeQ2DescendedTriples R ∧
      y.1 ≠ 2 ∧ Odd y.2.1 := by
  simp [stableFarRenewalProductionReturnedTriples]

/-- All old-owner / returned-state labels before deleting zero owner changes. -/
def stableFarRenewalProductionAmbient
    (R : ℕ) : Finset StableFarRenewalShellTag :=
  (primesUpTo (R - 1)).product
    (stableFarRenewalProductionReturnedTriples R)

/-- The owner-window cardinality difference is the sum of its pointwise
indicator differences, now in the exact complex charge currency. -/
theorem stableFarRenewalOwnerDifferenceWeight_eq_sum_productionCharge
    (R r p d : ℕ) :
    stableFarRenewalOwnerDifferenceWeight R r p d =
      ∑ q ∈ primesUpTo (R - 1),
        stableFarRenewalProductionCharge R (q, (r, (d, p))) := by
  have hcast := congrArg (fun z : ℤ => (z : ℂ))
    (crossingOuterOwnerSet_card_difference_eq_indicator_sum R r d p)
  push_cast at hcast
  unfold stableFarRenewalOwnerDifferenceWeight
    stableFarRenewalProductionCharge
  rw [hcast]
  rw [Finset.sum_mul]

/-- Restricting the odd rough prefix to the actual squarefree predecessor cube
changes no owner-difference mass.  The discarded nonsquarefree atoms have
native Mobius weight zero. -/
theorem stableFarRenewalOwnerDifferenceMass_eq_smoothOddSum
    (R r p B : ℕ) :
    stableFarRenewalOwnerDifferenceMass R r p B =
      ∑ d ∈ (squareRootLowPrimeGoSmoothCofactors r B).filter Odd,
        stableFarRenewalOwnerDifferenceWeight R r p d := by
  let T := oddCofactorPrefix B
  let S := (squareRootLowPrimeGoSmoothCofactors r B).filter Odd
  let F : ℕ → ℂ := fun d =>
    if canonicalLargestPrimeFactor d < r then
      stableFarRenewalOwnerDifferenceWeight R r p d
    else 0
  have hsub : S ⊆ T := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdSmooth, hdOdd⟩
    rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hdSmooth with
      ⟨hd1, hdB, _hdSq, _hdRough⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hd1, hdB⟩, hdOdd⟩
  have hzero :
      ∀ d ∈ T, d ∉ S → F d = 0 := by
    intro d hdT hdNotS
    rcases Finset.mem_filter.mp hdT with ⟨hdRange, hdOdd⟩
    rcases Finset.mem_Icc.mp hdRange with ⟨hd1, hdB⟩
    by_cases hrough : canonicalLargestPrimeFactor d < r
    · have hnotSq : ¬ Squarefree d := by
        intro hsq
        apply hdNotS
        exact Finset.mem_filter.mpr
          ⟨mem_squareRootLowPrimeGoSmoothCofactors.mpr
              ⟨hd1, hdB, hsq, hrough⟩,
            hdOdd⟩
      have hmu : μ d = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnotSq
      simp [F, hrough, stableFarRenewalOwnerDifferenceWeight,
        canonicalMoebiusWeight, hmu]
    · simp [F, hrough]
  unfold stableFarRenewalOwnerDifferenceMass
  change (∑ d ∈ T, F d) = _
  calc
    (∑ d ∈ T, F d) = ∑ d ∈ S, F d :=
      (Finset.sum_subset hsub hzero).symm
    _ = ∑ d ∈ S, stableFarRenewalOwnerDifferenceWeight R r p d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdSmooth := (Finset.mem_filter.mp hd).1
      have hrough :=
        (mem_squareRootLowPrimeGoSmoothCofactors.mp hdSmooth).2.2.2
      simp [F, hrough]

/-- Production returned fibre over one occupied odd coordinate pair. -/
def stableFarRenewalProductionReturnedFiber
    (R : ℕ) (rp : ℕ × ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (stableFarRenewalProductionReturnedTriples R).filter fun y =>
    (y.1, y.2.2) = rp

/-- One production returned fibre is exactly the odd part of the actual
squarefree predecessor cofactor carrier. -/
theorem stableFarRenewalProductionReturnedFiber_eq_oddCofactorImage
    {R : ℕ} {rp : ℕ × ℕ}
    (hrpOdd : rp ∈ stableFarRenewalOddCoordinatePairs R) :
    stableFarRenewalProductionReturnedFiber R rp =
      ((squareRootLowPrimeGoSmoothCofactors rp.1
          (stableFarReturnedCofactorCutoff R rp.1 rp.2)).filter Odd).image
        (fun d => (rp.1, (d, rp.2))) := by
  have hrp := (Finset.mem_filter.mp hrpOdd).1
  have hrne := (Finset.mem_filter.mp hrpOdd).2
  have hdata := stableFarRenewalCoordinatePair_data hrp
  ext y
  rcases y with ⟨r, ⟨d, p⟩⟩
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hyProd, hcoord⟩
    rcases Finset.mem_filter.mp hyProd with
      ⟨hdesc, _hrneY, hdOdd⟩
    have hrEq : r = rp.1 := congrArg Prod.fst hcoord
    have hpEq : p = rp.2 := congrArg Prod.snd hcoord
    subst r
    subst p
    have hdSmooth :=
      (mem_lowWheelFarPrimeQ2DescendedTriples_iff_renewalCofactor).1 hdesc
    exact Finset.mem_image.mpr
      ⟨d, Finset.mem_filter.mpr ⟨hdSmooth.2.2.2.2, hdOdd⟩, rfl⟩
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨d', hd', heq⟩
    rcases Finset.mem_filter.mp hd' with ⟨hdSmooth, hdOdd⟩
    have hdesc :
        (rp.1, (d', rp.2)) ∈ lowWheelFarPrimeQ2DescendedTriples R :=
      (mem_lowWheelFarPrimeQ2DescendedTriples_iff_renewalCofactor).2
        ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2, hdSmooth⟩
    have hprod :
        (rp.1, (d', rp.2)) ∈
          stableFarRenewalProductionReturnedTriples R :=
      Finset.mem_filter.mpr ⟨hdesc, hrne, hdOdd⟩
    have hfiber :
        (rp.1, (d', rp.2)) ∈
          stableFarRenewalProductionReturnedFiber R rp :=
      Finset.mem_filter.mpr ⟨hprod, rfl⟩
    rw [heq] at hfiber
    exact hfiber

/-- One returned production fibre, after summing old owners, is exactly its
owner-difference mass. -/
theorem stableFarRenewalProductionReturnedFiber_charge_eq_ownerDifferenceMass
    {R : ℕ} {rp : ℕ × ℕ}
    (hrpOdd : rp ∈ stableFarRenewalOddCoordinatePairs R) :
    (∑ y ∈ stableFarRenewalProductionReturnedFiber R rp,
      ∑ q ∈ primesUpTo (R - 1),
        stableFarRenewalProductionCharge R (q, y)) =
      stableFarRenewalOwnerDifferenceMass R rp.1 rp.2
        (stableFarReturnedCofactorCutoff R rp.1 rp.2) := by
  rw [stableFarRenewalProductionReturnedFiber_eq_oddCofactorImage hrpOdd]
  rw [Finset.sum_image]
  · rw [stableFarRenewalOwnerDifferenceMass_eq_smoothOddSum]
    apply Finset.sum_congr rfl
    intro d _hd
    exact
      (stableFarRenewalOwnerDifferenceWeight_eq_sum_productionCharge
        R rp.1 rp.2 d).symm
  · intro a _ha b _hb hab
    exact congrArg (fun y : ℕ × (ℕ × ℕ) => y.2.1) hab

/-- Fubini the live odd owner-difference tower back to its actual returned
triple carrier. -/
theorem stableFarRenewalOddOwnerDifferenceTower_eq_returnedCharge
    (R : ℕ) :
    stableFarRenewalOddOwnerDifferenceTower R =
      ∑ y ∈ stableFarRenewalProductionReturnedTriples R,
        ∑ q ∈ primesUpTo (R - 1),
          stableFarRenewalProductionCharge R (q, y) := by
  let S := stableFarRenewalProductionReturnedTriples R
  let T := stableFarRenewalOddCoordinatePairs R
  let g : ℕ × (ℕ × ℕ) → ℕ × ℕ := fun y => (y.1, y.2.2)
  let f : ℕ × (ℕ × ℕ) → ℂ := fun y =>
    ∑ q ∈ primesUpTo (R - 1),
      stableFarRenewalProductionCharge R (q, y)
  have hmaps : ∀ y ∈ S, g y ∈ T := by
    intro y hy
    have hprod := Finset.mem_filter.mp hy
    have hcoord :
        (y.1, y.2.2) ∈ stableFarRenewalCoordinatePairs R :=
      Finset.mem_image.mpr ⟨y, hprod.1, rfl⟩
    exact Finset.mem_filter.mpr ⟨hcoord, hprod.2.1⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := g) hmaps f
  have hraw :
      (∑ y ∈ S, f y) =
        ∑ rp ∈ T, ∑ y ∈ S with g y = rp, f y :=
    hfiber.symm
  unfold stableFarRenewalOddOwnerDifferenceTower
  change
    (∑ rp ∈ T,
      stableFarRenewalOwnerDifferenceMass R rp.1 rp.2
        (stableFarReturnedCofactorCutoff R rp.1 rp.2)) =
      ∑ y ∈ S, f y
  rw [hraw]
  apply Finset.sum_congr rfl
  intro rp hrp
  change
    stableFarRenewalOwnerDifferenceMass R rp.1 rp.2
        (stableFarReturnedCofactorCutoff R rp.1 rp.2) =
      ∑ y ∈ stableFarRenewalProductionReturnedFiber R rp,
        ∑ q ∈ primesUpTo (R - 1),
          stableFarRenewalProductionCharge R (q, y)
  exact
    (stableFarRenewalProductionReturnedFiber_charge_eq_ownerDifferenceMass
      hrp).symm

/-- Cartesian-product form of the same returned charge. -/
theorem stableFarRenewalReturnedCharge_eq_ambientCharge
    (R : ℕ) :
    (∑ y ∈ stableFarRenewalProductionReturnedTriples R,
      ∑ q ∈ primesUpTo (R - 1),
        stableFarRenewalProductionCharge R (q, y)) =
      ∑ t ∈ stableFarRenewalProductionAmbient R,
        stableFarRenewalProductionCharge R t := by
  unfold stableFarRenewalProductionAmbient
  calc
    (∑ y ∈ stableFarRenewalProductionReturnedTriples R,
      ∑ q ∈ primesUpTo (R - 1),
        stableFarRenewalProductionCharge R (q, y)) =
        ∑ q ∈ primesUpTo (R - 1),
          ∑ y ∈ stableFarRenewalProductionReturnedTriples R,
            stableFarRenewalProductionCharge R (q, y) := by
      exact Finset.sum_comm
    _ =
        ∑ t ∈ (primesUpTo (R - 1)).product
            (stableFarRenewalProductionReturnedTriples R),
          stableFarRenewalProductionCharge R t := by
      symm
      simpa only using
        (Finset.sum_product
          (s := primesUpTo (R - 1))
          (t := stableFarRenewalProductionReturnedTriples R)
          (f := fun t : ℕ × (ℕ × (ℕ × ℕ)) =>
            stableFarRenewalProductionCharge R t))

/-- The production two-shell carrier is exactly the nonzero-shell filter of the
ambient old-owner/returned-state product. -/
theorem stableFarRenewalProductionTwoShellCarrier_eq_ambient_filter
    (R : ℕ) :
    stableFarRenewalProductionTwoShellCarrier R =
      (stableFarRenewalProductionAmbient R).filter fun t =>
        stableFarRenewalFirstCutShell
            R t.1 t.2.1 t.2.2.1 t.2.2.2 ∨
          stableFarRenewalSecondCrossShell
            R t.1 t.2.1 t.2.2.1 t.2.2.2 := by
  ext t
  simp [stableFarRenewalProductionTwoShellCarrier,
    stableFarRenewalTwoShellCarrier,
    stableFarRenewalProductionAmbient,
    stableFarRenewalProductionReturnedTriples,
    and_assoc, and_left_comm, and_comm]

/-- Outside the two threshold shells the owner indicator difference is zero,
hence so is the production charge. -/
theorem stableFarRenewalProductionCharge_eq_zero_of_not_shell
    {R : ℕ} {t : StableFarRenewalShellTag}
    (hnot :
      ¬ (stableFarRenewalFirstCutShell
            R t.1 t.2.1 t.2.2.1 t.2.2.2 ∨
          stableFarRenewalSecondCrossShell
            R t.1 t.2.1 t.2.2.1 t.2.2.2)) :
    stableFarRenewalProductionCharge R t = 0 := by
  rcases t with ⟨q, ⟨r, ⟨d, p⟩⟩⟩
  have hdiff :
      stableFarRenewalOwnerIndicatorDifference R q r d p = 0 := by
    by_contra hne
    have hraw :=
      renewalOwnerIndicatorDifference_ne_zero_imp_two_shells hne
    apply hnot
    unfold stableFarRenewalFirstCutShell stableFarRenewalSecondCrossShell
    tauto
  simp [stableFarRenewalProductionCharge, hdiff]

/-- Deleting zero owner changes from the ambient product loses no signed mass. -/
theorem stableFarRenewalAmbientCharge_eq_productionCarrierCharge
    (R : ℕ) :
    (∑ t ∈ stableFarRenewalProductionAmbient R,
        stableFarRenewalProductionCharge R t) =
      ∑ t ∈ stableFarRenewalProductionTwoShellCarrier R,
        stableFarRenewalProductionCharge R t := by
  rw [stableFarRenewalProductionTwoShellCarrier_eq_ambient_filter]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hshell :
      stableFarRenewalFirstCutShell
          R t.1 t.2.1 t.2.2.1 t.2.2.2 ∨
        stableFarRenewalSecondCrossShell
          R t.1 t.2.1 t.2.2.1 t.2.2.2
  · simp [hshell]
  · have hzero :=
      stableFarRenewalProductionCharge_eq_zero_of_not_shell
        (R := R) (t := t) hshell
    simp [hshell, hzero]

/-- **Exact representation theorem.**  The complete odd owner-difference tower
left after the ChildFar cancellation is literally the signed, multiplicity-one
squarefree physical boundary from #787. -/
theorem stableFarRenewalOddOwnerDifferenceTower_eq_signedPhysicalBoundary
    (R : ℕ) :
    stableFarRenewalOddOwnerDifferenceTower R =
      stableFarRenewalProductionSignedBoundaryMass R := by
  rw [stableFarRenewalOddOwnerDifferenceTower_eq_returnedCharge,
    stableFarRenewalReturnedCharge_eq_ambientCharge,
    stableFarRenewalAmbientCharge_eq_productionCarrierCharge,
    stableFarRenewalProductionCharge_sum_eq_signedBoundaryMass]

end RHLean.Proof
