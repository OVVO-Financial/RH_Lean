import Mathlib
import RHLean.Proof.StableFarRenewalGlobalBoundary
import RHLean.Proof.RoughDyadicQ2Compression

/-!
# Cancel the odd q2 ChildFar bulk against the centered renewal boundary

The complete returned-fibre theorem leaves, for every odd returned owner r,

  centered fibre
    = owner-difference mass + r-rough dyadic boundary.

The exact far-prime range theorem identifies the sum of those rough boundaries
over p with the q2 ChildFar rough column for the same r.  The #785 compression
identifies that column with the literal ChildFar slice.

Therefore the odd-owner ChildFar population appearing on the source side of
the centered-incidence identity cancels exactly with the rough-boundary
population appearing inside the centered q2 tower.  The cancellation occurs
before any norm or triangle inequality.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

def stableFarRenewalOwnerTwoCenteredTower (R : ℕ) : ℂ :=
  ∑ rp ∈ stableFarRenewalOwnerTwoCoordinatePairs R,
    stableFarCenteredReturnedFibre R rp.1 rp.2

def stableFarRenewalOddOwnerDifferenceTower (R : ℕ) : ℂ :=
  ∑ rp ∈ stableFarRenewalOddCoordinatePairs R,
    stableFarRenewalOwnerDifferenceMass R rp.1 rp.2
      (stableFarReturnedCofactorCutoff R rp.1 rp.2)

def stableFarRenewalOddRoughBoundaryTower (R : ℕ) : ℂ :=
  ∑ rp ∈ stableFarRenewalOddCoordinatePairs R,
    roughDyadicCofactorBoundaryMass rp.1
      (stableFarReturnedCofactorCutoff R rp.1 rp.2)

/-- The global centered q2 tower splits into owner two, the signed
owner-difference field, and the odd rough dyadic boundary. -/
theorem farFourQ2CenteredTower_eq_ownerTwo_add_oddDifference_add_roughBoundary
    (R : ℕ) :
    farFourQ2CenteredTower R =
      stableFarRenewalOwnerTwoCenteredTower R +
        stableFarRenewalOddOwnerDifferenceTower R +
          stableFarRenewalOddRoughBoundaryTower R := by
  rw [farFourQ2CenteredTower_eq_sum_stableFarCenteredReturnedFibre]
  let S := stableFarRenewalCoordinatePairs R
  let f : ℕ × ℕ → ℂ := fun rp =>
    stableFarCenteredReturnedFibre R rp.1 rp.2
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not S (fun rp => rp.1 = 2) f
  change (∑ rp ∈ S, f rp) = _
  rw [← hsplit]
  unfold stableFarRenewalOwnerTwoCenteredTower
    stableFarRenewalOddOwnerDifferenceTower
    stableFarRenewalOddRoughBoundaryTower
    stableFarRenewalOwnerTwoCoordinatePairs
    stableFarRenewalOddCoordinatePairs
  change
    (∑ rp ∈ S.filter (fun rp => rp.1 = 2), f rp) +
        ∑ rp ∈ S.filter (fun rp => rp.1 ≠ 2), f rp =
      (∑ rp ∈ S.filter (fun rp => rp.1 = 2), f rp) +
        (∑ rp ∈ S.filter (fun rp => rp.1 ≠ 2),
          stableFarRenewalOwnerDifferenceMass R rp.1 rp.2
            (stableFarReturnedCofactorCutoff R rp.1 rp.2)) +
        ∑ rp ∈ S.filter (fun rp => rp.1 ≠ 2),
          roughDyadicCofactorBoundaryMass rp.1
            (stableFarReturnedCofactorCutoff R rp.1 rp.2)
  have hodd :
      (∑ rp ∈ S.filter (fun rp => rp.1 ≠ 2), f rp) =
        (∑ rp ∈ S.filter (fun rp => rp.1 ≠ 2),
          stableFarRenewalOwnerDifferenceMass R rp.1 rp.2
            (stableFarReturnedCofactorCutoff R rp.1 rp.2)) +
        ∑ rp ∈ S.filter (fun rp => rp.1 ≠ 2),
          roughDyadicCofactorBoundaryMass rp.1
            (stableFarReturnedCofactorCutoff R rp.1 rp.2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro rp hrpOdd
    rcases Finset.mem_filter.mp hrpOdd with ⟨hrp, hrne⟩
    have hdata := stableFarRenewalCoordinatePair_data hrp
    have hrgt : 2 < rp.1 := by
      have hr2 := hdata.1.two_le
      omega
    exact stableFarCenteredReturnedFibre_eq_fullDifference_add_roughBoundaryMass
      hdata.1 hrgt hdata.2.2.1
  simpa [add_assoc] using congrArg
    (fun z : ℂ =>
      (∑ rp ∈ S.filter (fun rp => rp.1 = 2), f rp) + z) hodd

/-- At one fixed odd returned owner, summing the rough boundary over the
coordinate-pair fibre is exactly the named rough-boundary column. -/
theorem stableFarRenewalOddCoordinateFiber_roughBoundary_eq_column
    {R r : ℕ} (hrne : r ≠ 2) :
    (∑ rp ∈ stableFarRenewalOddCoordinatePairs R with rp.1 = r,
      roughDyadicCofactorBoundaryMass rp.1
        (stableFarReturnedCofactorCutoff R rp.1 rp.2)) =
      stableFarRenewalRoughBoundaryColumn R r := by
  have hfilter :
      (stableFarRenewalOddCoordinatePairs R).filter (fun rp => rp.1 = r) =
        (stableFarRenewalCoordinatePairs R).filter (fun rp => rp.1 = r) := by
    ext rp
    constructor
    · intro h
      rcases Finset.mem_filter.mp h with ⟨hodd, heq⟩
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hodd).1, heq⟩
    · intro h
      rcases Finset.mem_filter.mp h with ⟨hrp, heq⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hrp, ?_⟩, heq⟩
      rw [heq]
      exact hrne
  change
    (∑ rp ∈ (stableFarRenewalOddCoordinatePairs R).filter
        (fun rp => rp.1 = r),
      roughDyadicCofactorBoundaryMass rp.1
        (stableFarReturnedCofactorCutoff R rp.1 rp.2)) =
      stableFarRenewalRoughBoundaryColumn R r
  rw [hfilter]
  unfold stableFarRenewalRoughBoundaryColumn
    stableFarRenewalFarPrimeSet
  symm
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro rp hrp
    have heq := (Finset.mem_filter.mp hrp).2
    rw [heq]
  · intro a ha b hb hab
    have haR := (Finset.mem_filter.mp ha).2
    have hbR := (Finset.mem_filter.mp hb).2
    apply Prod.ext
    · exact haR.trans hbR.symm
    · exact hab

/-- Globally, the rough boundary left by the centered odd returned fibres is
exactly the #785 odd-owner q2 ChildFar rough column. -/
theorem stableFarRenewalOddRoughBoundaryTower_eq_q2ChildFarRoughColumn
    (R : ℕ) :
    stableFarRenewalOddRoughBoundaryTower R =
      squareEndpointQ2OddChildFarRoughDyadicColumn R := by
  let S := stableFarRenewalOddCoordinatePairs R
  let T := (primesUpTo (R - 1)).erase 2
  let g : ℕ × ℕ → ℕ := Prod.fst
  let f : ℕ × ℕ → ℂ := fun rp =>
    roughDyadicCofactorBoundaryMass rp.1
      (stableFarReturnedCofactorCutoff R rp.1 rp.2)
  have hmaps : ∀ rp ∈ S, g rp ∈ T := by
    intro rp hrp
    have hmem := Finset.mem_filter.mp hrp
    have hdata := stableFarRenewalCoordinatePair_data hmem.1
    apply Finset.mem_erase.mpr
    exact ⟨hmem.2,
      mem_primesUpTo.mpr ⟨hdata.1, Nat.le_pred_of_lt hdata.2.1⟩⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := g) hmaps f
  have hraw :
      (∑ rp ∈ S, f rp) =
        ∑ r ∈ T, ∑ rp ∈ S with g rp = r, f rp :=
    hfiber.symm
  unfold stableFarRenewalOddRoughBoundaryTower
  change (∑ rp ∈ S, f rp) =
    squareEndpointQ2OddChildFarRoughDyadicColumn R
  rw [hraw]
  unfold squareEndpointQ2OddChildFarRoughDyadicColumn
  apply Finset.sum_congr rfl
  intro r hrT
  rcases Finset.mem_erase.mp hrT with ⟨hrne, hrmem⟩
  have hrPrime := (mem_primesUpTo.mp hrmem).1
  have hrR : r < R := by
    have hrLe := (mem_primesUpTo.mp hrmem).2
    have hr2 : 2 ≤ r := hrPrime.two_le
    have hRpos : 0 < R := by omega
    exact Nat.lt_of_le_pred hRpos hrLe
  change
    (∑ rp ∈ stableFarRenewalOddCoordinatePairs R with rp.1 = r,
      roughDyadicCofactorBoundaryMass rp.1
        (stableFarReturnedCofactorCutoff R rp.1 rp.2)) =
      q2DaughterFarRoughDyadicColumn R r
  rw [stableFarRenewalOddCoordinateFiber_roughBoundary_eq_column hrne,
    stableFarRenewalRoughBoundaryColumn_eq_q2DaughterFarRoughDyadicColumn
      hrPrime hrR]

/-- The same global rough-boundary tower is the literal odd-owner ChildFar
population, not a new residual. -/
theorem stableFarRenewalOddRoughBoundaryTower_eq_oddChildFarSlice
    (R : ℕ) :
    stableFarRenewalOddRoughBoundaryTower R =
      ∑ q ∈ (primesUpTo (R - 1)).erase 2,
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1 := by
  rw [stableFarRenewalOddRoughBoundaryTower_eq_q2ChildFarRoughColumn]
  exact (squareEndpointQ2OddChildFarSlice_eq_roughDyadicColumn R).symm

/-- **Pre-norm odd ChildFar cancellation normal form.**  The centered q2 tower
is owner two plus the signed owner-difference field plus exactly the literal
odd-owner ChildFar population. -/
theorem farFourQ2CenteredTower_eq_ownerTwo_add_oddDifference_add_oddChildFar
    (R : ℕ) :
    farFourQ2CenteredTower R =
      stableFarRenewalOwnerTwoCenteredTower R +
        stableFarRenewalOddOwnerDifferenceTower R +
        ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
            canonicalMoebiusWeight dp.1 := by
  rw [farFourQ2CenteredTower_eq_ownerTwo_add_oddDifference_add_roughBoundary,
    stableFarRenewalOddRoughBoundaryTower_eq_oddChildFarSlice]

/-- **Odd q2 bulk disappears.**  After substituting the exact centered-tower
normal form into the two-level incidence identity, the complete odd-owner
ChildFar population occurs on both sides and cancels algebraically.

What remains is owner two, the globally signed owner-difference tower, and the
unit/terminal centered correction. -/
theorem stableFarRenewal_incidence_after_oddChildFar_cancellation
    (R : ℕ) (hR : 3 ≤ R) :
    (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R 2,
        canonicalMoebiusWeight dp.1) +
      (∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
        lowWheelFullTaggedPhysicalWeight
          (lowWheelFarPrimeCrossingStableState x)) +
      (∑ p ∈ lowWheelFarPrimeUnitProducts R,
        canonicalMoebiusWeight p) =
    stableFarRenewalOwnerTwoCenteredTower R +
      stableFarRenewalOddOwnerDifferenceTower R +
      ∑ p ∈ lowWheelFarPrimeUnitProducts R,
        ((lowWheelFarPrimeQ2UnitCrossingMultiplicity R p : ℂ) - 1) := by
  have hincidence :=
    lowWheelFarPrimeChildFar_add_crossingRenewal_add_unitTerminal_eq_centered R
  have htwo : 2 ∈ primesUpTo (R - 1) :=
    mem_primesUpTo.mpr ⟨Nat.prime_two, by omega⟩
  have hsplit := Finset.sum_erase_add
    (s := primesUpTo (R - 1))
    (f := fun q =>
      ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
        canonicalMoebiusWeight dp.1) htwo
  have hchild :
      (∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1) =
      (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R 2,
        canonicalMoebiusWeight dp.1) +
      ∑ q ∈ (primesUpTo (R - 1)).erase 2,
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1 := by
    calc
      (∑ q ∈ primesUpTo (R - 1),
        ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
          canonicalMoebiusWeight dp.1) =
        (∑ q ∈ (primesUpTo (R - 1)).erase 2,
          ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
            canonicalMoebiusWeight dp.1) +
        (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R 2,
          canonicalMoebiusWeight dp.1) := hsplit.symm
      _ = _ := by ring
  rw [hchild] at hincidence
  have hcenter :
      (∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
        (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
          canonicalMoebiusWeight y.2.1) =
        farFourQ2CenteredTower R := by
    rfl
  rw [hcenter,
    farFourQ2CenteredTower_eq_ownerTwo_add_oddDifference_add_oddChildFar] at hincidence
  linear_combination hincidence

end RHLean.Proof
