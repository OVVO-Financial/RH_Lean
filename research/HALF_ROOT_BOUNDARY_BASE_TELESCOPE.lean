import «research.HALF_ROOT_SQUARE_CORRECTION_BOUND»
import RHLean.Proof.LowWheelCanonicalDefectReduction

/-!
# Consume the middle moving boundary inside the frozen base

After #608 the remaining object is the signed frozen base minus its moving
boundary column.  Apply the Euler telescope to those two terms together.
For `Y <= K <= X` and `X < (Y+1)^3`,

`F_Y(X) - sum_{Y<p<=K} F_p(X/p)
   = F_K(X) + sum_{Y<p<=K} M(X/p^2)`.

At `Y=R/2`, `K=R`, the entire middle moving boundary is therefore consumed
by advancing the base to the physical root.  The residual is exactly the
square correction already bounded in #608, with no second copy of that error.
Every remaining owner `p>R` is an ordinary lower Mertens state.  Consequently

`halfRootBoundaryCoupledCore = smooth - highTransport + squareCorrection
   = M(R) - canonicalDefect + squareCorrection`.

These are exact bridges to the existing signed carrier.  The middle
chronology costs only the known root-scale correction.  The signed root
smooth/transport coupling, equivalently the canonical defect, still requires
a quantitative estimate.  No bound on that defect or new global Mertens
exponent is asserted here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Telescope the base and a complete prefix of its moving boundary together.
The only failure of exact cutoff invariance is the completed square column. -/
theorem properSubwheel_base_sub_boundaryPrefix_eq_advancedBase_add_squares
    (X Y K : ℕ) (hYK : Y ≤ K) (hKX : K ≤ X)
    (hcubic : X < (Y + 1) ^ 3) :
    frozenPrimeUniverseMass (primesUpTo Y) X -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y K,
          frozenPrimeUniverseMass (primesUpTo p) (X / p)) =
      frozenPrimeUniverseMass (primesUpTo K) X +
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y K,
          mertensSummatoryInt (X / (p * p)) := by
  have htel := frozenPrimeUniverse_highUpperColumn_telescope X Y K hYK
  have hsplit :
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y K,
        frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) =
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y K,
        frozenPrimeUniverseMass (primesUpTo p) (X / p)) +
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y K,
        mertensSummatoryInt (X / (p * p)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
    have hpFull : p ∈ frozenPrimeUniverseHighPrimeSet Y X :=
      mem_frozenPrimeUniverseHighPrimeSet.mpr
        ⟨hpData.1, hpData.2.1, hpData.2.2.trans hKX⟩
    exact properSubwheel_highOwnerMovingTerm_eq_boundary_add_mertensSquare
      hpFull hcubic
  omega

private theorem halfRootBoundary_root_le_endpoint (R : ℕ) (hR : 6 ≤ R) :
    R ≤ squareRootEndpoint R := by
  have hquad : R + 1 ≤ R ^ 2 := by nlinarith
  unfold squareRootEndpoint
  omega

/-- The whole middle boundary cancels against the base's advance from `R/2`
to `R`.  Its residue is the same square correction as in #608. -/
theorem halfRoot_base_sub_middleBoundary_eq_rootBase_add_squareCorrection
    (R : ℕ) (hR : 6 ≤ R) :
    frozenPrimeUniverseMass (primesUpTo (R / 2)) (squareRootEndpoint R) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) R,
          frozenPrimeUniverseMass (primesUpTo p) (squareRootEndpoint R / p)) =
      frozenPrimeUniverseMass (primesUpTo R) (squareRootEndpoint R) +
        halfRootPrimeSquareCorrection R := by
  have hRX := halfRootBoundary_root_le_endpoint R hR
  have htel := properSubwheel_base_sub_boundaryPrefix_eq_advancedBase_add_squares
    (squareRootEndpoint R) (R / 2) R (Nat.div_le_self R 2) hRX
    (squareRootEndpoint_lt_halfRootSucc_cube R hR)
  have hsquares :
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) R,
        mertensSummatoryInt (squareRootEndpoint R / (p * p))) =
      halfRootPrimeSquareCorrection R := by
    rw [halfRootPrimeSquareCorrection_eq_middleSum R hR]
    apply Finset.sum_congr rfl
    intro p hp
    have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
    exact mertensSummatoryInt_squareRootEndpoint_div_square_eq_halfRootPrimeSquareWeight
      hR (mem_frozenPrimeUniverseHighPrimeSet.mpr
        ⟨hpData.1, hpData.2.1, hpData.2.2.trans hRX⟩)
  rw [hsquares] at htel
  exact htel

/-- The middle chronological coupling has root-scale error after cancellation.
This does not take separate norms of the frozen base or the moving column. -/
theorem abs_halfRoot_base_sub_middleBoundary_sub_rootBase_le_root_add_one
    (R : ℕ) (hR : 6 ≤ R) :
    |(frozenPrimeUniverseMass (primesUpTo (R / 2)) (squareRootEndpoint R) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) R,
          frozenPrimeUniverseMass (primesUpTo p) (squareRootEndpoint R / p))) -
      frozenPrimeUniverseMass (primesUpTo R) (squareRootEndpoint R)| ≤
        (R + 1 : ℤ) := by
  rw [halfRoot_base_sub_middleBoundary_eq_rootBase_add_squareCorrection R hR]
  simpa using abs_halfRootPrimeSquareCorrection_le_root_add_one R hR

/-- No unfinished middle frozen state remains.  The complete coupled core is
the root frozen base minus the ordinary high-prime Mertens band, plus the
single square correction. -/
theorem halfRootBoundaryCoupledCore_eq_rootBase_sub_topMertens_add_squareCorrection
    (R : ℕ) (hR : 6 ≤ R) :
    halfRootBoundaryCoupledCore R =
      (frozenPrimeUniverseMass (primesUpTo R) (squareRootEndpoint R) -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet R (squareRootEndpoint R),
          mertensSummatoryInt (squareRootEndpoint R / p)) +
        halfRootPrimeSquareCorrection R := by
  have hsplit := sum_frozenPrimeUniverseHighPrimeSet_split
    (R / 2) R (squareRootEndpoint R) (Nat.div_le_self R 2)
    (halfRootBoundary_root_le_endpoint R hR)
    (fun p => frozenPrimeUniverseMass (primesUpTo p) (squareRootEndpoint R / p))
  have hmiddle := halfRoot_base_sub_middleBoundary_eq_rootBase_add_squareCorrection R hR
  rw [squareRootProperSubwheel_topBoundary_eq_mertensBand R (by omega)] at hsplit
  unfold halfRootBoundaryCoupledCore halfRootMovingBoundaryColumn
  rw [hsplit]
  omega

/-- The root coupling is exactly the physical endpoint Mertens value.
Combining the two cancellations removes their shared square correction;
it does not create an extra root-scale error. -/
theorem halfRoot_rootBase_sub_topMertens_eq_mertensSummatoryInt
    (R : ℕ) (hR : 6 ≤ R) :
    frozenPrimeUniverseMass (primesUpTo R) (squareRootEndpoint R) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet R (squareRootEndpoint R),
          mertensSummatoryInt (squareRootEndpoint R / p)) =
      mertensSummatoryInt (squareRootEndpoint R) := by
  have hmain :=
    squareRootProperSubwheelFrozenCorrelation_eq_halfRootBoundary_sub_squareCorrection R hR
  have hcore :=
    halfRootBoundaryCoupledCore_eq_rootBase_sub_topMertens_add_squareCorrection R hR
  have hM : squareRootProperSubwheelFrozenCorrelation R (R / 2) =
      mertensSummatoryInt (squareRootEndpoint R) := by
    rw [squareRootProperSubwheelFrozenCorrelation_eq_roughMertens]
    unfold roughMertens mertensSummatoryInt
    simp [roughMoebius]
  rw [hM] at hmain
  unfold halfRootBoundaryCoupledCore at hcore
  omega

private theorem halfRootBoundary_mertensSummatoryInt_cast (X : ℕ) :
    (mertensSummatoryInt X : ℂ) = mertensSummatory X := by
  rw [← frozenPrimeUniverseMass_primesUpTo_self_eq_mertensSummatoryInt]
  exact frozenPrimeUniverseMass_primesUpTo_cast_eq_mertens le_rfl

/-- Exact bridge to the repository's `smooth - highTransport` identity. -/
theorem halfRootBoundaryCoupledCore_cast_eq_smooth_sub_transport_add_squareCorrection
    (R : ℕ) (hR : 6 ≤ R) :
    (halfRootBoundaryCoupledCore R : ℂ) =
      squareRootSmoothMass (R - 1) - squareRootTransportCofactorFirst R +
        (halfRootPrimeSquareCorrection R : ℂ) := by
  rw [halfRootBoundaryCoupledCore_eq_rootBase_sub_topMertens_add_squareCorrection R hR,
    halfRoot_rootBase_sub_topMertens_eq_mertensSummatoryInt R hR,
    Int.cast_add, halfRootBoundary_mertensSummatoryInt_cast]
  have hclock : mertensSummatory (squareRootEndpoint R) =
      squarePrefixMertens (R - 1) := by
    unfold squarePrefixMertens squarePrefixEndpoint squareRootEndpoint
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R)]
  rw [hclock, squarePrefixMertens_eq_squareRootSmooth_sub_transport,
    squareRootTransportMass_pred_eq_cofactorFirst R (by omega)]

/-- The remaining signed coupling is the existing canonical defect on the
same physical root carrier, with the known square correction retained. -/
theorem halfRootBoundaryCoupledCore_cast_eq_lowerMertens_sub_canonicalDefect_add_squareCorrection
    (R : ℕ) (hR : 6 ≤ R) :
    (halfRootBoundaryCoupledCore R : ℂ) =
      mertensSummatory R - lowWheelCanonicalDefectLedger R +
        (halfRootPrimeSquareCorrection R : ℂ) := by
  rw [halfRootBoundaryCoupledCore_cast_eq_smooth_sub_transport_add_squareCorrection R hR,
    squareRootTransportCofactorFirst_eq_smooth_sub_mertens_add_defect R (by omega)]
  ring

end RHLean.Proof
