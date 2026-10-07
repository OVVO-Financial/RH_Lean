import Mathlib
import «research.VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI»

/-!
# First-bad active physical excess ledger

This module removes the identity root from first-owner Fubini completely.

The active squarefree physical field is partitioned by first owner at clock
`R + 1`.  The identity site `n = 1`, the squareful restoring packet, and
the omitted-seat denominator mass remain in a global residual.  No term from
those excluded carriers is assigned a fictitious first owner.

The main theorem is an exact equality for

  `2 * D_(R+1)^2 - T_R`

as

  global active/root residual
  + sum of weighted active first-owner cell excesses.

No analytic estimate or sign assumption is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The active physical site has exactly the absolute mass already named by
`vfMidOneBlockUpperActiveAbsMass` when summed on the common Möbius clock. -/
theorem vfMidOneBlockActivePhysicalSite_absSum_eq
    (R : ℕ) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
      |vfMidOneBlockActivePhysicalSite R n|) =
      vfMidOneBlockUpperActiveAbsMass R := by
  have hsub :
      vfMidOneBlockActivePhysicalCarrier R ⊆
        lowOwnerNonzeroMobiusCarrier (R + 1) :=
    vfMidOneBlockActivePhysicalCarrier_subset_lowOwner_succ
  have hzero :
      ∀ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
        n ∉ vfMidOneBlockActivePhysicalCarrier R →
          |vfMidOneBlockActivePhysicalSite R n| = 0 := by
    intro n _hn hnot
    simp [vfMidOneBlockActivePhysicalSite, hnot]
  have hs :=
    Finset.sum_subset hsub hzero
  calc
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier (R + 1),
      |vfMidOneBlockActivePhysicalSite R n|) =
      ∑ n ∈ vfMidOneBlockActivePhysicalCarrier R,
        |vfMidOneBlockActivePhysicalSite R n| := hs.symm
    _ = vfMidOneBlockUpperActiveAbsMass R := by
      unfold vfMidOneBlockUpperActiveAbsMass
      apply Finset.sum_congr rfl
      intro n hn
      simp [vfMidOneBlockActivePhysicalSite, hn]

/-- Literal active diagonal after the identity root has been removed. -/
def vfMidActivePhysicalDiagonalMass (R : ℕ) : ℝ :=
  lowOwnerGlobalDiagonalPairMassWith (R + 1)
    (vfMidOneBlockActivePhysicalSite R)

/-- Ordered contribution of one active physical first-owner cell to twice the
actual endpoint-energy demand. -/
def vfMidActiveWeightedCellDemand
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  4 * lowOwnerFirstOwnerCellGramWith (R + 1) p sig
    (vfMidOneBlockActivePhysicalSite R)

/-- Matching absolute pair capacity on the same active physical cell. -/
def vfMidActiveWeightedCellCapacity
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  2 * lowOwnerFirstOwnerCellGramWith (R + 1) p sig
    (fun n => |vfMidOneBlockActivePhysicalSite R n|)

/-- Pure active-cell Co/Div excess.  This is the only local currency intended
for the weighted six-sector continuation partition. -/
def vfMidActiveWeightedCellExcess
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  vfMidActiveWeightedCellDemand R p sig -
    vfMidActiveWeightedCellCapacity R p sig

/-- The signed identity-root gate, written without putting `n = 1` into any
first-owner cell.  With `A_R = -D_R` and active signed mass `X_R`, this is
exactly `A_R^2 + 2 A_R X_R`. -/
def vfMidActiveIdentityAnchorGate (R : ℕ) : ℝ :=
  vfMidActualPrimeEndpointDefect R ^ 2 -
    2 * vfMidActualPrimeEndpointDefect R *
      (vfMidOneBlockPrimeSeatCharge R +
        vfMidOneBlockProcessedSquarefreeCharge R)

/-- Demand terms that never enter an active off-diagonal first-owner cell:
identity-root gate, active diagonal, and squareful restoring packet. -/
def vfMidActiveDemandResidual (R : ℕ) : ℝ :=
  2 * vfMidActiveIdentityAnchorGate R +
    2 * vfMidActivePhysicalDiagonalMass R -
    2 * vfMidOneBlockProcessedSquarefulCharge R *
      (2 * vfMidActualPrimeEndpointDefect (R + 1) +
        vfMidOneBlockProcessedSquarefulCharge R)

/-- Capacity terms that never enter an active off-diagonal first-owner cell:
the absolute identity-root cross budget, active diagonal, and all products
involving an omitted current seat. -/
def vfMidActiveCapacityResidual (R : ℕ) : ℝ :=
  vfMidActualPrimeEndpointDefect R ^ 2 +
    2 * |vfMidActualPrimeEndpointDefect R| *
      vfMidOneBlockUpperActiveAbsMass R +
    vfMidActivePhysicalDiagonalMass R +
    vfMidWeightedOmittedSeatAbsMass R *
      (2 * (|vfMidActualPrimeEndpointDefect R| +
        vfMidOneBlockUpperActiveAbsMass R) +
        vfMidWeightedOmittedSeatAbsMass R)

/-- Global non-cell excess after the identity root and excluded physical seats
have been quarantined outside first-owner Fubini. -/
def vfMidActiveGlobalResidualExcess (R : ℕ) : ℝ :=
  vfMidActiveDemandResidual R - vfMidActiveCapacityResidual R

/-- Exact demand decomposition with the identity root completely outside
first-owner Fubini. -/
theorem vfMid_globalDemand_eq_activeResidual_add_cells
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidActualPrimeEndpointDefect (R + 1) ^ 2 =
      vfMidActiveDemandResidual R +
        ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            vfMidActiveWeightedCellDemand R p sig := by
  have hsource :=
    vfMidFirstBadNormalizedProduct_eq_upperActive_sub_squarefulRestoring hR
  rw [vfMidFirstBadNormalizedProduct_eq_nextEndpointDefect_sq hR] at hsource
  have hfubini :=
    vfMidWeightedSiteSquare_eq_diagonal_add_firstOwnerCells
      (R + 1) (vfMidOneBlockActivePhysicalSite R)
  rw [vfMidOneBlockActivePhysicalSite_sum_eq_activeSource (R := R)] at hfubini
  have hcells :
      (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
          vfMidActiveWeightedCellDemand R p sig) =
        2 * ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            2 * lowOwnerFirstOwnerCellGramWith (R + 1) p sig
              (vfMidOneBlockActivePhysicalSite R) := by
    simp only [vfMidActiveWeightedCellDemand, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    apply Finset.sum_congr rfl
    intro sig _hsig
    ring
  rw [hcells]
  unfold vfMidActiveDemandResidual vfMidActiveIdentityAnchorGate
    vfMidActivePhysicalDiagonalMass vfMidUpperFirstBadSourceBill
  nlinarith only [hsource, hfubini]

/-- Exact unchanged `T_R` denominator decomposition with the identity root and
omitted seats outside the active first-owner cells. -/
theorem vfMid_globalCapacity_eq_activeResidual_add_cells
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadZeroTargetTotalMass R =
      vfMidActiveCapacityResidual R +
        ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            vfMidActiveWeightedCellCapacity R p sig := by
  have hfubini :=
    vfMidWeightedSiteSquare_eq_diagonal_add_firstOwnerCells
      (R + 1) (fun n => |vfMidOneBlockActivePhysicalSite R n|)
  rw [vfMidOneBlockActivePhysicalSite_absSum_eq R,
    vfMidWeightedDiagonal_abs_eq
      (R + 1) (vfMidOneBlockActivePhysicalSite R)] at hfubini
  have htotal := vfMidFirstBadZeroTargetTotalMass_eq R
  rw [vfMidOddSeatAbsMass_eq_active_add_omitted hR] at htotal
  have hcells :
      (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
          vfMidActiveWeightedCellCapacity R p sig) =
        ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            2 * lowOwnerFirstOwnerCellGramWith (R + 1) p sig
              (fun n => |vfMidOneBlockActivePhysicalSite R n|) := by
    rfl
  rw [hcells]
  unfold vfMidActiveCapacityResidual vfMidActivePhysicalDiagonalMass
  nlinarith only [htotal, hfubini]

/-- **Exact global active excess ledger.**

The complete first-bad excess is the non-cell root/exclusion residual plus the
sum of pure active squarefree first-owner cell excesses.  No identity or
squareful seat is assigned a first owner. -/
theorem vfMidFirstBadCoDivExcess_eq_activeResidual_add_weightedCells
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidActualPrimeEndpointDefect (R + 1) ^ 2 -
        vfMidFirstBadZeroTargetTotalMass R =
      vfMidActiveGlobalResidualExcess R +
        ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            vfMidActiveWeightedCellExcess R p sig := by
  rw [vfMid_globalDemand_eq_activeResidual_add_cells hR,
    vfMid_globalCapacity_eq_activeResidual_add_cells hR]
  unfold vfMidActiveGlobalResidualExcess
    vfMidActiveWeightedCellExcess
  rw [← Finset.sum_sub_distrib]
  apply congrArg
    (fun x : ℝ =>
      vfMidActiveDemandResidual R - vfMidActiveCapacityResidual R + x)
  apply Finset.sum_congr rfl
  intro p _hp
  rw [← Finset.sum_sub_distrib]

/-- Omitted-seat capacity correction is always cooling: it enters the global
excess with a nonpositive sign. -/
theorem vfMidOmittedSeatCapacityCooling_nonpos
    (R : ℕ) :
    -(vfMidWeightedOmittedSeatAbsMass R *
      (2 * (|vfMidActualPrimeEndpointDefect R| +
        vfMidOneBlockUpperActiveAbsMass R) +
        vfMidWeightedOmittedSeatAbsMass R)) ≤ 0 := by
  have hO : 0 ≤ vfMidWeightedOmittedSeatAbsMass R := by
    unfold vfMidWeightedOmittedSeatAbsMass
    positivity
  have hM : 0 ≤ vfMidOneBlockUpperActiveAbsMass R :=
    vfMidOneBlockUpperActiveAbsMass_nonneg R
  have hfactor :
      0 ≤ 2 * (|vfMidActualPrimeEndpointDefect R| +
        vfMidOneBlockUpperActiveAbsMass R) +
        vfMidWeightedOmittedSeatAbsMass R := by
    positivity
  nlinarith only [mul_nonneg hO hfactor]

/-- On the upper endpoint-sign branch, the squareful restoring packet is also
cooling. -/
theorem vfMidSquarefulRestoringCooling_nonpos
    {R : ℕ} (hR : 2 ≤ R)
    (hupper : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1)) :
    -(2 * vfMidOneBlockProcessedSquarefulCharge R *
      (2 * vfMidActualPrimeEndpointDefect (R + 1) +
        vfMidOneBlockProcessedSquarefulCharge R)) ≤ 0 := by
  have hQ :
      0 ≤ vfMidOneBlockProcessedSquarefulCharge R :=
    vfMidOneBlockProcessedSquarefulCharge_nonneg R hR
  have hfactor :
      0 ≤ 2 * vfMidActualPrimeEndpointDefect (R + 1) +
        vfMidOneBlockProcessedSquarefulCharge R := by
    nlinarith
  nlinarith only [mul_nonneg hQ hfactor]

end RHLean.Analysis
