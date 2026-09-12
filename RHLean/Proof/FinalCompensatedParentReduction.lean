import RHLean.Proof.LowWheelFrozenSquareResidualTransportClosure
import RHLean.Proof.LowWheelCanonicalFrozenReduction
import RHLean.Proof.StableFarWallCrossingRenewal
import RHLean.Proof.ExceptionalTransportCoboundary
import RHLean.Analysis.PhysicalDaughterEnergyObstructions
import RHLean.Analysis.SquareRootMatchedDegreeOneRecovery

/-!
# Final compensated parent reduction after the q^2 parent reassembly

This module performs no estimate.  It combines the merged q^2 source/transport
reassembly with the pre-existing canonical frozen/far reduction on one common
signed endpoint.

The point is to identify the exact object on which any final contraction must
act.  After the second-contact square residual is reassembled, define the
remaining parent core by removing only the algebraic endpoint rest from the
smooth side.  The endpoint identity says that this core is the full square
Mertens sample plus the complete signed q^2 residual.  The canonical frozen
reduction says that the full square Mertens sample plus the frozen/top/far
residual is only a root-scale boundary.  Therefore

  core + frozenTopFar = q2Residual + rootBoundary.

Equivalently, the genuinely hard signed comparison is the q^2 low-side packet
against the frozen/top/far high-side packet.  No selected-prime field is
substituted for Mobius, and no norm is taken before this reassembly.
-/

open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Parent-side core after removing the exact second-contact endpoint rest, but
before subtracting the signed q^2 square residual. -/
def finalCompensatedParentCore (R : ℕ) : ℂ :=
  squareRootSmoothMass (R - 1) - lowWheelFrozenSecondContactEndpointRest R

/-- The four already-root-scale terms left by the canonical frozen reduction. -/
def finalCompensatedRootBoundary (R : ℕ) : ℂ :=
  mertensSummatory R -
    lowWheelCanonicalDowncrossUniqueParentLedger R -
    squareRootNearPrimeTransport R + squareRootERuniq R

/-- The exact low/high signed comparison exposed by the two independent
reassemblies. -/
def finalCompensatedLowHighDifference (R : ℕ) : ℂ :=
  lowWheelFrozenSecondContactSquareResidualMass R -
    lowWheelFrozenTopFarResidual R

/-- The second-contact endpoint theorem says that the parent core is exactly the
square Mertens sample plus the whole signed q^2 residual. -/
theorem finalCompensatedParentCore_eq_squarePrefix_add_q2Residual
    (R : ℕ) (hR : 3 ≤ R) :
    finalCompensatedParentCore R =
      squarePrefixMertens (R - 1) +
        lowWheelFrozenSecondContactSquareResidualMass R := by
  have h :=
    squarePrefixMertens_eq_smooth_sub_secondContactEndpointRest_add_residual R hR
  unfold finalCompensatedParentCore
  calc
    squareRootSmoothMass (R - 1) - lowWheelFrozenSecondContactEndpointRest R =
        (squareRootSmoothMass (R - 1) -
          (lowWheelFrozenSecondContactEndpointRest R +
            lowWheelFrozenSecondContactSquareResidualMass R)) +
          lowWheelFrozenSecondContactSquareResidualMass R := by ring
    _ = squarePrefixMertens (R - 1) +
          lowWheelFrozenSecondContactSquareResidualMass R := by rw [← h]

/-- Independently, the square Mertens sample plus the frozen/top/far residual is
exactly the pre-existing root-scale boundary. -/
theorem squarePrefixMertens_add_frozenTopFar_eq_finalRootBoundary
    (R : ℕ) (hR : 56 ≤ R) :
    squarePrefixMertens (R - 1) + lowWheelFrozenTopFarResidual R =
      finalCompensatedRootBoundary R := by
  rw [squarePrefixMertens_eq_mertens_sub_canonicalDefect R (by omega),
    lowWheelCanonicalDefectLedger_eq_frozenTopFarResidual_add_rootTerms R hR]
  unfold finalCompensatedRootBoundary
  ring

/-- **Exact final low/high coupling.**  After all q^2 source-scale, owner,
root-floor, root-anchor, and historical matching-transport bookkeeping is
removed, the compensated parent core plus the hard far residual is the q^2
low-side residual plus only the root-scale boundary. -/
theorem finalCompensatedParentCore_add_frozenTopFar_eq_q2Residual_add_rootBoundary
    (R : ℕ) (hR : 56 ≤ R) :
    finalCompensatedParentCore R + lowWheelFrozenTopFarResidual R =
      lowWheelFrozenSecondContactSquareResidualMass R +
        finalCompensatedRootBoundary R := by
  have hcore :=
    finalCompensatedParentCore_eq_squarePrefix_add_q2Residual R (by omega)
  have hfar :=
    squarePrefixMertens_add_frozenTopFar_eq_finalRootBoundary R hR
  linear_combination hcore + hfar

/-- Equivalent normal form: the compensated parent core is the signed low/high
difference plus the root-scale boundary. -/
theorem finalCompensatedParentCore_eq_lowHighDifference_add_rootBoundary
    (R : ℕ) (hR : 56 ≤ R) :
    finalCompensatedParentCore R =
      finalCompensatedLowHighDifference R + finalCompensatedRootBoundary R := by
  have h :=
    finalCompensatedParentCore_add_frozenTopFar_eq_q2Residual_add_rootBoundary R hR
  unfold finalCompensatedLowHighDifference
  linear_combination h

/-- The root boundary in the final normal form already has linear amplitude at
square-root scale.  This is the same `10 R` estimate used by the recovered
matched-transport endpoint; no new triangle inequality is introduced here. -/
theorem norm_finalCompensatedRootBoundary_le_ten_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖finalCompensatedRootBoundary R‖ ≤ 10 * (R : ℝ) := by
  have h := norm_squareRootRecoveredMatchedTransport_add_frozenTopFar_le_ten_root
    R hR
  rw [squareRootMatched_sub_positivePrimeTransform_eq_squarePrefixMertens
      R (by omega),
    squarePrefixMertens_add_frozenTopFar_eq_finalRootBoundary R hR] at h
  exact h

/-- The original square Mertens sample itself is the root boundary minus the
frozen/top/far residual.  This records explicitly why the far packet may not be
silently put into the boundary: it carries the full non-root-scale endpoint. -/
theorem squarePrefixMertens_eq_rootBoundary_sub_frozenTopFar
    (R : ℕ) (hR : 56 ≤ R) :
    squarePrefixMertens (R - 1) =
      finalCompensatedRootBoundary R - lowWheelFrozenTopFarResidual R := by
  have h := squarePrefixMertens_add_frozenTopFar_eq_finalRootBoundary R hR
  linear_combination h

/-! ## Post-#673 exact splice onto whole q^2 Mertens daughters -/

/-- The complete square-endpoint Go q^2 column over all old prime owners. -/
def squareEndpointQ2GoColumn (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1),
    squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R)

/-- The same owner schedule after high-prime transport is retained.  Each
summand is the genuine lower-scale Mertens packet. -/
def squareEndpointQ2MertensColumn (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1),
    mertensSummatoryInt (squareRootEndpoint R / (q * q))

/-- Signed transport amount separating the frozen Go column from the whole
Mertens daughter column. -/
def squareEndpointQ2HighTransportDefect (R : ℕ) : ℤ :=
  squareEndpointQ2GoColumn R - squareEndpointQ2MertensColumn R

/-- The prime coboundary identity in `ExceptionalTransportCoboundary` extends
to every prime and every cutoff.  Below the owner the high-prime set is empty
and the frozen predecessor is already the full Mertens prefix; above the owner
this is the existing proper-subwheel telescope. -/
theorem q2DaughterHighTransport_eq_go_sub_mertens_all
    {q X : ℕ} (hq : q.Prime) :
    q2DaughterHighTransport q X =
      squareRootLowPrimeGoWallSquareResidual q X -
        mertensSummatoryInt (X / (q * q)) := by
  by_cases hcut : q - 1 ≤ X / (q * q)
  · exact q2DaughterHighTransport_eq_go_sub_mertens hcut
  · have hYq : X / (q * q) < q := by omega
    have hempty :
        frozenPrimeUniverseHighPrimeSet (q - 1) (X / (q * q)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hdata := mem_frozenPrimeUniverseHighPrimeSet.mp hp
      omega
    unfold q2DaughterHighTransport
    rw [hempty, Finset.sum_empty,
      squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff,
      frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner hq hYq]
    ring

/-- The algebraic transport defect is therefore literally the sum of the actual
high-prime transport columns on the same owner schedule. -/
def squareEndpointQ2HighTransportColumn (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1),
    q2DaughterHighTransport q (squareRootEndpoint R)

theorem squareEndpointQ2HighTransportDefect_eq_actualColumn (R : ℕ) :
    squareEndpointQ2HighTransportDefect R =
      squareEndpointQ2HighTransportColumn R := by
  unfold squareEndpointQ2HighTransportDefect squareEndpointQ2GoColumn
    squareEndpointQ2MertensColumn squareEndpointQ2HighTransportColumn
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  exact (q2DaughterHighTransport_eq_go_sub_mertens_all
    (mem_primesUpTo.mp hq).1).symm

/-- Root-anchor compensation already present in the saturated source together
with its actual historical matching fixed-transport population. -/
def finalQ2RootReassemblyBoundary (R : ℕ) : ℂ :=
  ((RHLean.Analysis.goCompensatedRootBoundary R : ℤ) : ℂ) +
    lowWheelFrozenSecondContactMatchingFixedTransportMass R

/-- The root reassembly boundary has no hidden full-scale smooth term: the
common frozen root cube and empty Euler face cancel exactly, leaving the old
root-anchor column minus the already-named root-floor correction. -/
theorem finalQ2RootReassemblyBoundary_eq_anchor_sub_rootFloorCorrection
    (R : ℕ) (hR : 2 ≤ R) :
    finalQ2RootReassemblyBoundary R =
      (((lowWheelFrozenSquareResidualRootAnchorColumn R -
        RHLean.Analysis.goRootFloorCorrection R : ℤ) : ℂ)) := by
  have hmatch :=
    lowWheelFrozenSecondContactMatchingFixedTransportMass_eq_smooth_add_anchor_sub_one
      R hR
  unfold finalQ2RootReassemblyBoundary RHLean.Analysis.goCompensatedRootBoundary
  rw [hmatch]
  push_cast
  ring

/-- The complete low-side square residual is the compensated root boundary minus
all literal Go q^2 daughters.  No norm is taken. -/
theorem lowWheelFrozenSecondContactSquareResidualMass_eq_rootReassembly_sub_goColumn
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelFrozenSecondContactSquareResidualMass R =
      finalQ2RootReassemblyBoundary R -
        ((squareEndpointQ2GoColumn R : ℤ) : ℂ) := by
  have hsource :=
    RHLean.Analysis.lowWheelFrozenSecondContactSource_sum_eq_compensatedRootBoundary_sub_allDaughters
      R hR
  have hsource' :
      (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
          lowWheelTaggedDowncrossWeight y) =
        (((RHLean.Analysis.goCompensatedRootBoundary R -
          squareEndpointQ2GoColumn R : ℤ) : ℂ)) := by
    simpa [lowWheelTaggedDowncrossWeight, squareEndpointQ2GoColumn] using hsource
  have hcomp :=
    lowWheelFrozenSecondContactSource_add_matchingFixedTransport_eq_squareResidual R
  rw [hsource'] at hcomp
  unfold finalQ2RootReassemblyBoundary
  push_cast at hcomp ⊢
  calc
    lowWheelFrozenSecondContactSquareResidualMass R =
        ((RHLean.Analysis.goCompensatedRootBoundary R : ℤ) : ℂ) -
          ((squareEndpointQ2GoColumn R : ℤ) : ℂ) +
          lowWheelFrozenSecondContactMatchingFixedTransportMass R := hcomp.symm
    _ = ((RHLean.Analysis.goCompensatedRootBoundary R : ℤ) : ℂ) +
          lowWheelFrozenSecondContactMatchingFixedTransportMass R -
          ((squareEndpointQ2GoColumn R : ℤ) : ℂ) := by ring

/-- Inserting `Go = M + highTransport` exposes the whole lower-scale Mertens
column while the actual transport correction remains signed. -/
theorem lowWheelFrozenSecondContactSquareResidualMass_eq_neg_mertensColumn_add_rootTransport
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelFrozenSecondContactSquareResidualMass R =
      -(((squareEndpointQ2MertensColumn R : ℤ) : ℂ)) +
        (finalQ2RootReassemblyBoundary R -
          ((squareEndpointQ2HighTransportColumn R : ℤ) : ℂ)) := by
  rw [lowWheelFrozenSecondContactSquareResidualMass_eq_rootReassembly_sub_goColumn R hR]
  rw [← squareEndpointQ2HighTransportDefect_eq_actualColumn R]
  unfold squareEndpointQ2HighTransportDefect
  push_cast
  ring

/-- Descended far-prime part already recognized by #671/#673. -/
def squareEndpointQ2ChildFarSliceColumn (R : ℕ) : ℂ :=
  ∑ q ∈ primesUpTo (R - 1),
    ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
      canonicalMoebiusWeight dp.1

/-- Strict-crossing survivors after forgetting only their stripped owner tag.
The crossing carrier remains the index, so multiplicity is retained exactly. -/
def stableFarRenewalColumn (R : ℕ) : ℂ :=
  ∑ x ∈ lowWheelFarPrimeCrossingProductCarrier R,
    lowWheelFullTaggedPhysicalWeight
      (lowWheelFarPrimeCrossingStableState x)

/-- Unit-face and the two already-owned terminal populations in the common true
Möbius product currency. -/
def stableFarTerminalProductColumn (R : ℕ) : ℂ :=
  ∑ n ∈ lowWheelFarWallTerminalProducts R,
    canonicalMoebiusWeight n

/-- Everything left after the whole q^2 Mertens daughter column is pulled out of
the exact low/high comparison.  The child-far slice stays signed together with
the literal high-prime transport column. -/
def finalQ2SurvivorCorrection (R : ℕ) : ℂ :=
  finalQ2RootReassemblyBoundary R -
      ((squareEndpointQ2HighTransportColumn R : ℤ) : ℂ) +
    squareEndpointQ2ChildFarSliceColumn R +
    stableFarRenewalColumn R +
    stableFarTerminalProductColumn R

/-- **Exact post-#673 low/high splice.**  The hard compensated low/high
comparison is a column of genuine lower-scale Mertens daughters plus one
explicit signed survivor correction. -/
theorem finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_survivor
    (R : ℕ) (hR : 56 ≤ R) :
    finalCompensatedLowHighDifference R =
      -(((squareEndpointQ2MertensColumn R : ℤ) : ℂ)) +
        finalQ2SurvivorCorrection R := by
  have hlow :=
    lowWheelFrozenSecondContactSquareResidualMass_eq_neg_mertensColumn_add_rootTransport
      R (by omega)
  have hfar :=
    lowWheelFrozenTopFarResidual_eq_neg_childFarSlices_sub_stableRenewal_sub_terminal
      R hR
  unfold finalCompensatedLowHighDifference
  rw [hlow, hfar]
  unfold finalQ2SurvivorCorrection squareEndpointQ2ChildFarSliceColumn
    stableFarRenewalColumn stableFarTerminalProductColumn
  ring

/-- Substitution into the exact final parent normal form.  The only non-root
term not displayed as a whole recursive Mertens daughter is now the explicit
survivor correction. -/
theorem finalCompensatedParentCore_eq_neg_mertensColumn_add_survivor_add_rootBoundary
    (R : ℕ) (hR : 56 ≤ R) :
    finalCompensatedParentCore R =
      -(((squareEndpointQ2MertensColumn R : ℤ) : ℂ)) +
        finalQ2SurvivorCorrection R + finalCompensatedRootBoundary R := by
  rw [finalCompensatedParentCore_eq_lowHighDifference_add_rootBoundary R hR,
    finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_survivor R hR]

end RHLean.Proof
