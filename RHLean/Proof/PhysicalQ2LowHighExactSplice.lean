import RHLean.Proof.FinalCompensatedParentReduction
import RHLean.Proof.StableFarWallCrossingRenewal
import RHLean.Analysis.PhysicalDaughterEnergyObstructions

/-!
# Exact low/high splice onto whole q^2 Mertens daughters

This module performs the post-#672/#673 substitution before any norm is taken.
The low-side saturated second-contact source is first rewritten as the globally
compensated root boundary minus every literal Go q^2 daughter.  The stable-far
side is then rewritten using #673 as the descended child-far slices plus the
literal stable-wall renewal occurrences and the terminal product carrier.

The key point is to insert the full signed daughter

  M(X_R/q^2) = Go_q(X_R) - highTransport_q(X_R)

only after those two physical reassemblies have been made.  The resulting
identity isolates a column of genuine lower-scale Mertens packets and leaves one
explicit signed survivor correction.  No coefficient L2 mass is identified with
Mertens energy and no absolute value is taken here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The complete square-endpoint Go q^2 column over all old prime owners. -/
def squareEndpointQ2GoColumn (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1),
    squareRootLowPrimeGoWallSquareResidual q (squareRootEndpoint R)

/-- The same owner schedule after the high-prime transport has been retained:
each summand is the genuine lower-scale Mertens packet. -/
def squareEndpointQ2MertensColumn (R : ℕ) : ℤ :=
  ∑ q ∈ primesUpTo (R - 1),
    mertensSummatoryInt (squareRootEndpoint R / (q * q))

/-- Signed amount which must be attached to the frozen Go column to recover the
whole Mertens daughter column.  This is defined as one signed difference, so no
ownerwise norm is introduced. -/
def squareEndpointQ2HighTransportDefect (R : ℕ) : ℤ :=
  squareEndpointQ2GoColumn R - squareEndpointQ2MertensColumn R

/-- The root-anchor compensation already present in the saturated source,
together with its actual historical matching fixed-transport population. -/
def finalQ2RootReassemblyBoundary (R : ℕ) : ℂ :=
  ((RHLean.Analysis.goCompensatedRootBoundary R : ℤ) : ℂ) +
    lowWheelFrozenSecondContactMatchingFixedTransportMass R

/-- The entire low-side square residual is the compensated root boundary minus
all literal Go q^2 daughters.  This is just the two existing signed identities
spliced together. -/
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
  linear_combination hcomp

/-- Algebraically inserting `Go = M + highTransportDefect` exposes the whole
lower-scale Mertens column while keeping the transport correction signed. -/
theorem lowWheelFrozenSecondContactSquareResidualMass_eq_neg_mertensColumn_add_rootTransport
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelFrozenSecondContactSquareResidualMass R =
      -(((squareEndpointQ2MertensColumn R : ℤ) : ℂ)) +
        (finalQ2RootReassemblyBoundary R -
          ((squareEndpointQ2HighTransportDefect R : ℤ) : ℂ)) := by
  rw [lowWheelFrozenSecondContactSquareResidualMass_eq_rootReassembly_sub_goColumn R hR]
  unfold squareEndpointQ2HighTransportDefect
  push_cast
  ring

/-- The descended far-prime part already recognized by #671/#673, written as a
single named signed column. -/
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

/-- Everything left after the whole q^2 Mertens daughter column has been pulled
out of the exact low/high comparison.  This is a signed object; in particular
the far child slice is not normed separately from the high-transport defect. -/
def finalQ2SurvivorCorrection (R : ℕ) : ℂ :=
  finalQ2RootReassemblyBoundary R -
      ((squareEndpointQ2HighTransportDefect R : ℤ) : ℂ) +
    squareEndpointQ2ChildFarSliceColumn R +
    stableFarRenewalColumn R +
    stableFarTerminalProductColumn R

/-- **Exact post-#673 low/high splice.**  The hard compensated low/high
comparison is one column of genuine lower-scale Mertens daughters, with sign
`-1`, plus the explicit survivor correction.  Every equality used to reach
this statement is signed and finite. -/
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

/-- Substitution into the exact final parent normal form.  At this point the
only non-root term not already displayed as a whole recursive Mertens daughter
is `finalQ2SurvivorCorrection`. -/
theorem finalCompensatedParentCore_eq_neg_mertensColumn_add_survivor_add_rootBoundary
    (R : ℕ) (hR : 56 ≤ R) :
    finalCompensatedParentCore R =
      -(((squareEndpointQ2MertensColumn R : ℤ) : ℂ)) +
        finalQ2SurvivorCorrection R + finalCompensatedRootBoundary R := by
  rw [finalCompensatedParentCore_eq_lowHighDifference_add_rootBoundary R hR,
    finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_survivor R hR]
  ring

/-- The extracted daughter column still has the intact predecessor/high-
transport meaning owner by owner.  This records criterion #660.2 without
replacing any physical packet by a coefficient norm. -/
theorem squareEndpointQ2MertensColumn_eq_signedPredecessorColumn (R : ℕ) :
    squareEndpointQ2MertensColumn R =
      ∑ q ∈ primesUpTo (R - 1),
        exceptionalSignedPredecessorState q
          (squareRootEndpoint R / (q * q)) := by
  unfold squareEndpointQ2MertensColumn
  apply Finset.sum_congr rfl
  intro q hq
  exact (exceptionalSignedPredecessorState_eq_mertens
    (mem_primesUpTo.mp hq).1 _).symm

end RHLean.Proof
