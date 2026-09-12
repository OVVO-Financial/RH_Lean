import RHLean.Proof.LowWheelFrozenSquareResidualTransportClosure
import RHLean.Proof.LowWheelCanonicalFrozenReduction
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

end RHLean.Proof
