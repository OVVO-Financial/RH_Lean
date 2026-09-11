import Mathlib
import RHLean.Proof.SquareRootLowPrimeCombinedTaggedElevenPushforward
import RHLean.Proof.LowWheelCanonicalRepeatedFrozenCofactorMate

/-!
# Source-side normal form of the old physical residual

This file is structural.  It takes no norm and introduces no estimate.
It rewrites the opaque far set-difference residual in the source/partner
coordinates already used by the saturated second-contact and RoughPrefix
machinery.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open FrozenCofactorTopBottom

attribute [local instance] Classical.propDecidable

/-- The one-shot product-one mate used by the RoughPrefix source-scale
cancellation and the frozen top image used in the old residual are different
physical images of the same frozen source ledger, hence have exactly the same
signed mass. -/
theorem lowWheelCanonicalRepeatedFrozenProductOneMateLedger_eq_topImageLedger
    (R : ℕ) :
    lowWheelCanonicalRepeatedFrozenProductOneMateLedger R =
      lowWheelFrozenCofactorTopImageLedger R := by
  have hprod :=
    sum_lowWheelCanonicalRepeatedFrozenCofactor_add_productOneMate_eq_zero R
  have htop := lowWheelFrozenCofactorTopImageLedger_eq_neg R
  change lowWheelCanonicalFrozenCofactorLedger R +
      lowWheelCanonicalRepeatedFrozenProductOneMateLedger R = 0 at hprod
  linear_combination hprod - htop

/-- **Exact source-side normal form of the old hard physical residual.**
After the full far Othello cancellation, the residual is one stable far packet
plus the source-side frozen-cofactor and internal-terminal ledgers, together
with the literal at-most-seven near internal mate strip.  No term is bounded or
dropped. -/
theorem lowWheelFrozenTopFarPhysicalResidualLedger_eq_sourceNormalForm
    {R : ℕ} (hR : 6 ≤ R) :
    lowWheelFrozenTopFarPhysicalResidualLedger R =
      (∑ z ∈ lowWheelFarTaggedPhysicalStableCarrier R,
        lowWheelFullTaggedPhysicalWeight z) +
      lowWheelCanonicalFrozenCofactorLedger R +
      lowWheelCanonicalRepeatedTerminalInternalLedger R +
      lowWheelCanonicalRepeatedTerminalInternalMateNearLedger R := by
  have hfar := lowWheelFarTaggedPhysicalLedger_eq_residual_add_farMate_add_top R hR
  have hstable := lowWheelFarTaggedPhysicalLedger_eq_stable R
  have hsplit := lowWheelCanonicalRepeatedTerminalInternalMateLedger_eq_near_add_far R
  have hinter := lowWheelCanonicalRepeatedTerminalInternalLedger_eq_neg_mateLedger R
  have htop := lowWheelFrozenCofactorTopImageLedger_eq_neg R
  linear_combination -hfar + hstable + hsplit - htop - hinter

/-- The same normal form with the frozen top image written as the historical
product-one mate used by RoughPrefix.  This makes the sign comparison explicit:
the old residual contains the *negative* of that mate ledger. -/
theorem lowWheelFrozenTopFarPhysicalResidualLedger_eq_stable_sub_mates
    {R : ℕ} (hR : 6 ≤ R) :
    lowWheelFrozenTopFarPhysicalResidualLedger R =
      (∑ z ∈ lowWheelFarTaggedPhysicalStableCarrier R,
        lowWheelFullTaggedPhysicalWeight z) -
      lowWheelCanonicalRepeatedTerminalInternalMateFarLedger R -
      lowWheelCanonicalRepeatedFrozenProductOneMateLedger R := by
  have hfar := lowWheelFarTaggedPhysicalLedger_eq_residual_add_farMate_add_top R hR
  have hstable := lowWheelFarTaggedPhysicalLedger_eq_stable R
  have htop :=
    lowWheelCanonicalRepeatedFrozenProductOneMateLedger_eq_topImageLedger R
  linear_combination -hfar + hstable + htop

/-- Combined #643/#645 interior in the source-side normal form.  The full-face
Go source remains signed together with the old source sectors; no boundary or
energy interpretation is inserted. -/
theorem oldResidual_add_fullFaceDefect_eq_sourceNormalForm_add_defect
    {R : ℕ} (hR : 6 ≤ R) :
    lowWheelFrozenTopFarPhysicalResidualLedger R +
        ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ) =
      (∑ z ∈ lowWheelFarTaggedPhysicalStableCarrier R,
        lowWheelFullTaggedPhysicalWeight z) +
      lowWheelCanonicalFrozenCofactorLedger R +
      lowWheelCanonicalRepeatedTerminalInternalLedger R +
      lowWheelCanonicalRepeatedTerminalInternalMateNearLedger R +
      ((squareRootLowPrimeGoFullFaceDefectSourceMass R : ℤ) : ℂ) := by
  rw [lowWheelFrozenTopFarPhysicalResidualLedger_eq_sourceNormalForm hR]
  ring

end RHLean.Proof
