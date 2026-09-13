import Mathlib
import RHLean.Proof.PostRootPartnerEulerMemory
import RHLean.Proof.CanonicalRoughTruncatedWheelManyPrimeTelescope
import RHLean.Proof.CanonicalRoughColumnAbelBridge
import RHLean.Analysis.SquareRootMatchedTransport
import RHLean.Proof.StableFarWallUnitRenewalCentering
import RHLean.Proof.PhysicalQ2ExceptionalTerminalSynthesis
import RHLean.Proof.PostRootPartnerMellinInterpolation
import RHLean.Proof.LogSquareCorrectionQ2Tower

/-!
# Exact Euler-hazard alignment of the post-root partner ledger

This module keeps the post-#685 chronology signed until the physical/canonical
first-power column has been identified.  No norm is taken in the splice layer.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-! ## Scalar Euler-hazard mass -/

def postRootEulerHazardMass : List ℕ → ℝ
  | [] => 0
  | p :: ps =>
      canonicalRoughEulerFactor p * postRootEulerHazardMass ps +
        1 / (p : ℝ)

@[simp] theorem postRootEulerHazardMass_nil :
    postRootEulerHazardMass [] = 0 := by
  rfl

@[simp] theorem postRootEulerHazardMass_cons (p : ℕ) (ps : List ℕ) :
    postRootEulerHazardMass (p :: ps) =
      canonicalRoughEulerFactor p * postRootEulerHazardMass ps +
        1 / (p : ℝ) := by
  rfl

theorem postRootEulerHazardMass_eq_one_sub_eulerProduct (ps : List ℕ) :
    postRootEulerHazardMass ps =
      1 - canonicalRoughPrimeListEulerProduct ps := by
  induction ps with
  | nil =>
      simp [postRootEulerHazardMass, canonicalRoughPrimeListEulerProduct]
  | cons p ps ih =>
      simp only [postRootEulerHazardMass_cons,
        canonicalRoughPrimeListEulerProduct_cons]
      rw [ih]
      unfold canonicalRoughEulerFactor
      ring

/-! ## Boundary-valued Euler-hazard ledger -/

def postRootEulerHazardLedger (boundary : ℕ → ℂ) : List ℕ → ℂ
  | [] => 0
  | p :: ps =>
      (canonicalRoughEulerFactor p : ℂ) *
          postRootEulerHazardLedger boundary ps +
        boundary p / (p : ℂ)

@[simp] theorem postRootEulerHazardLedger_nil (boundary : ℕ → ℂ) :
    postRootEulerHazardLedger boundary [] = 0 := by
  rfl

@[simp] theorem postRootEulerHazardLedger_cons
    (boundary : ℕ → ℂ) (p : ℕ) (ps : List ℕ) :
    postRootEulerHazardLedger boundary (p :: ps) =
      (canonicalRoughEulerFactor p : ℂ) *
          postRootEulerHazardLedger boundary ps +
        boundary p / (p : ℂ) := by
  rfl

theorem postRootEulerHazardLedger_append
    (boundary : ℕ → ℂ) (pre post : List ℕ) :
    postRootEulerHazardLedger boundary (pre ++ post) =
      (canonicalRoughPrimeListEulerProduct pre : ℂ) *
          postRootEulerHazardLedger boundary post +
        postRootEulerHazardLedger boundary pre := by
  induction pre with
  | nil =>
      simp [postRootEulerHazardLedger, canonicalRoughPrimeListEulerProduct]
  | cons p pre ih =>
      simp only [List.cons_append, postRootEulerHazardLedger_cons,
        canonicalRoughPrimeListEulerProduct_cons]
      rw [ih]
      push_cast
      ring

/-! ## Literal connection to the #540 physical defect ledger -/

def squareRootCanonicalRoughPhysicalStepBoundaryCharge
    (R : ℕ) (step : CanonicalRoughPhysicalEulerStep) : ℂ :=
  (step.1 : ℂ) * squareRootCanonicalRoughPhysicalStepDefect R step

def squareRootCanonicalRoughTransportedBoundaryChargeLedger
    (R : ℕ) : List CanonicalRoughPhysicalEulerStep → ℂ
  | [] => 0
  | step :: steps =>
      (canonicalRoughEulerFactor step.1 : ℂ) *
          squareRootCanonicalRoughTransportedBoundaryChargeLedger R steps +
        squareRootCanonicalRoughPhysicalStepBoundaryCharge R step /
          (step.1 : ℂ)

theorem squareRootCanonicalRoughTransportedBoundaryChargeLedger_eq_defectLedger
    (R : ℕ) (steps : List CanonicalRoughPhysicalEulerStep)
    (hprime : ∀ step ∈ steps, step.1.Prime) :
    squareRootCanonicalRoughTransportedBoundaryChargeLedger R steps =
      squareRootCanonicalRoughTransportedDefectLedger R steps := by
  induction steps with
  | nil =>
      rfl
  | cons step steps ih =>
      have hp : step.1.Prime := hprime step (by simp)
      have htail : ∀ s ∈ steps, s.1.Prime := by
        intro s hs
        exact hprime s (by simp [hs])
      have hp0 : (step.1 : ℂ) ≠ 0 := by
        exact_mod_cast hp.ne_zero
      have hscale :
          squareRootCanonicalRoughPhysicalStepBoundaryCharge R step /
              (step.1 : ℂ) =
            squareRootCanonicalRoughPhysicalStepDefect R step := by
        unfold squareRootCanonicalRoughPhysicalStepBoundaryCharge
        field_simp [hp0]
      simp only [squareRootCanonicalRoughTransportedBoundaryChargeLedger,
        squareRootCanonicalRoughTransportedDefectLedger]
      rw [ih htail, hscale]

/-- Canonical endpoint of the hazard-coordinate splice. -/
theorem postRootCanonicalColumn_logAlignmentTarget (X K : ℕ) :
    (∑ q ∈ primesUpTo K,
      (primorialTruncatedSignedReciprocalCube (primesUpTo (q - 1)) (X / q) -
        primorialSignedContractionFactor (primesUpTo (q - 1)))) =
      primorialTruncatedWheelAbelPrimitive X K := by
  exact canonicalUnweightedColumn_eq_abelPrimitive X K

/-! ## FAR-4 splice: exact q² carrier first, energy second -/

/-- The centered q²-descended carrier obtained from the old stable-far census
after every nonunit strict crossing is sent to its unique next child. -/
def farFourQ2CenteredTower (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
    (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
      canonicalMoebiusWeight y.2.1

/-- The complementary terminal population in the old census.  It is kept only
as a signed bookkeeping object; it must not be normed separately. -/
def farFourTerminalRemainder (R : ℕ) : ℂ :=
  (∑ p ∈ lowWheelFarPrimeUnitProducts R,
      ((lowWheelFarPrimeQ2UnitCrossingMultiplicity R p : ℂ) - 1)) +
    ∑ n ∈ lowWheelFrozenTopFarOwnedProducts R,
      canonicalMoebiusWeight n

theorem lowWheelFarWallTerminalProducts_mass_eq_unit_add_owned (R : ℕ) :
    (∑ n ∈ lowWheelFarWallTerminalProducts R,
        canonicalMoebiusWeight n) =
      (∑ p ∈ lowWheelFarPrimeUnitProducts R,
        canonicalMoebiusWeight p) +
      ∑ n ∈ lowWheelFrozenTopFarOwnedProducts R,
        canonicalMoebiusWeight n := by
  unfold lowWheelFarWallTerminalProducts
  rw [Finset.sum_union (lowWheelFarPrimeUnitProducts_disjoint_owned R)]

/-- Exact old-census normal form, before any norm.  This theorem is retained to
make the cancellation requirement visible; the two displayed terms are not
separate errors. -/
theorem lowWheelFrozenTopFarResidual_eq_neg_q2CenteredTower_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      -farFourQ2CenteredTower R - farFourTerminalRemainder R := by
  have hfar :=
    lowWheelFrozenTopFarResidual_eq_neg_childFarSlices_sub_stableRenewal_sub_terminal
      R hR
  have hcenter :=
    lowWheelFarPrimeChildFar_add_crossingRenewal_add_unitTerminal_eq_centered R
  have hterminal := lowWheelFarWallTerminalProducts_mass_eq_unit_add_owned R
  unfold farFourQ2CenteredTower farFourTerminalRemainder
  rw [hterminal] at hfar
  rw [hfar]
  linear_combination -hcenter

/-- Literal factor-four FAR splice with the root-envelope constant exposed. -/
def FarFourSplice (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
      4 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
        rawQ2ChildEnergyReal R q +
      C * (R : ℝ) ^ 2 * K

/-- The named splice is definitionally the body of the pre-existing FAR-4
terminal criterion. -/
theorem frozenTopFarFourEnergy_iff_exists_nonneg_farFourSplice :
    FrozenTopFarFourEnergyStatement ↔
      ∃ C : ℝ, 0 ≤ C ∧ FarFourSplice C := by
  rfl

/-! ## Corrected post-diagnostic transport/far seam -/

/-- The exact signed mismatch between the q² daughter high-transport column and
the stable-far destination census.  The diagnostic after #685 shows that this
quantity is not identically zero; it is therefore kept as the genuine next
signed seam rather than hidden in a false support equality. -/
def q2TransportFarMismatch (R : ℕ) : ℂ :=
  (((squareEndpointQ2HighTransportColumn R : ℤ) : ℂ)) +
    lowWheelFrozenTopFarResidual R

/-- Equivalent source/destination form of the mismatch.  The three routed far
populations are exactly the negative frozen/top/far residual, so the mismatch
is `HighTransport - (ChildFar + Renewal + Terminal)`. -/
theorem q2TransportFarMismatch_eq_highTransport_sub_farPopulations
    (R : ℕ) (hR : 56 ≤ R) :
    q2TransportFarMismatch R =
      (((squareEndpointQ2HighTransportColumn R : ℤ) : ℂ)) -
        (squareEndpointQ2ChildFarSliceColumn R +
          stableFarRenewalColumn R + stableFarTerminalProductColumn R) := by
  have hfar := farPopulations_eq_neg_frozenTopFar R hR
  unfold q2TransportFarMismatch
  rw [hfar]
  ring

/-- **Exact corrected survivor seam.**  No cancellation is assumed: the #674
survivor is the root reassembly boundary minus the literal transport/far
mismatch. -/
theorem finalQ2SurvivorCorrection_eq_root_sub_q2TransportFarMismatch
    (R : ℕ) (hR : 56 ≤ R) :
    finalQ2SurvivorCorrection R =
      finalQ2RootReassemblyBoundary R - q2TransportFarMismatch R := by
  have hfar := farPopulations_eq_neg_frozenTopFar R hR
  unfold finalQ2SurvivorCorrection q2TransportFarMismatch
  rw [hfar]
  ring

/-- **Exact corrected low/high normal form.**  The genuine lower-scale q²
Mertens column is exposed, while the only remaining signed seam is the explicit
transport/far mismatch.  No norm or estimate enters this identity. -/
theorem finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_root_sub_mismatch
    (R : ℕ) (hR : 56 ≤ R) :
    finalCompensatedLowHighDifference R =
      -(((squareEndpointQ2MertensColumn R : ℤ) : ℂ)) +
        (finalQ2RootReassemblyBoundary R - q2TransportFarMismatch R) := by
  rw [finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_survivor R hR,
    finalQ2SurvivorCorrection_eq_root_sub_q2TransportFarMismatch R hR]

/-- **Candidate signed q²-tower support statement.**

The exact integer diagnostic `scripts/far_four_diagnostic.py --q2-support`
refutes this candidate at `R = 56`: high transport is `8`, while the three
destination columns total `160 + 309 - 466 = 3`. This diagnostic has not been
formalized as a Lean certificate. The proposition is retained to name the
failed target; the implications below remain conditional algebra only.

The existing routing theorems classify the stable-far source, whose cofactor
cube is below `q` and whose original cutoff is `q*d*p <= X_R`. High transport
instead uses the predecessor cube below `p` at `q^2*d*p <= X_R`. LOG-MATCH
preserves the former carrier and does not identify these two sources. -/
def FarFourSignedQ2TowerSupport : Prop :=
  ∀ R : ℕ, 56 ≤ R →
    (((squareEndpointQ2HighTransportColumn R : ℤ) : ℂ)) =
      squareEndpointQ2ChildFarSliceColumn R +
        stableFarRenewalColumn R + stableFarTerminalProductColumn R

/-- The support statement is exactly the assertion that the #674 survivor is
only the root-scale reassembly boundary. -/
theorem farFourSignedQ2TowerSupport_iff_survivor_eq_root :
    FarFourSignedQ2TowerSupport ↔
      ∀ R : ℕ, 56 ≤ R →
        finalQ2SurvivorCorrection R = finalQ2RootReassemblyBoundary R := by
  constructor
  · intro h R hR
    have hs := h R hR
    unfold finalQ2SurvivorCorrection
    linear_combination -hs
  · intro h R hR
    have hs := h R hR
    unfold finalQ2SurvivorCorrection at hs
    linear_combination -hs

/-- Once the signed support identity is proved, the exact low/high packet is a
column of genuine q² Mertens daughters plus only the root reassembly boundary.
No norm appears in this composition. -/
theorem finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_root_of_q2Support
    (hsupport : FarFourSignedQ2TowerSupport)
    (R : ℕ) (hR : 56 ≤ R) :
    finalCompensatedLowHighDifference R =
      -(((squareEndpointQ2MertensColumn R : ℤ) : ℂ)) +
        finalQ2RootReassemblyBoundary R := by
  rw [finalCompensatedLowHighDifference_eq_neg_mertensColumn_add_survivor R hR]
  rw [(farFourSignedQ2TowerSupport_iff_survivor_eq_root.mp hsupport) R hR]

/-- Pin the exact Mellin/q² commutator next to the global signed splice. -/
theorem farFour_logMatch : LOG_MATCH := log_match

end RHLean.Proof
