import Mathlib
import «research.DIRECT_SUM_COUPLED_PACKET»
import RHLean.Proof.PostRootPartnerEulerMemory
import RHLean.Proof.LowWheelCanonicalRepeatedMassReduction

/-!
# Coupled direct-sum packet: fresh-prime / range-exit decomposition

This file is exact finite algebra.  It does not prove a dispersion estimate or
FAR-4.

The adaptive raw Euler ledger already keeps every signed fresh-prime update
before norms.  Here one step is split into two pieces:

* the internal fresh-prime threshold term, where a parent partner lies at or
  below the newly adjoined prime;
* the range-exit term, containing genuine terminal top escapes, lower-root
  births with their sign, and the exact inherited-coefficient mismatch.  The
  mismatch belongs here because it is the algebraic memory of earlier carrier
  exits: it is precisely what remains when two current endpoints inherited
  different larger-prime histories.

These two pieces are then iterated along the actual adaptive chronology.  On a
complete descending schedule the named coupled PNT packet is exactly the
fresh-prime ledger plus the range-exit packet, where the latter also contains
the already explicit root correction and subtracts the exact dyadic
reconstruction remainder.  No absolute value, Cauchy inequality, or energy
bound is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Internal threshold part of one adaptive fresh-prime step. -/
def directSumCoupledFreshPrimeThresholdStepMass
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    a c * canonicalMoebiusWeight c *
      ((squareRootCanonicalRoughFreshThresholdLossBoundary R c p).card : ℂ)

/-- Geometric range motion at one step: genuine top escape minus lower-root
birth, before coefficient-mismatch memory is added. -/
def directSumCoupledGeometricRangeExitStepMass
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ c ∈ squareRootCanonicalRoughFreshPrimeParentsOn p U,
    a c * canonicalMoebiusWeight c *
      (((squareRootCanonicalRoughFreshTopEscapeBoundary R c p).card : ℂ) -
        ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ))

/-- Full range-exit contribution of one adaptive step.  Besides literal
geometric exits/entries it retains the exact coefficient mismatch created by
unequal earlier histories. -/
def directSumCoupledRangeExitStepMass
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  directSumCoupledGeometricRangeExitStepMass R p U a +
    squareRootCanonicalRoughAdaptiveRawMismatchMass R p U a

/-- The raw physical boundary is exactly threshold fresh-prime mass plus
geometric range motion. -/
theorem squareRootCanonicalRoughAdaptiveRawBoundaryMass_eq_freshPrimeThreshold_add_geometricRangeExit
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) :
    squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a =
      directSumCoupledFreshPrimeThresholdStepMass R p U a +
        directSumCoupledGeometricRangeExitStepMass R p U a := by
  unfold squareRootCanonicalRoughAdaptiveRawBoundaryMass
    directSumCoupledFreshPrimeThresholdStepMass
    directSumCoupledGeometricRangeExitStepMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [squareRootCanonicalRoughFreshLossBoundary_card_eq_threshold_add_topEscape]
  push_cast
  ring

/-- Consequently the complete one-step raw correction, including mismatch, is
exactly fresh-prime threshold plus range exit. -/
theorem adaptiveRawBoundary_add_mismatch_eq_freshPrime_add_rangeExit
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) :
    squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a +
        squareRootCanonicalRoughAdaptiveRawMismatchMass R p U a =
      directSumCoupledFreshPrimeThresholdStepMass R p U a +
        directSumCoupledRangeExitStepMass R p U a := by
  rw [squareRootCanonicalRoughAdaptiveRawBoundaryMass_eq_freshPrimeThreshold_add_geometricRangeExit]
  unfold directSumCoupledRangeExitStepMass
  ring

/-- Cumulative internal fresh-prime threshold mass along the literal adaptive
raw chronology. -/
def directSumCoupledFreshPrimeLedger
    (R : ℕ) : List ℕ → Finset ℕ → (ℕ → ℂ) → ℂ
  | [], _U, _a => 0
  | p :: ps, U, a =>
      directSumCoupledFreshPrimeThresholdStepMass R p U a +
        directSumCoupledFreshPrimeLedger R ps
          (squareRootCanonicalRoughAdaptiveNextCarrier p U)
          (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)

/-- Cumulative range-exit/mismatch mass along the same adaptive chronology. -/
def directSumCoupledRangeExitLedger
    (R : ℕ) : List ℕ → Finset ℕ → (ℕ → ℂ) → ℂ
  | [], _U, _a => 0
  | p :: ps, U, a =>
      directSumCoupledRangeExitStepMass R p U a +
        directSumCoupledRangeExitLedger R ps
          (squareRootCanonicalRoughAdaptiveNextCarrier p U)
          (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)

/-- **Exact chronological split.**  The complete adaptive raw ledger is the sum
of the fresh-prime threshold ledger and the range-exit ledger. -/
theorem squareRootCanonicalRoughAdaptiveRawLedger_eq_freshPrime_add_rangeExit
    (R : ℕ) (ps : List ℕ) (U : Finset ℕ) (a : ℕ → ℂ) :
    squareRootCanonicalRoughAdaptiveRawLedger R ps U a =
      directSumCoupledFreshPrimeLedger R ps U a +
        directSumCoupledRangeExitLedger R ps U a := by
  induction ps generalizing U a with
  | nil =>
      simp [squareRootCanonicalRoughAdaptiveRawLedger,
        directSumCoupledFreshPrimeLedger, directSumCoupledRangeExitLedger]
  | cons p ps ih =>
      have hstep := adaptiveRawBoundary_add_mismatch_eq_freshPrime_add_rangeExit
        R p U a
      have htail := ih
        (U := squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (a := squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)
      simp only [squareRootCanonicalRoughAdaptiveRawLedger,
        directSumCoupledFreshPrimeLedger, directSumCoupledRangeExitLedger]
      rw [hstep, htail]
      ring

/-- Physical fresh-prime part of the coupled packet for one chosen schedule. -/
def directSumCoupledFreshPrimePacket (R : ℕ) (ps : List ℕ) : ℂ :=
  directSumCoupledFreshPrimeLedger R ps
    (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))

/-- Everything in the coupled PNT packet which is not the internal fresh-prime
threshold telescope: chronological range exits/mismatch, the explicit rough
root correction, and the exact dyadic reconstruction remainder with its native
sign. -/
def directSumCoupledRangeExitPacket (R : ℕ) (ps : List ℕ) : ℂ :=
  directSumCoupledRangeExitLedger R ps
      (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ)) +
    frozenTopFarRoughRootCorrection R - directSumDyadicFarRemainder R

/-- **Coupled fresh-prime / range-exit decomposition.**

On any complete descending prime schedule, the scalar packet measured by
`kappa_R` is exactly the internal fresh-prime threshold telescope plus the
range-exit packet.  Cancellation is preserved all the way through this equality;
there is no norm or estimate in the proof. -/
theorem directSumCoupledPNTPacket_eq_freshPrimePacket_add_rangeExitPacket
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    directSumCoupledPNTPacket R =
      directSumCoupledFreshPrimePacket R ps +
        directSumCoupledRangeExitPacket R ps := by
  have hfar := directSumCoupledFarPacket_eq_frozenTopFarResidual R
  have hraw :=
    lowWheelFrozenTopFarResidual_eq_rawLedger_add_rootCorrection_of_completeSchedule
      R hR ps hsched
  have hsplit :=
    squareRootCanonicalRoughAdaptiveRawLedger_eq_freshPrime_add_rangeExit
      R ps (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))
  unfold directSumCoupledFarPacket at hfar
  unfold directSumCoupledFreshPrimePacket directSumCoupledRangeExitPacket
  rw [hraw, hsplit] at hfar
  linear_combination hfar

end RHLean.Proof
