import Mathlib
import «research.DIRECT_SUM_FRESH_PRIME_GLOBAL_COLLAPSE»
import RHLean.Proof.PostRootPartnerReciprocalCompression

/-!
# Fresh-prime chronology as a prime-weighted reciprocal Stokes ledger

The global collapse layer proves that the complete descending raw chronology is
exactly the fresh-prime threshold ledger.  Independently, the reciprocal
compression layer proves on the same evolved carrier that one raw boundary is
exactly the current prime times a signed drop from the raw state to the
cofactor-weighted reciprocal Euler next state.

This file composes those two exact statements before any norm is taken.  The
result is a global pre-square normal form

  rough correlation = sum_p p * (raw state before p - reciprocal Euler state after p).

The cofactor weight is essential: the literal truncated-wheel column is
reciprocal in the cofactor, whereas the RH-critical raw ledger is not.  The
compiled raw-to-reciprocal coordinate change supplies exactly that missing
factor and creates no mismatch on a complete descending prefix.

No estimate, absolute value, q^2 energy inequality, or RH-scale hypothesis is
used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Prime-weighted reciprocal Stokes drop at the current prime, written on the
literal evolved raw state after the already-processed prefix `pre`. -/
def directSumFreshPrimeScaledReciprocalDrop
    (R p : ℕ) (pre : List ℕ) : ℂ :=
  let U0 := Finset.Icc 1 (squareRootEndpoint R)
  let U := squareRootCanonicalRoughAdaptiveCarrier pre U0
  let a := squareRootCanonicalRoughAdaptiveRawCoefficient pre U0
    (fun _ => (1 : ℂ))
  let b := fun n : ℕ => (n : ℂ) * a n
  (p : ℂ) *
    (squareRootCanonicalRoughAdaptiveRawWeightedMass R U a -
      squareRootCanonicalRoughAdaptiveWeightedMass R
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveNextCoefficient p U b))

/-- **Fresh threshold = scaled reciprocal Stokes drop.**  On a complete
processed prefix, #699 removes top escape/birth/mismatch from the raw boundary,
while the reciprocal compression theorem identifies that same raw boundary
with the prime-scaled cofactor-weighted Euler drop. -/
theorem directSumFreshPrimeThresholdStepMass_eq_scaledReciprocalDrop
    (R : ℕ) {p : ℕ} (pre : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p pre) :
    let U0 := Finset.Icc 1 (squareRootEndpoint R)
    let U := squareRootCanonicalRoughAdaptiveCarrier pre U0
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient pre U0
      (fun _ => (1 : ℂ))
    directSumCoupledFreshPrimeThresholdStepMass R p U a =
      directSumFreshPrimeScaledReciprocalDrop R p pre := by
  dsimp [directSumFreshPrimeScaledReciprocalDrop]
  rw [← adaptiveRawBoundaryMass_evolved_eq_freshPrimeThreshold_of_completeDescendingPrefix
    R pre hR hp hcomplete]
  exact evolvedRawBoundary_eq_scaledReciprocalDrop_of_completeDescendingPrefix
    R pre hR hp hcomplete

/-- Cumulative prime-weighted Stokes ledger along the literal chronology.  The
processed prefix is retained in the recursion because it determines the actual
evolved coefficient field. -/
def directSumFreshPrimeScaledReciprocalDropLedger
    (R : ℕ) : List ℕ → List ℕ → ℂ
  | _pre, [] => 0
  | pre, p :: ps =>
      directSumFreshPrimeScaledReciprocalDrop R p pre +
        directSumFreshPrimeScaledReciprocalDropLedger R (pre ++ [p]) ps

/-- The cumulative Stokes ledger is exactly the fresh-prime ledger on every
stepwise-complete chronology.  This is finite iteration of the preceding
one-step equality; no inequality is introduced. -/
theorem directSumFreshPrimeScaledReciprocalDropLedger_eq_freshLedger
    (R : ℕ) (pre ps : List ℕ) (hR : 2 ≤ R)
    (hstep : SquareRootCanonicalRoughStepwiseComplete R pre ps) :
    directSumFreshPrimeScaledReciprocalDropLedger R pre ps =
      directSumCoupledFreshPrimeLedger R ps
        (squareRootCanonicalRoughAdaptiveCarrier pre
          (Finset.Icc 1 (squareRootEndpoint R)))
        (squareRootCanonicalRoughAdaptiveRawCoefficient pre
          (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))) := by
  induction ps generalizing pre with
  | nil =>
      simp [directSumFreshPrimeScaledReciprocalDropLedger,
        directSumCoupledFreshPrimeLedger]
  | cons p ps ih =>
      rcases hstep with ⟨hp, hcomplete, htail⟩
      have hhead :=
        directSumFreshPrimeThresholdStepMass_eq_scaledReciprocalDrop
          R pre hR hp hcomplete
      have htailEq := ih (pre := pre ++ [p]) htail
      simp only [directSumFreshPrimeScaledReciprocalDropLedger,
        directSumCoupledFreshPrimeLedger]
      rw [← hhead, htailEq]
      congr 1
      · rfl
      · simpa [squareRootCanonicalRoughAdaptiveCarrier_append,
          squareRootCanonicalRoughAdaptiveRawCoefficient_append,
          squareRootCanonicalRoughAdaptiveCarrier,
          squareRootCanonicalRoughAdaptiveRawCoefficient]

/-- On every repository-complete descending schedule the fresh packet is
literally the prime-weighted reciprocal Stokes ledger. -/
theorem directSumFreshPrimeScaledReciprocalDropLedger_eq_freshPacket_of_completeSchedule
    (R : ℕ) (ps : List ℕ) (hR : 2 ≤ R)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    directSumFreshPrimeScaledReciprocalDropLedger R [] ps =
      directSumCoupledFreshPrimePacket R ps := by
  have hstep :=
    squareRootCanonicalRoughStepwiseComplete_of_completeDescendingSchedule
      R ps hsched
  have h :=
    directSumFreshPrimeScaledReciprocalDropLedger_eq_freshLedger
      R [] ps hR hstep
  unfold directSumCoupledFreshPrimePacket
  simpa [squareRootCanonicalRoughAdaptiveCarrier,
    squareRootCanonicalRoughAdaptiveRawCoefficient] using h

/-- **Global pre-square Stokes normal form.**  The canonical rough critical
correlation is exactly the sum of the prime-weighted reciprocal Euler drops
along any complete descending chronology. -/
theorem directSumFreshPrimeScaledReciprocalDropLedger_eq_roughCorrelation
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    directSumFreshPrimeScaledReciprocalDropLedger R [] ps =
      squareRootCanonicalRoughCorrelation R := by
  calc
    directSumFreshPrimeScaledReciprocalDropLedger R [] ps =
        directSumCoupledFreshPrimePacket R ps :=
      directSumFreshPrimeScaledReciprocalDropLedger_eq_freshPacket_of_completeSchedule
        R ps (by omega) hsched
    _ = squareRootCanonicalRoughCorrelation R :=
      directSumCoupledFreshPrimePacket_eq_roughCorrelation_of_completeSchedule
        R hR ps hsched

end RHLean.Proof
