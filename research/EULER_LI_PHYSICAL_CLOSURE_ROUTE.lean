import Mathlib
import «research.CANONICAL_DESCENDING_PRIME_CHRONOLOGY»
import RHLean.Proof.FarSurvivorRenewal_is_LowerMertens
import RHLean.Proof.PhysicalQ2ExceptionalTerminalSynthesis

/-!
# Euler/Li physical closure route

This file compiles the logical endgame suggested by the physical forcing
decoder without asserting the remaining quantitative estimate.

The already-proved exact global Euler-to-q² bridge says that, on the canonical
complete descending prime chronology,

  raw Euler boundary ledger + root correction
    =
  odd q² Mertens owner column + ownerwise chronology error.

Therefore a single signed FAR-4-scale estimate on the completed Euler ledger is
*exactly equivalent* to the existing ownerwise signed synthesis statement.
That statement is already equivalent to FAR-4, and FAR-4 already has a compiled
terminal consumer to Mathlib's `RiemannHypothesis`.

No triangle inequality, Cauchy-Schwarz split, independence assumption, or new
prime-distribution hypothesis is introduced here.  The only open input is the
uniform signed Euler-ledger estimate defined below.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- **Euler/Li physical boundary statement.**

The canonical raw Euler chronology is kept signed all the way through the root
correction.  The right side is exactly the already-established FAR-4 recursive
budget: four times the genuine odd-owner q² daughter energy plus a root-scale
boundary allowance.

The name records the intended interpretation: Li supplies the macroscopic
centering/equilibrium, while the physical centered source has been decoded into
the Möbius/Euler chronology.  This statement itself is purely finite arithmetic
and makes no appeal to an asymptotic Li approximation. -/
def EulerLiPhysicalBoundaryStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖
          squareRootCanonicalRoughAdaptiveRawLedger R
              (squareRootCanonicalRoughDescendingPrimeSchedule R)
              (Finset.Icc 1 (squareRootEndpoint R))
              (fun _ => (1 : ℂ)) +
            frozenTopFarRoughRootCorrection R
        ‖ ^ 2 ≤
        4 * farFourOddQ2DaughterEnergy R +
          C * (R : ℝ) ^ 2 * K

/-- The proposed Euler/Li boundary estimate is not a new terminal criterion:
by the exact global Euler-to-q² bridge it is literally the existing ownerwise
signed synthesis statement in the canonical descending coordinate. -/
theorem eulerLiPhysicalBoundary_iff_farFourOwnerwiseSignedSynthesis :
    EulerLiPhysicalBoundaryStatement ↔
      FarFourOwnerwiseSignedSynthesisStatement := by
  constructor
  · rintro ⟨C, hC, hEuler⟩
    refine ⟨C, hC, ?_⟩
    intro R K hR hK
    have hbound := hEuler R K hR hK
    have hbridge :=
      adaptiveRawLedger_add_rootCorrection_eq_oddMertensColumn_add_ownerwiseError_of_completeSchedule
        R hR (squareRootCanonicalRoughDescendingPrimeSchedule R)
        (squareRootCanonicalRoughDescendingPrimeSchedule_complete R)
    rw [hbridge] at hbound
    exact hbound
  · rintro ⟨C, hC, hOwner⟩
    refine ⟨C, hC, ?_⟩
    intro R K hR hK
    have hbound := hOwner R K hR hK
    have hbridge :=
      adaptiveRawLedger_add_rootCorrection_eq_oddMertensColumn_add_ownerwiseError_of_completeSchedule
        R hR (squareRootCanonicalRoughDescendingPrimeSchedule R)
        (squareRootCanonicalRoughDescendingPrimeSchedule_complete R)
    rw [hbridge]
    exact hbound

/-- Exact identification of the Euler/Li boundary route with the existing FAR-4
terminal energy statement.  This is a logical/combinatorial identification,
not a proof of the remaining uniform estimate. -/
theorem eulerLiPhysicalBoundary_iff_frozenTopFarFourEnergy :
    EulerLiPhysicalBoundaryStatement ↔
      FrozenTopFarFourEnergyStatement :=
  eulerLiPhysicalBoundary_iff_farFourOwnerwiseSignedSynthesis.trans
    farFourOwnerwiseSignedSynthesis_iff_frozenTopFarFourEnergy

/-- **Compiled logical route to RH.**

Once the single signed Euler-ledger estimate above is proved, no additional
analytic bookkeeping is needed: exact Euler-to-q² identification gives FAR-4,
and the existing terminal theorem gives `RiemannHypothesis`. -/
theorem riemannHypothesis_of_eulerLiPhysicalBoundary
    (hEuler : EulerLiPhysicalBoundaryStatement) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frozenTopFarFourEnergy
  exact eulerLiPhysicalBoundary_iff_frozenTopFarFourEnergy.mp hEuler

end RHLean.Proof
