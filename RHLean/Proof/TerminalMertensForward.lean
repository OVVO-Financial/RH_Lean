import RHLean.Analysis.MertensRiemannHypothesis
import RHLean.Proof.TerminalMertensReduction

/-!
# Discharge the terminal forward Mertens criterion

The analytic continuation and completed-zeta reflection now construct the one
direction of the classical Mertens criterion that the terminal proof actually
uses.  This file plugs that theorem into `TerminalMertensReduction` and records
the resulting unconditional implication from the projected-renewal estimate to
Mathlib's Riemann Hypothesis.

The reverse implication `RH → MertensEnergyBoundedStatement` is not needed here
and remains outside this forward route.
-/

noncomputable section

namespace RHLean.Proof

namespace TerminalMertensForward

open RHLean.Analysis
open TerminalMertensReduction

/-- The previously external forward Mertens criterion is now constructed from
the Mellin continuation, analytic uniqueness, and completed-zeta reflection. -/
theorem mertensForwardCriterion : MertensForwardCriterion := by
  intro hM
  change RiemannHypothesis
  exact riemannHypothesis_of_mertensEnergyBounded hM

/-- Consequently the terminal implication no longer needs any classical
Mertens/RH criterion supplied by the caller.  Once the projected-renewal
quadratic estimate is proved, RH follows outright. -/
theorem projectedRenewalQuadraticBounded_imp_riemannHypothesis_unconditional
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ProjectedRenewalQuadraticBoundedStatement Λ →
      RiemannHypothesisStatement :=
  projectedRenewalQuadraticBounded_imp_riemannHypothesis
    hΛ mertensForwardCriterion

end TerminalMertensForward

end RHLean.Proof
