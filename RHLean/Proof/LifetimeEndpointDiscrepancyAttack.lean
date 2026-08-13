import Mathlib
import RHLean.Proof.DeathShellSubpolynomial

/-!
# Lifetime endpoint discrepancy is the only remaining lifetime-flow input

The endpoint decomposition writes the active survivor mass as

`birth - death`.

The repository already proves the death process has RH-scale translated local
energy unconditionally for every positive shell parameter `Λ`.  Therefore the
two-premise lifetime endpoint package can be reduced exactly to one analytic
statement: RH-scale local energy for the birth-minus-death discrepancy.

This module makes that deletion explicit and propagates the single remaining
premise to the canonical high-sector and square-prefix criteria, and to the
existing conditional RH terminal.
-/

noncomputable section

namespace RHLean.Proof

/-- For positive shell scale, the old two-part endpoint package is equivalent to
control of the birth-minus-death discrepancy alone because the death half is
already unconditional. -/
theorem lifetimeEndpointUniformLocalBounded_iff_discrepancy
    {Λ : ℝ} (hΛ : 0 < Λ) :
    LifetimeEndpointUniformLocalBoundedStatement Λ ↔
      LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, lifetimeDeathUniformLocalBounded hΛ⟩

/-- Equivalently, the full lifetime-flow criterion itself has only one live
analytic input at positive shell scale. -/
theorem lifetimeFlowUniformLocalBounded_iff_endpointDiscrepancy
    {Λ : ℝ} (hΛ : 0 < Λ) :
    LifetimeFlowUniformLocalBoundedStatement Λ ↔
      LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ := by
  rw [lifetimeFlowUniformLocalBounded_iff_endpoint,
    lifetimeEndpointUniformLocalBounded_iff_discrepancy hΛ]

/-- The single endpoint-discrepancy premise implies the canonical high-sector
uniform local-energy statement. -/
theorem lifetimeEndpointDiscrepancyUniformLocalBounded_implies_canonicalHigh
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hD : LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ) :
    CanonicalHighUniformLocalBoundedStatement Λ := by
  apply lifetimeFlowUniformLocalBounded_implies_canonicalHigh Λ
  exact (lifetimeFlowUniformLocalBounded_iff_endpointDiscrepancy hΛ).2 hD

/-- The same single survivor-discrepancy premise implies the protected
square-prefix uniform-local criterion. -/
theorem lifetimeEndpointDiscrepancyUniformLocalBounded_implies_squarePrefixUniformLocal
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hD : LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ) :
    RHLean.Analysis.SquarePrefixUniformLocalBoundedStatement := by
  apply lifetimeEndpointUniformLocalBounded_implies_squarePrefixUniformLocal Λ
  exact (lifetimeEndpointUniformLocalBounded_iff_discrepancy hΛ).2 hD

/-- Conditional RH terminal with the death-process input deleted.  The only
lifetime-flow analytic premise left is the birth-minus-death discrepancy. -/
theorem lifetimeEndpointDiscrepancyUniformLocalBounded_implies_riemannHypothesis
    {Λ : ℝ} (hΛ : 0 < Λ)
    (criterion : RHLean.Analysis.ClassicalMertensRHCriterion)
    (hD : LifetimeEndpointDiscrepancyUniformLocalBoundedStatement Λ) :
    RHLean.Analysis.RiemannHypothesisStatement := by
  apply lifetimeEndpointUniformLocalBounded_implies_riemannHypothesis Λ criterion
  exact (lifetimeEndpointUniformLocalBounded_iff_discrepancy hΛ).2 hD

end RHLean.Proof
