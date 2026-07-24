import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RHLean.Analysis.ActualStartSignedFrame

noncomputable section

open Filter Asymptotics

namespace RHLean.Analysis

/-- Mathlib's formal proposition expressing the Riemann Hypothesis. -/
def RiemannHypothesisStatement : Prop := RiemannHypothesis

/-- The sharp actual-start signed-frame statement supplied by the compiled closure. -/
def ActualStartSignedFrameStatement
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) : Prop :=
  ∀ N,
    actualStartFrameEnergy start N ≤
      4 * actualStartPredictionFrameEnergy start N

/--
The square-prefix growth criterion attached to the actual-start frame energy.
This matches the standard `O(N^(3+ε))` shape, but does not itself assert any
connection to the Riemann Hypothesis.
-/
def ActualStartPrefixBoundedStatement
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun N : ℕ => actualStartFrameEnergy start N) =O[atTop]
      (fun N : ℕ => Real.rpow (N : ℝ) (3 + ε))

/--
The explicit analytic bridge still required after the signed-frame theorem.
Neither field is proved by the algebraic/Gram closure itself:

* `signedFrame_to_prefixBounded` identifies the finite signed-frame inequality
  with the square-prefix asymptotic criterion;
* `prefixBounded_iff_riemannHypothesis` is the external analytic equivalence.

Packaging these as fields keeps every remaining premise visible and avoids
introducing either implication as a project axiom.
-/
structure ActualStartRHBridge
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) where
  signedFrame_to_prefixBounded :
    ActualStartSignedFrameStatement start →
      ActualStartPrefixBoundedStatement start
  prefixBounded_iff_riemannHypothesis :
    ActualStartPrefixBoundedStatement start ↔ RiemannHypothesisStatement

/-- The bridge equivalence remains available as an explicitly supplied theorem. -/
theorem actualStart_prefixBounded_iff_riemannHypothesis
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start) :
    ActualStartPrefixBoundedStatement start ↔ RiemannHypothesisStatement :=
  bridge.prefixBounded_iff_riemannHypothesis

/-- An explicit bridge converts an already proved signed-frame statement to RH. -/
theorem riemannHypothesis_of_actualStartSignedFrame
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start)
    (hframe : ActualStartSignedFrameStatement start) :
    RiemannHypothesisStatement := by
  apply bridge.prefixBounded_iff_riemannHypothesis.mp
  exact bridge.signedFrame_to_prefixBounded hframe

/--
Final composition theorem. The compiled finite-range realization, asymptotic
joint-Gram control, exact starting configuration, and signed interaction
absorption prove the signed-frame statement. An explicitly supplied analytic
bridge then converts that statement to mathlib's `RiemannHypothesis`.
-/
theorem riemannHypothesis_of_compiled_actualStartClosure
    (skeleton : ResonantProjectionSkeleton ℂ ℂ)
    (data : (M : ℕ) → ActualResidualData skeleton.cutoff M)
    (expectation : FiniteRangeCertificateExpectation)
    (realization : ActualFiniteRangeJointGramRealization
      skeleton data expectation)
    (weights : BlockLyapunovWeights)
    (forcingData : ActualForcingData)
    (asymptoticControl : ActualJointGramAsymptoticControl
      skeleton data weights forcingData
        realization.accepted.certificate.rangeEnd)
    (start : ActualStartConfiguration skeleton data)
    (frameControl : ActualStartSignedFrameControl start
      (affineInvariantBound asymptoticControl.rho
        asymptoticControl.forcingBound
        (finiteRangeCertificateBaseBound realization.accepted.certificate)))
    (bridge : ActualStartRHBridge start) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_actualStartSignedFrame start bridge
  exact actualStart_signedFrame
    skeleton data expectation realization weights forcingData
      asymptoticControl start frameControl

end RHLean.Analysis
