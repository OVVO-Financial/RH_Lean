import RHLean.Proof.SquareRootAmplificationLogGrowth

/-!
# An unconditional eventual-budget consumer of zero-log growth

The repository already defines `SquareRootAmplificationZeroLogGrowthStatement`
but does not prove it.  This file proves what **would follow** from that
precise proposition at every physical square endpoint: every positive
logarithmic budget eventually holds simultaneously for all admitted roots.

No assumption about Pintz, zeta zeros, primes, or arithmetic cancellation is
hidden in this theorem. It is deliberately directional: the argument does not
prove zero-log growth and must not be counted as an unconditional RH result.
-/

noncomputable section

namespace RHLean.Proof

/-- A zero logarithmic amplification limit supplies one common eventual
budget for **every** admitted square endpoint through the current cutoff.
The cutoff and maximum are the exact definitions in
`SquareRootAmplificationLogGrowth.lean`. -/
theorem squareRootAmplificationZeroLog_eventually_endpoint_budget
    (hzero : SquareRootAmplificationZeroLogGrowthStatement)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ X : ℕ in Filter.atTop,
      ∀ R : ℕ, 2 ≤ R → squareRootEndpoint R ≤ X →
        Real.log (1 + squareRootEndpointAmplification R) ≤
          eps * Real.log (X : ℝ) := by
  have hlim : Filter.Tendsto squareRootAmplificationLogRatio
      Filter.atTop (nhds (0 : ℝ)) := hzero
  have hnear : {x : ℝ | x < eps} ∈ nhds (0 : ℝ) :=
    isOpen_Iio.mem_nhds heps
  have hbudget : ∀ᶠ X : ℕ in Filter.atTop,
      squareRootAmplificationLogRatio X < eps :=
    hlim.eventually hnear
  filter_upwards [hbudget, Filter.eventually_ge_atTop (2 : ℕ)] with X hX hXge
  exact (squareRootAmplificationLogRatio_le_iff X eps hXge heps.le).1 hX.le

/-- Complete asymptotic characterization of the zero-log proposition by
one **simultaneous** all-square-endpoint budget for each positive epsilon.
The reverse direction uses nonnegativity of the actual logarithmic ratio.
This is an equivalence of two *open* arithmetic statements, not a proof of
either statement unconditionally. -/
theorem squareRootAmplificationZeroLog_iff_eventually_endpoint_budget :
    SquareRootAmplificationZeroLogGrowthStatement ↔
      ∀ eps : ℝ, 0 < eps →
        ∀ᶠ X : ℕ in Filter.atTop,
          ∀ R : ℕ, 2 ≤ R → squareRootEndpoint R ≤ X →
            Real.log (1 + squareRootEndpointAmplification R) ≤
              eps * Real.log (X : ℝ) := by
  constructor
  · intro hzero eps heps
    exact squareRootAmplificationZeroLog_eventually_endpoint_budget hzero heps
  · intro hbudgets
    change Filter.Tendsto squareRootAmplificationLogRatio
      Filter.atTop (nhds (0 : ℝ))
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with X hX
      exact lt_of_lt_of_le ha (squareRootAmplificationLogRatio_nonneg hX)
    · intro b hb
      have heps : 0 < b / 2 := by linarith
      have hbudget := hbudgets (b / 2) heps
      filter_upwards [hbudget, Filter.eventually_ge_atTop (2 : ℕ)]
        with X hX hXge
      have hratio : squareRootAmplificationLogRatio X ≤ b / 2 :=
        (squareRootAmplificationLogRatio_le_iff X (b / 2)
          hXge heps.le).2 hX
      linarith

/-- This is the literal Mobius/strict-history endpoint inequality obtained by
exponentiating the previous eventual logarithmic budget.  In particular it
keeps the real numerator, the factor `R^2`, and the exact `K_R`; no surrogate
energy, cancellation estimate, or unproved universal amplification bound is
substituted.  The positive exponent is arbitrary, but the statement is still
conditional on `hzero`. -/
theorem squareRootAmplificationZeroLog_eventually_native_envelope
    (hzero : SquareRootAmplificationZeroLogGrowthStatement)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ X : ℕ in Filter.atTop,
      ∀ R : ℕ, 2 ≤ R → squareRootEndpoint R ≤ X →
        (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) ≤
          Real.exp (eps * Real.log (X : ℝ)) *
            (R : ℝ) ^ 2 * squareRootHistoricalK R := by
  have hbudget :=
    squareRootAmplificationZeroLog_eventually_endpoint_budget hzero heps
  filter_upwards [hbudget] with X hX
  intro R hR hRX
  have hpositive : 0 < 1 + squareRootEndpointAmplification R := by
    linarith [squareRootEndpointAmplification_nonneg R]
  have hlog : Real.log (1 + squareRootEndpointAmplification R) ≤
      eps * Real.log (X : ℝ) := hX R hR hRX
  have hexp : 1 + squareRootEndpointAmplification R ≤
      Real.exp (eps * Real.log (X : ℝ)) :=
    (Real.log_le_iff_le_exp hpositive).1 hlog
  have hratio : squareRootEndpointAmplification R ≤
      Real.exp (eps * Real.log (X : ℝ)) := by linarith
  exact (squareRootEndpointAmplification_le_iff
    (by omega : 1 ≤ R) (Real.exp (eps * Real.log (X : ℝ)))).1 hratio

end RHLean.Proof
