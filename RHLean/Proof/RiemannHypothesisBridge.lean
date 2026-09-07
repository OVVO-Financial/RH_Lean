import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RHLean.Proof.ActualStartLocalSignedFrame
import RHLean.Proof.GlobalFirstJumpCriticalCorrelationBridge

noncomputable section

namespace RHLean.Analysis

open RHLean.Verification

/-- Mathlib's formal proposition expressing the Riemann Hypothesis. -/
def RiemannHypothesisStatement : Prop := RiemannHypothesis

/-- The sharp actual-start signed-frame statement on every local window. -/
def ActualStartLocalSignedFrameStatement
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) : Prop :=
  ∀ N H,
    actualStartLocalFrameEnergy start N H ≤
      4 * actualStartLocalPredictionFrameEnergy start N H

/--
The manuscript's uniform local square-prefix criterion:
`V_loc(N,H) ≪_ε H N^(2+ε)` uniformly for `1 ≤ H ≤ N`.
-/
def ActualStartUniformLocalBoundedStatement
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        actualStartLocalFrameEnergy start N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/-- The pointwise square-prefix bound obtained from the local criterion at `H = 1`. -/
def ActualStartPointwiseSquareBoundedStatement
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, 1 ≤ N →
        ‖start.actual N‖ ^ 2 ≤
          C * Real.rpow (N : ℝ) (2 + ε)

/-- Taking `H = 1` in the uniform local criterion gives the pointwise bound. -/
theorem actualStart_pointwiseSquareBounded_of_uniformLocalBounded
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (hlocal : ActualStartUniformLocalBoundedStatement start) :
    ActualStartPointwiseSquareBoundedStatement start := by
  intro ε hε
  rcases hlocal ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N hN
  have h := hbound N 1 (by simp) hN
  simpa [actualStartLocalFrameEnergy] using h

/--
The corrected explicit analytic bridge. The elementary localization step
`uniform local → pointwise` is proved above. The remaining fields isolate:

* the prediction estimate transporting the local signed-frame theorem to the
  manuscript's uniform local bound;
* the classical RH-to-local direction;
* the pointwise square-prefix/Mertens converse to RH.

No field is introduced as an axiom or treated as already proved.
-/
structure ActualStartRHBridge
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data) where
  localSignedFrame_to_uniformLocalBounded :
    ActualStartLocalSignedFrameStatement start →
      ActualStartUniformLocalBoundedStatement start
  riemannHypothesis_to_uniformLocalBounded :
    RiemannHypothesisStatement →
      ActualStartUniformLocalBoundedStatement start
  pointwiseSquareBounded_to_riemannHypothesis :
    ActualStartPointwiseSquareBoundedStatement start →
      RiemannHypothesisStatement

/--
The manuscript's uniform local square-prefix criterion is equivalent to RH once
the two classical square-prefix/Mertens directions are explicitly supplied.
-/
theorem actualStart_uniformLocalBounded_iff_riemannHypothesis
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start) :
    ActualStartUniformLocalBoundedStatement start ↔
      RiemannHypothesisStatement := by
  constructor
  · intro hlocal
    exact bridge.pointwiseSquareBounded_to_riemannHypothesis
      (actualStart_pointwiseSquareBounded_of_uniformLocalBounded start hlocal)
  · exact bridge.riemannHypothesis_to_uniformLocalBounded

/-- An explicit corrected bridge converts a uniform local signed-frame theorem to RH. -/
theorem riemannHypothesis_of_actualStartLocalSignedFrame
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start)
    (hframe : ActualStartLocalSignedFrameStatement start) :
    RiemannHypothesisStatement := by
  apply (actualStart_uniformLocalBounded_iff_riemannHypothesis start bridge).mp
  exact bridge.localSignedFrame_to_uniformLocalBounded hframe

/--
Corrected final composition theorem. It uses the compiled uniform residual
closure plus a genuinely local signed-interaction control to prove the local
frame statement. The explicit analytic bridge then applies the manuscript's
uniform local criterion rather than the insufficient global cubic average.
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
    (localFrameControl : ActualStartLocalSignedFrameControl start
      (affineInvariantBound asymptoticControl.rho
        asymptoticControl.forcingBound
        (finiteRangeCertificateBaseBound realization.accepted.certificate)))
    (bridge : ActualStartRHBridge start) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_actualStartLocalSignedFrame start bridge
  exact actualStart_localSignedFrame
    skeleton data expectation realization weights forcingData
      asymptoticControl start localFrameControl

end RHLean.Analysis

namespace RHLean.Proof

open RHLean.Analysis

/-! ## Product packing as a square-root covariance power contraction -/

/-- The post-root family carrier in the covariance descent is the same prime
set whose quotient seats were packed injectively in the first-jump geometry. -/
theorem postRootPrimeFamilySet_eq_signedFirstJumpPostRootPrimeSet (W : ℕ) :
    postRootPrimeFamilySet W = signedFirstJumpPostRootPrimeSet W := by
  ext p
  simp [postRootPrimeFamilySet, signedFirstJumpPostRootPrimeSet,
    mem_frozenPrimeUniverseHighPrimeSet, and_comm, and_left_comm, and_assoc]

/-- Hence the exact #588 product packing applies verbatim to the lower scales
`floor(W/p)` copied by the post-root covariance families. -/
theorem sum_postRootPrimeFamily_quotients_le_endpoint (W : ℕ) :
    (∑ p ∈ postRootPrimeFamilySet W, W / p) ≤ W := by
  rw [postRootPrimeFamilySet_eq_signedFirstJumpPostRootPrimeSet]
  exact sum_signedFirstJumpPostRootPrimeSeatCounts_le_root W

/-- Every post-root quotient lies at square-root scale: its square is at most
the physical endpoint. -/
theorem postRootPrimeFamily_quotient_sq_le
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet W) :
    (W / p) ^ 2 ≤ W := by
  rcases mem_postRootPrimeFamilySet.mp hp with ⟨hpRoot, _hpW, hpPrime⟩
  have hWpp : W < p * p := (Nat.sqrt_lt).1 hpRoot
  have hq_lt_p : W / p < p :=
    (Nat.div_lt_iff_lt_mul hpPrime.pos).2 hWpp
  have hqp : (W / p) * p ≤ W := Nat.div_mul_le_self W p
  calc
    (W / p) ^ 2 = (W / p) * (W / p) := by ring
    _ ≤ (W / p) * p := Nat.mul_le_mul_left _ hq_lt_p.le
    _ ≤ W := hqp

private theorem rpow_one_add_le_mul_halfPower_of_sq_le
    {q W : ℕ} {ε : ℝ}
    (hq : 1 ≤ q) (hqqW : q ^ 2 ≤ W) (hε : 0 ≤ ε) :
    Real.rpow (q : ℝ) (1 + ε) ≤
      (q : ℝ) * Real.rpow (W : ℝ) (ε / 2) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqnonneg : (0 : ℝ) ≤ (q : ℝ) := hqpos.le
  have hsq : ((q : ℝ) ^ 2) ≤ (W : ℝ) := by exact_mod_cast hqqW
  have hexp : 0 ≤ ε / 2 := by linarith
  have hqpowTwo : Real.rpow (q : ℝ) (2 : ℝ) = (q : ℝ) ^ (2 : ℕ) :=
    Real.rpow_natCast (q : ℝ) 2
  have hhalf :
      Real.rpow (q : ℝ) ε =
        Real.rpow ((q : ℝ) ^ 2) (ε / 2) := by
    calc
      Real.rpow (q : ℝ) ε =
          Real.rpow (q : ℝ) (2 * (ε / 2)) := by
        congr 1
        ring
      _ = Real.rpow (Real.rpow (q : ℝ) (2 : ℝ)) (ε / 2) :=
        Real.rpow_mul hqnonneg (2 : ℝ) (ε / 2)
      _ = Real.rpow ((q : ℝ) ^ 2) (ε / 2) := by rw [hqpowTwo]
  have hqeps :
      Real.rpow (q : ℝ) ε ≤ Real.rpow (W : ℝ) (ε / 2) := by
    rw [hhalf]
    exact Real.rpow_le_rpow (by positivity) hsq hexp
  calc
    Real.rpow (q : ℝ) (1 + ε) =
        Real.rpow (q : ℝ) 1 * Real.rpow (q : ℝ) ε :=
      Real.rpow_add (x := (q : ℝ)) hqpos 1 ε
    _ = (q : ℝ) * Real.rpow (q : ℝ) ε := by rw [Real.rpow_one]
    _ ≤ (q : ℝ) * Real.rpow (W : ℝ) (ε / 2) :=
      mul_le_mul_of_nonneg_left hqeps hqnonneg

/-- **Square-root power packing.**  The complete post-root family population at
power `1+ε` costs only `W * W^(ε/2)`.  This is the quantitative gain needed for
the covariance bootstrap and uses no PNT input. -/
theorem sum_postRootPrimeFamily_rpow_le_endpoint_halfPower
    (W : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ p ∈ postRootPrimeFamilySet W,
        Real.rpow ((W / p : ℕ) : ℝ) (1 + ε)) ≤
      (W : ℝ) * Real.rpow (W : ℝ) (ε / 2) := by
  have hterm : ∀ p ∈ postRootPrimeFamilySet W,
      Real.rpow ((W / p : ℕ) : ℝ) (1 + ε) ≤
        ((W / p : ℕ) : ℝ) * Real.rpow (W : ℝ) (ε / 2) := by
    intro p hp
    rcases mem_postRootPrimeFamilySet.mp hp with ⟨_hpRoot, hpW, hpPrime⟩
    have hq1 : 1 ≤ W / p :=
      (Nat.one_le_div_iff hpPrime.pos).2 hpW
    exact rpow_one_add_le_mul_halfPower_of_sq_le hq1
      (postRootPrimeFamily_quotient_sq_le hp) hε
  have hpackNat := sum_postRootPrimeFamily_quotients_le_endpoint W
  have hpack :
      (∑ p ∈ postRootPrimeFamilySet W, ((W / p : ℕ) : ℝ)) ≤ (W : ℝ) := by
    exact_mod_cast hpackNat
  have hfactor : 0 ≤ Real.rpow (W : ℝ) (ε / 2) := by positivity
  calc
    (∑ p ∈ postRootPrimeFamilySet W,
        Real.rpow ((W / p : ℕ) : ℝ) (1 + ε)) ≤
      ∑ p ∈ postRootPrimeFamilySet W,
        (((W / p : ℕ) : ℝ) * Real.rpow (W : ℝ) (ε / 2)) :=
      Finset.sum_le_sum hterm
    _ = Real.rpow (W : ℝ) (ε / 2) *
        (∑ p ∈ postRootPrimeFamilySet W, ((W / p : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ Real.rpow (W : ℝ) (ε / 2) * (W : ℝ) :=
      mul_le_mul_of_nonneg_left hpack hfactor
    _ = (W : ℝ) * Real.rpow (W : ℝ) (ε / 2) := by ring

end RHLean.Proof
