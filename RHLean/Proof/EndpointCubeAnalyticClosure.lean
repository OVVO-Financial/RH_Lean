import RHLean.Proof.RiemannHypothesisBridge
import RHLean.Proof.GlobalFirstJumpCriticalCorrelationBridge

noncomputable section

open scoped BigOperators Topology

namespace RHLean.Analysis

/-- Local square energy of an abstract endpoint-boundary sequence. -/
def endpointBoundaryLocalEnergy (boundary : ℕ → ℂ) (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H, ‖boundary (N + h)‖ ^ 2

/--
The supreme endpoint-cube analytic target: uniform local square-root-scale
control on every translated square-prefix window.
-/
def EndpointCubeUniformLocalBoundaryStatement (boundary : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        endpointBoundaryLocalEnergy boundary N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)

/--
An exact realization identifies the endpoint-cube boundary sequence with the
actual square-prefix sequence already used by the RH bridge.
-/
structure EndpointCubeBoundaryRealization
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (boundary : ℕ → ℂ) where
  boundary_eq_actual : ∀ N, boundary N = start.actual N

/-- Exact realization transfers endpoint-boundary local control to the existing criterion. -/
theorem actualStart_uniformLocalBounded_of_endpointBoundary
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (boundary : ℕ → ℂ)
    (realization : EndpointCubeBoundaryRealization start boundary)
    (hboundary : EndpointCubeUniformLocalBoundaryStatement boundary) :
    ActualStartUniformLocalBoundedStatement start := by
  intro ε hε
  rcases hboundary ε hε with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N H hH hHN
  simpa [endpointBoundaryLocalEnergy, actualStartLocalFrameEnergy,
    realization.boundary_eq_actual] using hbound N H hH hHN

/-- Endpoint-cube local boundary control implies RH through the explicit existing bridge. -/
theorem riemannHypothesis_of_endpointCubeBoundary
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start)
    (boundary : ℕ → ℂ)
    (realization : EndpointCubeBoundaryRealization start boundary)
    (hboundary : EndpointCubeUniformLocalBoundaryStatement boundary) :
    RiemannHypothesisStatement := by
  apply (actualStart_uniformLocalBounded_iff_riemannHypothesis start bridge).mp
  exact actualStart_uniformLocalBounded_of_endpointBoundary
    start boundary realization hboundary

/--
The first backward analytic layer. The exact boundary is decomposed into a
smooth main term and a signed oscillatory residual. The closure field is kept
explicit: this structure records the precise remaining analytic theorem rather
than asserting it from the two component bounds by absolute values.
-/
structure EndpointCubeSmoothResidualControl
    (boundary smooth residual : ℕ → ℂ) where
  exact_decomposition : ∀ N, boundary N = smooth N + residual N
  smooth_uniform_local : EndpointCubeUniformLocalBoundaryStatement smooth
  residual_uniform_local : EndpointCubeUniformLocalBoundaryStatement residual
  signed_recombination_closure : EndpointCubeUniformLocalBoundaryStatement boundary

/-- Smooth/residual control exposes the supreme endpoint-boundary estimate. -/
theorem endpointBoundary_of_smoothResidualControl
    {boundary smooth residual : ℕ → ℂ}
    (control : EndpointCubeSmoothResidualControl boundary smooth residual) :
    EndpointCubeUniformLocalBoundaryStatement boundary :=
  control.signed_recombination_closure

/--
The second backward layer. A full signed Gram theorem must retain all diagonal
and off-diagonal boundary-packet interactions and deliver the smooth/residual
control without replacing the signed form by separate positive shell bounds.
-/
structure EndpointCubeSignedGramControl
    (boundary smooth residual : ℕ → ℂ) where
  smoothResidualControl : EndpointCubeSmoothResidualControl boundary smooth residual

/-- Full signed Gram control closes the endpoint-boundary estimate. -/
theorem endpointBoundary_of_signedGramControl
    {boundary smooth residual : ℕ → ℂ}
    (control : EndpointCubeSignedGramControl boundary smooth residual) :
    EndpointCubeUniformLocalBoundaryStatement boundary :=
  control.smoothResidualControl.signed_recombination_closure

/-- The complete backward theorem: signed endpoint-cube Gram control implies RH. -/
theorem riemannHypothesis_of_endpointCubeSignedGram
    {skeleton : ResonantProjectionSkeleton ℂ ℂ}
    {data : (M : ℕ) → ActualResidualData skeleton.cutoff M}
    (start : ActualStartConfiguration skeleton data)
    (bridge : ActualStartRHBridge start)
    (boundary smooth residual : ℕ → ℂ)
    (realization : EndpointCubeBoundaryRealization start boundary)
    (control : EndpointCubeSignedGramControl boundary smooth residual) :
    RiemannHypothesisStatement := by
  exact riemannHypothesis_of_endpointCubeBoundary
    start bridge boundary realization
      (endpointBoundary_of_signedGramControl control)

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
