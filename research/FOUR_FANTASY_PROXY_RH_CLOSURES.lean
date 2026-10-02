import Mathlib
import «research.VF_MID_FRACTIONAL_PRIME_CLUSTER»
import «research.LI_FLOOR_PRIME_COUNT_FANTASY»
import «research.VF_MID_LINEAR_INTERPOLATION_FANTASY»

/-!
# Four fantasy prime-count proxy closures

This file makes the four counterfactual proxy scenarios explicit and routes
each of them to the same classical von-Koch/RH interface.

The four fantasy identifications are:

1. actual prime count equals continuous Li;
2. actual prime count at square endpoints equals the exact discrete VF-mid
   fractional-prime cluster;
3. actual prime count equals the literal midpoint-to-midpoint VF interpolant;
4. actual prime count equals floor(Li).

Each identification is intentionally an explicit hypothesis.  The deterministic
error theorem for each corresponding proxy is proved elsewhere (or trivially
zero in the continuous-Li case), and each hypothesis is consumed here by the
same classical criterion.
-/

noncomputable section

namespace RHLean.Analysis

/-! ## Fantasy 1: continuous Li is actual prime count -/

/-- Counterfactual identification of actual prime count with continuous Li. -/
def ContinuousLiIdentifiesActualPrimes : Prop :=
  ∀ x : ℝ, 4 ≤ x →
    vfMidPrimeCount x = vfMidLogarithmicIntegralFromTwo x

/-- If actual prime count is exactly Li, the classical discrepancy is identically
zero and therefore satisfies the von-Koch bound with constant zero. -/
theorem primeLiVonKochBounded_of_continuousLiIdentification
    (hident : ContinuousLiIdentifiesActualPrimes) :
    PrimeLiVonKochBoundedStatement := by
  refine ⟨0, le_rfl, ?_⟩
  intro x hx
  unfold vfMidPrimeLiError
  rw [hident x hx]
  simp

/-- Fantasy 1 closes RH through the repository's classical criterion. -/
theorem riemannHypothesis_of_continuousLiIdentification
    (criterion : ClassicalVonKochRHCriterion)
    (hident : ContinuousLiIdentifiesActualPrimes) :
    VFMidRiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (primeLiVonKochBounded_of_continuousLiIdentification hident)

/-! ## Fantasy 2: exact discrete VF-mid fractional cluster is actual primes -/

/-- Counterfactual square-endpoint identification of actual prime count with
the exact integer-lattice VF-mid fractional-prime cluster. -/
def VFMidFractionalClusterIdentifiesActualPrimes : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    vfMidPrimeCount ((R : ℝ) ^ 2) =
      vfMidFractionalPrimeClusterMass R

/-- Under exact identification with the fractional VF cluster, the square
endpoint prime-minus-VF error is identically zero. -/
theorem vfMidSquareEndpointVonKochBounded_of_fractionalClusterIdentification
    (hident : VFMidFractionalClusterIdentifiesActualPrimes) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  refine ⟨0, le_rfl, ?_⟩
  intro R hR
  unfold vfMidPrimeError
  rw [hident R hR, vfMidFractionalPrimeClusterMass_eq_vfMid_sq R hR]
  simp

/-- Fantasy 2 closes RH through the already-compiled square-endpoint bridge. -/
theorem riemannHypothesis_of_vfMidFractionalClusterIdentification
    (criterion : ClassicalVonKochRHCriterion)
    (hident : VFMidFractionalClusterIdentifiesActualPrimes) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_fractionalClusterIdentification hident)

/-! ## Fantasies 3 and 4

Fantasy 3 is closed by:
  riemannHypothesis_of_vfMidLinearMidpointIdentification

Fantasy 4 is closed by:
  riemannHypothesis_of_liFloorPrimeCountIdentification

Those theorem statements live with the corresponding proxy definitions so the
error estimates and their RH consumers remain adjacent in the source.
-/

/-! ## Quantitative proxy-to-actual reductions

The exact-identification fantasies above are the zero-error special cases.
For reassessing the real arithmetic problem, the useful formulation is weaker:
each deterministic proxy is already known to track Li at root scale (or better),
so an RH-scale bound between actual prime count and that proxy alone suffices.
-/

/-- Actual prime count tracks a real-valued proxy at the von-Koch scale. -/
def PrimeProxyVonKochTrackingStatement (proxy : ℝ → ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ x : ℝ, 4 ≤ x →
      |vfMidPrimeCount x - proxy x| ≤
        A * Real.sqrt x * Real.log x

/-- A deterministic proxy tracks Li at root scale. -/
def PrimeProxyLiRootBoundedStatement (proxy : ℝ → ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧
    ∀ x : ℝ, 4 ≤ x →
      |proxy x - vfMidLogarithmicIntegralFromTwo x| ≤
        B * Real.sqrt x

/-- Generic transfer: root-scale proxy-to-Li control plus an RH-scale
actual-to-proxy bound yields the classical prime-minus-Li von-Koch bound. -/
theorem primeLiVonKochBounded_of_proxyTracking
    {proxy : ℝ → ℝ}
    (htrack : PrimeProxyVonKochTrackingStatement proxy)
    (hroot : PrimeProxyLiRootBoundedStatement proxy) :
    PrimeLiVonKochBoundedStatement := by
  rcases htrack with ⟨A, hA0, hA⟩
  rcases hroot with ⟨B, hB0, hB⟩
  let ell : ℝ := Real.log 4
  have hell : 0 < ell := by
    dsimp [ell]
    exact Real.log_pos (by norm_num)
  refine ⟨A + B / ell, add_nonneg hA0 (div_nonneg hB0 hell.le), ?_⟩
  intro x hx
  have hlog : ell ≤ Real.log x := by
    dsimp [ell]
    exact Real.log_le_log (by norm_num) hx
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hcoef0 : 0 ≤ (B / ell) * Real.sqrt x :=
    mul_nonneg (div_nonneg hB0 hell.le) hsqrt0
  have hrootScale :
      B * Real.sqrt x ≤
        (B / ell) * Real.sqrt x * Real.log x := by
    have hm := mul_le_mul_of_nonneg_left hlog hcoef0
    have heq :
        (B / ell) * Real.sqrt x * ell = B * Real.sqrt x := by
      field_simp [hell.ne']
    linarith
  have hdecomp :
      vfMidPrimeLiError x =
        (vfMidPrimeCount x - proxy x) +
          (proxy x - vfMidLogarithmicIntegralFromTwo x) := by
    unfold vfMidPrimeLiError
    ring
  rw [hdecomp]
  calc
    |(vfMidPrimeCount x - proxy x) +
        (proxy x - vfMidLogarithmicIntegralFromTwo x)|
        ≤ |vfMidPrimeCount x - proxy x| +
            |proxy x - vfMidLogarithmicIntegralFromTwo x| :=
      abs_add_le _ _
    _ ≤ A * Real.sqrt x * Real.log x + B * Real.sqrt x :=
      add_le_add (hA x hx) (hB x hx)
    _ ≤ A * Real.sqrt x * Real.log x +
        (B / ell) * Real.sqrt x * Real.log x :=
      add_le_add_left hrootScale _
    _ = (A + B / ell) * Real.sqrt x * Real.log x := by ring

/-- Generic RH consumer for any proxy whose deterministic Li error is root
scale and whose actual-prime tracking error is von-Koch scale. -/
theorem riemannHypothesis_of_proxyTracking
    (criterion : ClassicalVonKochRHCriterion)
    {proxy : ℝ → ℝ}
    (htrack : PrimeProxyVonKochTrackingStatement proxy)
    (hroot : PrimeProxyLiRootBoundedStatement proxy) :
    VFMidRiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (primeLiVonKochBounded_of_proxyTracking htrack hroot)

/-! ### Scenario 1: continuous Li -/

def ContinuousLiProxyTrackingStatement : Prop :=
  PrimeProxyVonKochTrackingStatement vfMidLogarithmicIntegralFromTwo

theorem continuousLiProxy_li_root_bounded :
    PrimeProxyLiRootBoundedStatement vfMidLogarithmicIntegralFromTwo := by
  refine ⟨0, le_rfl, ?_⟩
  intro x hx
  simp

theorem riemannHypothesis_of_continuousLiProxyTracking
    (criterion : ClassicalVonKochRHCriterion)
    (htrack : ContinuousLiProxyTrackingStatement) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_proxyTracking criterion htrack
    continuousLiProxy_li_root_bounded

/-! ### Scenario 2: discrete VF-mid fractional cluster -/

/-- Square-endpoint actual-to-proxy tracking for the exact cumulative
fractional VF cluster.  Because the cluster mass equals VF_mid at squares,
this is exactly the direct square-endpoint arithmetic target. -/
def VFMidFractionalClusterSquareTrackingStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 2 ≤ R →
      |vfMidPrimeCount ((R : ℝ) ^ 2) -
          vfMidFractionalPrimeClusterMass R| ≤
        C * (R : ℝ) * Real.log R

theorem vfMidSquareEndpointVonKochBounded_of_fractionalClusterTracking
    (htrack : VFMidFractionalClusterSquareTrackingStatement) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  rcases htrack with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  intro R hR
  have hbound := hC R hR
  rw [vfMidFractionalPrimeClusterMass_eq_vfMid_sq R hR] at hbound
  simpa [vfMidPrimeError] using hbound

theorem riemannHypothesis_of_vfMidFractionalClusterTracking
    (criterion : ClassicalVonKochRHCriterion)
    (htrack : VFMidFractionalClusterSquareTrackingStatement) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_fractionalClusterTracking htrack)

/-! ### Scenario 3: all-real literal VF midpoint interpolation -/

def VFMidLinearProxyTrackingStatement : Prop :=
  PrimeProxyVonKochTrackingStatement vfMidLinearMidpointInterpolant

theorem vfMidLinearProxy_li_root_bounded :
    PrimeProxyLiRootBoundedStatement vfMidLinearMidpointInterpolant := by
  simpa [PrimeProxyLiRootBoundedStatement,
    VFMidLinearMidpointLiRootBoundedStatement] using
      vfMidLinearMidpoint_li_root_bounded

theorem riemannHypothesis_of_vfMidLinearProxyTracking
    (criterion : ClassicalVonKochRHCriterion)
    (htrack : VFMidLinearProxyTrackingStatement) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_proxyTracking criterion htrack
    vfMidLinearProxy_li_root_bounded

/-! ### Scenario 4: floored Li -/

def LiFloorProxyTrackingStatement : Prop :=
  PrimeProxyVonKochTrackingStatement liIntegerCutoffFloorPrimeCountProxy

theorem liFloorProxy_li_root_bounded :
    PrimeProxyLiRootBoundedStatement liIntegerCutoffFloorPrimeCountProxy := by
  let K : ℝ := 1 + 1 / Real.log 4
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK0, ?_⟩
  intro x hx
  have hround :=
    abs_liIntegerCutoffFloorPrimeCountProxy_sub_li_le hx
  have hx0 : 0 ≤ x := by linarith
  have hs := Real.sq_sqrt hx0
  have hs0 := Real.sqrt_nonneg x
  have hsqrt : (1 : ℝ) ≤ Real.sqrt x := by
    nlinarith
  have hscale : K ≤ K * Real.sqrt x := by
    simpa using mul_le_mul_of_nonneg_left hsqrt hK0
  exact hround.trans hscale

theorem riemannHypothesis_of_liFloorProxyTracking
    (criterion : ClassicalVonKochRHCriterion)
    (htrack : LiFloorProxyTrackingStatement) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_proxyTracking criterion htrack
    liFloorProxy_li_root_bounded

/-- The four proxy routes have now been reduced to one explicit arithmetic
input each: an RH-scale bound between actual prime count and that proxy. -/
theorem fourFantasyProxyTrackingBounds_close_RH
    (criterion : ClassicalVonKochRHCriterion) :
    (ContinuousLiProxyTrackingStatement →
      VFMidRiemannHypothesisStatement) ∧
    (VFMidFractionalClusterSquareTrackingStatement →
      VFMidRiemannHypothesisStatement) ∧
    (VFMidLinearProxyTrackingStatement →
      VFMidRiemannHypothesisStatement) ∧
    (LiFloorProxyTrackingStatement →
      VFMidRiemannHypothesisStatement) := by
  exact ⟨riemannHypothesis_of_continuousLiProxyTracking criterion,
    riemannHypothesis_of_vfMidFractionalClusterTracking criterion,
    riemannHypothesis_of_vfMidLinearProxyTracking criterion,
    riemannHypothesis_of_liFloorProxyTracking criterion⟩

end RHLean.Analysis
