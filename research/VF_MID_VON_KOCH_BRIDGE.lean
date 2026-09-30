import Mathlib
import RHLean.Analysis.PrimeSieveAbelIdentity
import RHLean.Proof.RiemannHypothesisBridge

/-!
# Square-tile midpoint prime-count bridge

This file formalizes the square-tile midpoint path VF_mid used to compare the
exact prime-counting staircase with the logarithmic integral without replacing
the square partition by an integer-site Li proxy.

The intended proof architecture is deliberately minimal:

1. define the real-valued continuous midpoint path vfMid;
2. prove the unconditional quadrature bridge
     vfMid(x) = logarithmicIntegralFromTwo(x) + O(1);
3. isolate the single RH-scale arithmetic target
     |pi(x) - vfMid(x)| <= C * sqrt(x) * log(x);
4. transfer that target to the classical von-Koch prime-count discrepancy.

No per-tile absolute error hypothesis and no separate signed-cancellation
criterion is introduced here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-! ## The midpoint-tiled logarithmic integral -/

/-- Square-band index used by the midpoint path.  For x >= 0 this is
floor (sqrt x). -/
def vfMidSquareRootIndex (x : ℝ) : ℕ :=
  ⌊Real.sqrt x⌋₊

/-- Midpoint of the complete square band [r^2,(r+1)^2). -/
def vfMidBandMidpoint (r : ℕ) : ℝ :=
  (r : ℝ) ^ 2 + (r : ℝ) + (1 / 2 : ℝ)

/-- Midpoint Li mass assigned to one completed square band. -/
def vfMidBandMass (r : ℕ) : ℝ :=
  (2 * (r : ℝ) + 1) / Real.log (vfMidBandMidpoint r)

/-- Sum of all completed midpoint masses before square index R. -/
def vfMidFinishedMass (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 2 R, vfMidBandMass r

/-- Interpolated midpoint mass on the live square band containing x. -/
def vfMidLiveMass (x : ℝ) : ℝ :=
  let R := vfMidSquareRootIndex x
  (x - (R : ℝ) ^ 2) /
    Real.log (((R : ℝ) ^ 2 + x) / 2)

/-- The continuous square-tile midpoint path.

For x < 4 it is zero.  For x >= 4, if R = floor (sqrt x), this is

sum_{r=2}^{R-1} (2r+1)/log(r^2+r+1/2)
 + (x-R^2)/log((R^2+x)/2).
-/
def vfMid (x : ℝ) : ℝ :=
  if x < 4 then 0
  else vfMidFinishedMass (vfMidSquareRootIndex x) + vfMidLiveMass x

/-- The square-root index is exact at square endpoints. -/
@[simp] theorem vfMidSquareRootIndex_sq (R : ℕ) :
    vfMidSquareRootIndex ((R : ℝ) ^ 2) = R := by
  simp [vfMidSquareRootIndex]

/-- The live contribution vanishes when the live band is empty. -/
@[simp] theorem vfMidLiveMass_sq (R : ℕ) :
    vfMidLiveMass ((R : ℝ) ^ 2) = 0 := by
  simp [vfMidLiveMass]

/-- Completing one additional square band appends exactly its midpoint mass. -/
theorem vfMidFinishedMass_succ {R : ℕ} (hR : 2 ≤ R) :
    vfMidFinishedMass (R + 1) =
      vfMidFinishedMass R + vfMidBandMass R := by
  unfold vfMidFinishedMass
  rw [Finset.sum_Ico_succ_top hR]

/-- At every square endpoint R^2 with R >= 2, the path is exactly the sum of
the completed bands before R; there is no live-band correction. -/
theorem vfMid_sq {R : ℕ} (hR : 2 ≤ R) :
    vfMid ((R : ℝ) ^ 2) = vfMidFinishedMass R := by
  have h4nat : 4 ≤ R ^ 2 := by nlinarith
  have h4 : (4 : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast h4nat
  simp [vfMid, not_lt.mpr h4]

/-- Exact prime-counting staircase on the reals, constant between integers.
Only x >= 4 is used by the von-Koch target. -/
def vfMidPrimeCount (x : ℝ) : ℝ :=
  (((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime).card : ℝ)

/-- Running midpoint prime-count error. -/
def vfMidPrimeError (x : ℝ) : ℝ :=
  vfMidPrimeCount x - vfMid x

/-- Midpoint quadrature error relative to the repository's Li normalization. -/
def vfMidLiError (x : ℝ) : ℝ :=
  vfMid x - logarithmicIntegralFromTwo x

/-- Classical prime-count discrepancy in the same real-cutoff coordinates. -/
def vfMidPrimeLiError (x : ℝ) : ℝ :=
  vfMidPrimeCount x - logarithmicIntegralFromTwo x

/-- The exact algebraic decomposition: prime-minus-Li is
prime-minus-VF plus VF-minus-Li. -/
theorem vfMidPrimeLiError_eq_primeError_add_liError (x : ℝ) :
    vfMidPrimeLiError x = vfMidPrimeError x + vfMidLiError x := by
  unfold vfMidPrimeLiError vfMidPrimeError vfMidLiError
  ring

/-! ## Midpoint quadrature infrastructure -/

/-- Explicit second derivative of the Li density on the positive side of
the logarithmic singularity. -/
def vfMidInvLogSecond (x : ℝ) : ℝ :=
  (Real.log x + 2) / (x ^ 2 * Real.log x ^ 3)

/-- The second iterated derivative of 1/log is the explicit positive density
used in the midpoint remainder estimate. -/
theorem iteratedDeriv_inv_log_two {x : ℝ} (hx : 1 < x) :
    iteratedDeriv 2 (fun t : ℝ => (Real.log t)⁻¹) x =
      vfMidInvLogSecond x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
    Real.deriv_inv_log]
  have hnum := (hasDerivAt_inv hx0).neg
  have hden := (Real.hasDerivAt_log hx0).pow 2
  have hd := hnum.div hden (pow_ne_zero 2 hlog0)
  rw [hd.deriv]
  unfold vfMidInvLogSecond
  field_simp
  ring

/-- Midpoint-rule error bound derived from Mathlib's C2 trapezoidal-rule
estimate.  The constant 1/8 is deliberately non-sharp; only summability of the
square-band errors is needed downstream. -/
theorem midpoint_rule_error_le_of_c2
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiffOn ℝ 2 f [[a, b]])
    {ζ : ℝ}
    (hζ : ∀ x, |iteratedDerivWithin 2 f [[a, b]] x| ≤ ζ) :
    |(b - a) * f ((a + b) / 2) - ∫ t in a..b, f t| ≤
      |b - a| ^ 3 * ζ / 8 := by
  have h1 := trapezoidal_error_le_of_c2 hf hζ (N := 1) (by norm_num)
  have h2 := trapezoidal_error_le_of_c2 hf hζ (N := 2) (by norm_num)
  have hζ0 : 0 ≤ ζ := (abs_nonneg _).trans (hζ a)
  have hident :
      (b - a) * f ((a + b) / 2) - ∫ t in a..b, f t =
        2 * trapezoidal_error f 2 a b -
          trapezoidal_error f 1 a b := by
    unfold trapezoidal_error trapezoidal_integral
    simp
    ring
  rw [hident, sub_eq_add_neg]
  calc
    |2 * trapezoidal_error f 2 a b + -trapezoidal_error f 1 a b|
        ≤ |2 * trapezoidal_error f 2 a b| +
            |-trapezoidal_error f 1 a b| := abs_add_le _ _
    _ = 2 * |trapezoidal_error f 2 a b| +
          |trapezoidal_error f 1 a b| := by simp
    _ ≤ 2 * (|b - a| ^ 3 * ζ / (12 * (2 : ℝ) ^ 2)) +
          (|b - a| ^ 3 * ζ / (12 * (1 : ℝ) ^ 2)) := by
      gcongr
    _ = |b - a| ^ 3 * ζ / 8 := by ring

/-! ## Frozen analytic statements -/

/-- Unconditional midpoint quadrature bridge to be proved for the concrete
vfMid: the tiled path differs from Li by a globally bounded amount. -/
def VFMidLiBoundedStatement : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧
    ∀ x : ℝ, 4 ≤ x →
      |vfMidLiError x| ≤ B

/-- The sole arithmetic target.

This is the exact von-Koch scale on the running error.  It deliberately asks
for no per-band bound and no stronger log-free root estimate. -/
def VFMidVonKochBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 4 ≤ x →
      |vfMidPrimeError x| ≤
        C * Real.sqrt x * Real.log x

/-- Classical prime-count form of the von-Koch scale, expressed using the same
real prime-count staircase and the repository's logarithmicIntegralFromTwo. -/
def PrimeLiVonKochBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 4 ≤ x →
      |vfMidPrimeLiError x| ≤
        C * Real.sqrt x * Real.log x

/-- Mathlib currently does not expose the classical von-Koch equivalence in
this normalization.  As elsewhere in this repository for the classical Mertens
criterion, package that standard analytic theorem as an explicit interface. -/
structure ClassicalVonKochRHCriterion where
  iff_riemannHypothesis :
    PrimeLiVonKochBoundedStatement ↔ RiemannHypothesisStatement

/-! ## Deterministic transfer from VF_mid to the classical discrepancy -/

/-- On x >= 4, the von-Koch weight sqrt x * log x is bounded below by the
positive constant 2 * log 4. -/
theorem two_log_four_le_sqrt_mul_log {x : ℝ} (hx : 4 ≤ x) :
    2 * Real.log 4 ≤ Real.sqrt x * Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hsqrt : 2 ≤ Real.sqrt x := by
    have hs := Real.sq_sqrt hx0
    have hs0 := Real.sqrt_nonneg x
    nlinarith
  have hlog : Real.log 4 ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hlog0 : 0 ≤ Real.log 4 :=
    (Real.log_pos (by norm_num)).le
  calc
    2 * Real.log 4 ≤ Real.sqrt x * Real.log 4 :=
      mul_le_mul_of_nonneg_right hsqrt hlog0
    _ ≤ Real.sqrt x * Real.log x :=
      mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)

/-- A bounded midpoint quadrature error plus the frozen VF_mid running bound
gives the classical prime-minus-Li von-Koch bound. -/
theorem primeLiVonKochBounded_of_vfMid
    (hquad : VFMidLiBoundedStatement)
    (hvf : VFMidVonKochBoundedStatement) :
    PrimeLiVonKochBoundedStatement := by
  rcases hquad with ⟨B, hB0, hB⟩
  rcases hvf with ⟨C, hC0, hC⟩
  let c : ℝ := 2 * Real.log 4
  have hc0 : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨C + B / c, add_nonneg hC0 (div_nonneg hB0 hc0.le), ?_⟩
  intro x hx
  have hg : c ≤ Real.sqrt x * Real.log x := by
    simpa [c] using two_log_four_le_sqrt_mul_log hx
  have hBg :
      B ≤ (B / c) * (Real.sqrt x * Real.log x) := by
    have hmul := mul_le_mul_of_nonneg_left hg (div_nonneg hB0 hc0.le)
    have hBc : (B / c) * c = B := by
      field_simp [hc0.ne']
    linarith
  calc
    |vfMidPrimeLiError x|
        = |vfMidPrimeError x + vfMidLiError x| := by
            rw [vfMidPrimeLiError_eq_primeError_add_liError]
    _ ≤ |vfMidPrimeError x| + |vfMidLiError x| := abs_add_le _ _
    _ ≤ C * Real.sqrt x * Real.log x + B :=
      add_le_add (hC x hx) (hB x hx)
    _ ≤ (C + B / c) * Real.sqrt x * Real.log x := by
      nlinarith

/-- Once the unconditional quadrature bridge is kernel-checked, the only
remaining hypothesis in this route is VFMidVonKochBoundedStatement. -/
theorem riemannHypothesis_of_vfMidVonKoch
    (criterion : ClassicalVonKochRHCriterion)
    (hquad : VFMidLiBoundedStatement)
    (hvf : VFMidVonKochBoundedStatement) :
    RiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (primeLiVonKochBounded_of_vfMid hquad hvf)

end RHLean.Analysis
