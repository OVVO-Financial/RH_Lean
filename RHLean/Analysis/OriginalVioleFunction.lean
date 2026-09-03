import Mathlib
import RHLean.Analysis.DynamicVioleBaseline
import RHLean.Analysis.NativePNTLambdaRecipInterval
import RHLean.Analysis.NativePNTNormalizedReciprocal

/-!
# Original parameter-free Viole function

This module formalizes the original Viole Function exactly as published.  It
has no fitted coefficients and does not use `pi(x)` as an input.

For a real input `x`, set

```text
N(x) = floor(sqrt(x))^2,
t(x) = log_10(x),
C(x) = (1 + 1 / t(x))^(1 + t(x)).
```

The continuous core of the original estimator is

```text
VF(x) = N(x) / log(N(x) / C(x)).
```

The published R implementation then applies `floor` and truncates below at
zero.  The dynamic object is the parameter-free correction `C(x)`, not a pair
of calibrated coefficients.

The same estimator has an implied logarithmic base.  Its normalized form is

```text
log b_VF(x) = 1 / (1 - log(C(x)) / log(N(x))).
```

Consequently, once the correction ratio tends to zero, the implied base tends
to `exp 1 = e`.  The final theorem below isolates this elementary analytic
step from the separate limit proofs for the Euler sequence and square-floor
numerator.
-/

noncomputable section

open Filter Topology
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Proof

/-- Base-ten logarithm written by change of base. -/
def originalVFLog10 (x : ℝ) : ℝ :=
  Real.log x / Real.log 10

/-- The squared floor of the square root used by the published VF numerator. -/
def originalVFSquareNumerator (x : ℝ) : ℝ :=
  ((Nat.floor (Real.sqrt x) : ℕ) : ℝ) ^ 2

/-- The parameter-free Euler correction from the original VF. -/
def originalVFEulerCorrection (x : ℝ) : ℝ :=
  let t := originalVFLog10 x
  Real.rpow (1 + 1 / t) (1 + t)

/-- The natural-log denominator appearing in the original VF. -/
def originalVFDenominator (x : ℝ) : ℝ :=
  Real.log (originalVFSquareNumerator x / originalVFEulerCorrection x)

/-- The continuous core of the published estimator, before flooring and
truncation at zero. -/
def originalVFContinuous (x : ℝ) : ℝ :=
  originalVFSquareNumerator x / originalVFDenominator x

/-- The exact integer-valued post-processing used in the published R code. -/
def originalVF (x : ℝ) : ℕ :=
  Nat.floor (max 0 (originalVFContinuous x))

/-- Ratio controlling the implied dynamic logarithmic base. -/
def originalVFCorrectionRatio (x : ℝ) : ℝ :=
  Real.log (originalVFEulerCorrection x) /
    Real.log (originalVFSquareNumerator x)

/-- The implied logarithm of the dynamic base of the original VF. -/
def originalVFImpliedLogBase (x : ℝ) : ℝ :=
  1 / (1 - originalVFCorrectionRatio x)

/-- The implied dynamic logarithmic base of the original VF. -/
def originalVFImpliedBase (x : ℝ) : ℝ :=
  Real.exp (originalVFImpliedLogBase x)

/-- The original VF implied base is positive at every input. -/
theorem originalVFImpliedBase_pos (x : ℝ) :
    0 < originalVFImpliedBase x := by
  exact Real.exp_pos _

/-- The analytic final step: if the correction contributes a vanishing share
of the main logarithm, then the original VF's implied base tends to `e`. -/
theorem originalVFImpliedBase_tendsto_e
    (hRatio : Tendsto originalVFCorrectionRatio atTop (𝓝 0)) :
    Tendsto originalVFImpliedBase atTop (𝓝 (Real.exp 1)) := by
  have hcont : ContinuousAt (fun z : ℝ => Real.exp (1 / (1 - z))) 0 := by
    fun_prop (disch := norm_num)
  change Tendsto (fun x : ℝ => Real.exp (1 / (1 - originalVFCorrectionRatio x)))
    atTop (𝓝 (Real.exp 1))
  have htarget : Real.exp (1 / (1 - (0 : ℝ))) = Real.exp 1 := by
    norm_num
  simpa only [Function.comp_apply, htarget] using hcont.tendsto.comp hRatio

/-! ## Direct normalized cutoff advancement on the Viole clock -/

/-- Normalized reciprocal average restricted to divisors at most `M`. -/
def nativePNTNormalizedRecipAveragePrefix
    (N M : Nat) : Real :=
  ∑ d ∈ Finset.Icc 1 M,
    nativePNTNormalizedRecipWeight d * nativePNTNormalizedError (N / d)

/-- Normalized reciprocal average carried by the divisor annulus `(M,L]`. -/
def nativePNTNormalizedRecipAverageAnnulus
    (N M L : Nat) : Real :=
  ∑ d ∈ Finset.Ioc M L,
    nativePNTNormalizedRecipWeight d * nativePNTNormalizedError (N / d)

/-- Exact prefix/annulus decomposition of the fixed-reciprocal normalized
Selberg average. -/
theorem nativePNTNormalizedRecipAverage_eq_prefix_add_annulus
    (N M : Nat) (hM : 1 ≤ M) (hMN : M ≤ N) :
    nativePNTNormalizedRecipAverage N =
      nativePNTNormalizedRecipAveragePrefix N M +
        nativePNTNormalizedRecipAverageAnnulus N M N := by
  unfold nativePNTNormalizedRecipAverage
    nativePNTNormalizedRecipAveragePrefix
    nativePNTNormalizedRecipAverageAnnulus
  have hset :
      Finset.Icc 1 N = Finset.Icc 1 M ∪ Finset.Ioc M N := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdis : Disjoint (Finset.Icc 1 M) (Finset.Ioc M N) := by
    rw [Finset.disjoint_left]
    intro d hdPrefix hdAnnulus
    rw [Finset.mem_Icc] at hdPrefix
    rw [Finset.mem_Ioc] at hdAnnulus
    omega
  rw [hset, Finset.sum_union hdis]

@[simp] theorem nativePNTNormalizedError_one :
    nativePNTNormalizedError 1 = -1 := by
  rw [nativePNTNormalizedError_eq_psi_div_sub_one 1 (by norm_num)]
  simp [nativePsi]

/-- At a subdoubling endpoint `L < 2*M`, every new divisor `M < d <= L`
has quotient exactly one.  The newly opened divisor annulus is therefore the
negative reciprocal von-Mangoldt interval mass. -/
theorem nativePNTNormalizedRecipAverageAnnulus_eq_neg_lambdaRecipInterval_of_subdoubling
    (M L : Nat) (hsub : L < 2 * M) :
    nativePNTNormalizedRecipAverageAnnulus L M L =
      -nativeLambdaRecipInterval M L := by
  unfold nativePNTNormalizedRecipAverageAnnulus nativeLambdaRecipInterval
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdI := Finset.mem_Ioc.mp hd
  have hlo : 1 * d ≤ L := by simpa using hdI.2
  have hhi : L < (1 + 1) * d := by
    have htwo : 2 * M < 2 * d := Nat.mul_lt_mul_left 2 hdI.1
    omega
  have hdiv : L / d = 1 := Nat.div_eq_of_lt_le hlo hhi
  rw [hdiv, nativePNTNormalizedError_one]
  unfold nativePNTNormalizedRecipWeight
  ring

/-- Endpoint form of the adjacent-square normalized socket. -/
theorem nativePNTNormalizedRecipAverage_endpoint_eq_prefix_sub_interval_of_subdoubling
    (M L : Nat) (hM : 1 ≤ M) (hML : M ≤ L) (hsub : L < 2 * M) :
    nativePNTNormalizedRecipAverage L =
      nativePNTNormalizedRecipAveragePrefix L M -
        nativeLambdaRecipInterval M L := by
  rw [nativePNTNormalizedRecipAverage_eq_prefix_add_annulus L M hM hML,
    nativePNTNormalizedRecipAverageAnnulus_eq_neg_lambdaRecipInterval_of_subdoubling
      M L hsub]
  ring

/-- The integer cutoff underneath the `r`th Viole square midpoint. -/
def violeClockCutoff (r : Nat) : Nat := r ^ 2 + r

/-- Consecutive Viole cutoffs are increasing. -/
theorem violeClockCutoff_le_succ (r : Nat) :
    violeClockCutoff r ≤ violeClockCutoff (r + 1) := by
  unfold violeClockCutoff
  have hsquare : r ^ 2 ≤ (r + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  exact Nat.add_le_add hsquare (by omega)

/-- From `r >= 3` onward, consecutive Viole cutoffs are strictly subdoubling. -/
theorem violeClockCutoff_succ_lt_two_mul
    (r : Nat) (hr : 3 ≤ r) :
    violeClockCutoff (r + 1) < 2 * violeClockCutoff r := by
  have hrpos : 0 < r := by omega
  have h2r : 2 * r < r * r :=
    Nat.mul_lt_mul_of_pos_right (by omega : 2 < r) hrpos
  have hsmall : r + 2 ≤ 2 * r := by omega
  have hrr : r + 2 < r * r := hsmall.trans_lt h2r
  unfold violeClockCutoff
  calc
    (r + 1) ^ 2 + (r + 1) = r ^ 2 + 2 * r + (r + 2) := by ring
    _ < r ^ 2 + 2 * r + r ^ 2 := Nat.add_lt_add_left hrr (r ^ 2 + 2 * r)
    _ = 2 * (r ^ 2 + r) := by ring

/-- Exact adjacent-square specialization of the nonzero normalized divisor
socket. -/
theorem violeClockNormalizedRecipAverageAnnulus_eq_neg_interval
    (r : Nat) (hr : 3 ≤ r) :
    nativePNTNormalizedRecipAverageAnnulus
        (violeClockCutoff (r + 1))
        (violeClockCutoff r)
        (violeClockCutoff (r + 1)) =
      -nativeLambdaRecipInterval
        (violeClockCutoff r) (violeClockCutoff (r + 1)) := by
  exact
    nativePNTNormalizedRecipAverageAnnulus_eq_neg_lambdaRecipInterval_of_subdoubling
      (violeClockCutoff r) (violeClockCutoff (r + 1))
      (violeClockCutoff_succ_lt_two_mul r hr)

/-- Raising the physical cutoff never invalidates a true tail with the same
slope. -/
theorem primeSieveStateDependentSelbergTailAbove_mono_cutoff
    (M L : Nat) (alpha : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hML : M ≤ L) :
    PrimeSieveStateDependentSelbergTailAbove L alpha := by
  rcases htail with ⟨hM2, halpha, htail⟩
  exact ⟨hM2.trans hML, halpha, fun q hLq => htail q (hML.trans hLq)⟩

/-- Convert a true PNT tail to its normalized-error form. -/
theorem primeSieveStateDependentSelbergTailAbove_normalizedError_abs_le
    (M N : Nat) (alpha : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hMN : M ≤ N) :
    |nativePNTNormalizedError N| ≤ alpha := by
  have hNpos : (0 : Real) < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  have hraw := htail.2.2 N hMN
  unfold nativePNTNormalizedError
  rw [abs_div, abs_of_pos hNpos]
  exact (div_le_iff₀ hNpos).2 hraw

/-- Sign-conditioned direct cutoff exclusion.  Under the old tail, the only
states to eliminate are the two extremal strips
`alpha' < e(N) <= alpha` and `-alpha <= e(N) < -alpha'`. -/
def NativePNTNormalizedDirectCutoffExclusion
    (M L : Nat) (alpha alpha' : Real) : Prop :=
  3 ≤ L ∧ M ≤ L ∧ 0 < alpha' ∧ alpha' ≤ alpha ∧
    ∀ N : Nat, L ≤ N →
      (alpha' < nativePNTNormalizedError N →
        nativePNTNormalizedError N ≤ alpha →
          nativePNTNormalizedRecipSelbergConstant -
              alpha' * Real.log (N : Real) ≤
            nativePNTNormalizedRecipAverage N) ∧
      (nativePNTNormalizedError N < -alpha' →
        -alpha ≤ nativePNTNormalizedError N →
          nativePNTNormalizedRecipAverage N ≤
            alpha' * Real.log (N : Real) -
              nativePNTNormalizedRecipSelbergConstant)

/-- The signed exclusion upgrades an old tail directly to the new slope. -/
theorem nativePNTNormalizedDirectCutoffExclusion_step
    (M L : Nat) (alpha alpha' : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hexcl : NativePNTNormalizedDirectCutoffExclusion M L alpha alpha') :
    PrimeSieveStateDependentSelbergTailAbove L alpha' := by
  rcases hexcl with ⟨hL3, hML, halpha', _hale, hexcl⟩
  refine ⟨by omega, halpha', ?_⟩
  intro N hLN
  have hN3 : 3 ≤ N := hL3.trans hLN
  have hNpos : (0 : Real) < (N : Real) := by
    exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hold :=
    primeSieveStateDependentSelbergTailAbove_normalizedError_abs_le
      M N alpha htail (hML.trans hLN)
  have holdBounds := abs_le.mp hold
  have hrec := nativePNTNormalized_signed_recip_recurrence_abs_le N hN3
  have hrecBounds := abs_le.mp hrec
  have hbar := hexcl N hLN
  have hnorm : |nativePNTNormalizedError N| ≤ alpha' := by
    rw [abs_le]
    constructor
    · by_contra hneg
      have hextreme : nativePNTNormalizedError N < -alpha' :=
        lt_of_not_ge hneg
      have havg := hbar.2 hextreme holdBounds.1
      have hmul :
          nativePNTNormalizedError N * Real.log (N : Real) <
            (-alpha') * Real.log (N : Real) :=
        mul_lt_mul_of_pos_right hextreme hlog
      linarith [hrecBounds.1, havg, hmul]
    · by_contra hpos
      have hextreme : alpha' < nativePNTNormalizedError N :=
        lt_of_not_ge hpos
      have havg := hbar.1 hextreme holdBounds.2
      have hmul :
          alpha' * Real.log (N : Real) <
            nativePNTNormalizedError N * Real.log (N : Real) :=
        mul_lt_mul_of_pos_right hextreme hlog
      linarith [hrecBounds.2, havg, hmul]
  unfold nativePNTNormalizedError at hnorm
  rw [abs_div, abs_of_pos hNpos] at hnorm
  exact (div_le_iff₀ hNpos).1 hnorm

/-- Exact scalar slope whose reciprocal square increases by `delta`. -/
def nativePNTReciprocalSquareSlope
    (alpha delta : Real) : Real :=
  alpha / Real.sqrt (1 + delta * alpha ^ 2)

theorem nativePNTReciprocalSquareSlope_pos
    (alpha delta : Real) (halpha : 0 < alpha) (hdelta : 0 ≤ delta) :
    0 < nativePNTReciprocalSquareSlope alpha delta := by
  have hins : 0 < 1 + delta * alpha ^ 2 := by
    nlinarith [mul_nonneg hdelta (sq_nonneg alpha)]
  exact div_pos halpha (Real.sqrt_pos.2 hins)

theorem nativePNTReciprocalSquareSlope_le
    (alpha delta : Real) (halpha : 0 < alpha) (hdelta : 0 ≤ delta) :
    nativePNTReciprocalSquareSlope alpha delta ≤ alpha := by
  have hins : 1 ≤ 1 + delta * alpha ^ 2 := by
    nlinarith [mul_nonneg hdelta (sq_nonneg alpha)]
  have hsqrt : 1 ≤ Real.sqrt (1 + delta * alpha ^ 2) := by
    simpa using Real.sqrt_le_sqrt hins
  have hsqrtPos : 0 < Real.sqrt (1 + delta * alpha ^ 2) :=
    lt_of_lt_of_le zero_lt_one hsqrt
  unfold nativePNTReciprocalSquareSlope
  apply (div_le_iff₀ hsqrtPos).2
  have hmul := mul_le_mul_of_nonneg_left hsqrt halpha.le
  simpa using hmul

/-- The reciprocal-square gain of the scalar update is exactly `delta`. -/
theorem nativePNTReciprocalSquareSlope_inv_sq_sub
    (alpha delta : Real) (halpha : 0 < alpha) (hdelta : 0 ≤ delta) :
    1 / (nativePNTReciprocalSquareSlope alpha delta) ^ 2 -
        1 / alpha ^ 2 = delta := by
  have hins0 : 0 ≤ 1 + delta * alpha ^ 2 := by
    nlinarith [mul_nonneg hdelta (sq_nonneg alpha)]
  have hins : 0 < 1 + delta * alpha ^ 2 := by
    nlinarith [mul_nonneg hdelta (sq_nonneg alpha)]
  have hsqrtSq :
      (Real.sqrt (1 + delta * alpha ^ 2)) ^ 2 =
        1 + delta * alpha ^ 2 := Real.sq_sqrt hins0
  have hsqrtPos : 0 < Real.sqrt (1 + delta * alpha ^ 2) :=
    Real.sqrt_pos.2 hins
  have halpha0 : alpha ≠ 0 := ne_of_gt halpha
  have hsqrt0 : Real.sqrt (1 + delta * alpha ^ 2) ≠ 0 :=
    ne_of_gt hsqrtPos
  unfold nativePNTReciprocalSquareSlope
  field_simp [halpha0, hsqrt0]
  nlinarith [hsqrtSq]

/-- One exact reciprocal-square direct cutoff step. -/
theorem nativePNTReciprocalSquareDirectCutoff_step
    (M L : Nat) (alpha delta : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hdelta : 0 ≤ delta)
    (hexcl : NativePNTNormalizedDirectCutoffExclusion
      M L alpha (nativePNTReciprocalSquareSlope alpha delta)) :
    PrimeSieveStateDependentSelbergTailAbove
        L (nativePNTReciprocalSquareSlope alpha delta) ∧
      nativePNTReciprocalSquareSlope alpha delta ≤ alpha ∧
      1 / (nativePNTReciprocalSquareSlope alpha delta) ^ 2 -
          1 / alpha ^ 2 = delta := by
  have halpha : 0 < alpha := htail.2.1
  exact ⟨
    nativePNTNormalizedDirectCutoffExclusion_step
      M L alpha (nativePNTReciprocalSquareSlope alpha delta) htail hexcl,
    nativePNTReciprocalSquareSlope_le alpha delta halpha hdelta,
    nativePNTReciprocalSquareSlope_inv_sq_sub alpha delta halpha hdelta⟩

/-- Signed gain requested from one Viole block before leakage. -/
def violeClockBlockReciprocalSquareGain
    (c : Real) (eps : Nat → Real) (r : Nat) : Real :=
  c * (dynamicVioleAnchor (r + 1) - dynamicVioleAnchor r) - eps r

/-- Remaining direct arithmetic law.  Positive-gain blocks must exclude the
old-tail extremal strip in the normalized signed recurrence. -/
def VioleClockSignedNormalizedDirectCutoffLaw
    (r0 : Nat) (c : Real) (eps : Nat → Real) : Prop :=
  3 ≤ r0 ∧ 0 < c ∧
    ∀ (r : Nat) (alpha : Real),
      r0 ≤ r →
      PrimeSieveStateDependentSelbergTailAbove (violeClockCutoff r) alpha →
      0 < violeClockBlockReciprocalSquareGain c eps r →
      NativePNTNormalizedDirectCutoffExclusion
        (violeClockCutoff r) (violeClockCutoff (r + 1)) alpha
        (nativePNTReciprocalSquareSlope alpha
          (violeClockBlockReciprocalSquareGain c eps r))

/-- A direct normalized exclusion law implies the frozen #551 reciprocal-square
coupling and bypasses `CubicGainFromTo` completely. -/
theorem violeClockReciprocalSquareCoupling_of_signedNormalizedDirectCutoffLaw
    (r0 : Nat) (c : Real) (eps : Nat → Real)
    (hlaw : VioleClockSignedNormalizedDirectCutoffLaw r0 c eps) :
    VioleClockReciprocalSquareCoupling r0 c eps := by
  rcases hlaw with ⟨hr0, hc, hlaw⟩
  refine ⟨by omega, hc, ?_⟩
  intro r alpha hr htail
  have hML := violeClockCutoff_le_succ r
  have htailCut :
      PrimeSieveStateDependentSelbergTailAbove (violeClockCutoff (r + 1)) alpha :=
    primeSieveStateDependentSelbergTailAbove_mono_cutoff
      (violeClockCutoff r) (violeClockCutoff (r + 1)) alpha htail hML
  let delta : Real := violeClockBlockReciprocalSquareGain c eps r
  by_cases hdelta : 0 < delta
  · have hexcl := hlaw r alpha hr htail (by simpa [delta] using hdelta)
    have hstep := nativePNTReciprocalSquareDirectCutoff_step
      (violeClockCutoff r) (violeClockCutoff (r + 1)) alpha delta htail
      hdelta.le (by simpa [delta] using hexcl)
    refine ⟨nativePNTReciprocalSquareSlope alpha delta, hstep.1, hstep.2.1, ?_⟩
    have hgain := hstep.2.2
    simpa [delta, violeClockCutoff, violeClockBlockReciprocalSquareGain] using
      hgain.ge
  · have hdeltaNonpos : delta ≤ 0 := le_of_not_gt hdelta
    refine ⟨alpha, ?_, le_rfl, ?_⟩
    · simpa [violeClockCutoff] using htailCut
    · have hzero : 1 / alpha ^ 2 - 1 / alpha ^ 2 = 0 := by ring
      rw [hzero]
      simpa [delta, violeClockBlockReciprocalSquareGain] using hdeltaNonpos

end RHLean.Analysis