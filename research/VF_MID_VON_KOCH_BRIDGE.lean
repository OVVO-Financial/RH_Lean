import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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

open Set MeasureTheory intervalIntegral
open scoped BigOperators Interval

namespace RHLean.Analysis

/-- The repository normalization of the logarithmic integral, reproduced here
with narrow dependencies so this research file does not depend on the umbrella
`Mathlib` import used by older RHLean modules. -/
def vfMidLogarithmicIntegralFromTwo (x : ℝ) : ℝ :=
  ∫ u in (2 : ℝ)..x, (Real.log u)⁻¹

/-- Mathlib's formal Riemann-hypothesis proposition, exposed locally without
importing the heavier RHLean bridge module. -/
def VFMidRiemannHypothesisStatement : Prop :=
  RiemannHypothesis

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
  (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- Running midpoint prime-count error. -/
def vfMidPrimeError (x : ℝ) : ℝ :=
  vfMidPrimeCount x - vfMid x

/-- Midpoint quadrature error relative to the repository's Li normalization. -/
def vfMidLiError (x : ℝ) : ℝ :=
  vfMid x - vfMidLogarithmicIntegralFromTwo x

/-- Classical prime-count discrepancy in the same real-cutoff coordinates. -/
def vfMidPrimeLiError (x : ℝ) : ℝ :=
  vfMidPrimeCount x - vfMidLogarithmicIntegralFromTwo x

/-- The exact algebraic decomposition: prime-minus-Li is
prime-minus-VF plus VF-minus-Li. -/
theorem vfMidPrimeLiError_eq_primeError_add_liError (x : ℝ) :
    vfMidPrimeLiError x = vfMidPrimeError x + vfMidLiError x := by
  unfold vfMidPrimeLiError vfMidPrimeError vfMidLiError
  ring

/-! ## Midpoint quadrature infrastructure -/

/-- Exact Li mass of a complete square band. -/
def vfMidBandIntegral (r : ℕ) : ℝ :=
  ∫ t in ((r : ℝ) ^ 2)..(((r + 1 : ℕ) : ℝ) ^ 2),
    (Real.log t)⁻¹

/-- Signed midpoint quadrature residual on a complete square band. -/
def vfMidBandQuadratureError (r : ℕ) : ℝ :=
  vfMidBandMass r - vfMidBandIntegral r

/-- Exact Li mass on the live portion of square band R. -/
def vfMidLiveIntegral (R : ℕ) (x : ℝ) : ℝ :=
  ∫ t in ((R : ℝ) ^ 2)..x, (Real.log t)⁻¹

/-- Signed midpoint quadrature residual on the live portion of square band R. -/
def vfMidLiveQuadratureError (R : ℕ) (x : ℝ) : ℝ :=
  (x - (R : ℝ) ^ 2) /
      Real.log (((R : ℝ) ^ 2 + x) / 2) -
    vfMidLiveIntegral R x



/-- Explicit second derivative of the Li density on the positive side of
the logarithmic singularity. -/
def vfMidInvLogSecond (x : ℝ) : ℝ :=
  (Real.log x + 2) / (x ^ 2 * Real.log x ^ 3)

/-- The second iterated derivative of 1/log is the explicit positive density
used in the midpoint remainder estimate. -/
theorem deriv_inv_log_formula {x : ℝ} (hx : 1 < x) :
    deriv (fun t : ℝ => (Real.log t)⁻¹) x =
      -x⁻¹ / Real.log x ^ 2 := by
  have hx0 : x ≠ 0 := by linarith
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  exact ((Real.hasDerivAt_log hx0).inv hlog0).deriv

theorem iteratedDeriv_inv_log_two {x : ℝ} (hx : 1 < x) :
    iteratedDeriv 2 (fun t : ℝ => (Real.log t)⁻¹) x =
      vfMidInvLogSecond x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hev :
      (fun y : ℝ => deriv (fun t : ℝ => (Real.log t)⁻¹) y) =ᶠ[𝓝 x]
        (fun y : ℝ => -y⁻¹ / Real.log y ^ 2) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact deriv_inv_log_formula hy
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
    Filter.EventuallyEq.deriv_eq hev]
  have hnum := (hasDerivAt_inv hx0).neg
  have hden := (Real.hasDerivAt_log hx0).pow 2
  have hd := hnum.div hden (pow_ne_zero 2 hlog0)
  rw [hd.deriv]
  unfold vfMidInvLogSecond
  field_simp [hx0, hlog0]
  ring

/-- The natural-number majorant generated by square-band midpoint
quadrature is summable. -/
theorem summable_nat_inv_div_log_sq :
    Summable (fun r : ℕ => ((r : ℝ)⁻¹ / Real.log (r : ℝ) ^ 2)) := by
  let g : ℝ → ℝ := fun t => t⁻¹ / Real.log t ^ 2
  let f : ℕ → ℝ := fun n => g n
  let F : ℕ → ℝ := fun n => if n = 1 then f 2 else f n
  have hanti : AntitoneOn g (Ici 2) := by
    intro x hx y hy hxy
    have hx2 : (2 : ℝ) ≤ x := hx
    have hy2 : (2 : ℝ) ≤ y := hy
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx2
    have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy2
    have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx2
    have hy1 : 1 < y := lt_of_lt_of_le (by norm_num) hy2
    have hlogx : 0 < Real.log x := Real.log_pos hx1
    have hlogy : 0 < Real.log y := Real.log_pos hy1
    have hinv : y⁻¹ ≤ x⁻¹ := by
      exact (inv_le_inv₀ hypos hxpos).2 hxy
    have hlog : Real.log x ≤ Real.log y :=
      Real.log_le_log hxpos hxy
    have hsquare : Real.log x ^ 2 ≤ Real.log y ^ 2 := by
      exact pow_le_pow_left₀ hlogx.le hlog 2
    have hinvSquare : (Real.log y ^ 2)⁻¹ ≤ (Real.log x ^ 2)⁻¹ := by
      exact
        (inv_le_inv₀ (sq_pos_of_pos hlogy) (sq_pos_of_pos hlogx)).2 hsquare
    dsimp [g]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul hinv hinvSquare (inv_nonneg.mpr (sq_nonneg _))
      (inv_nonneg.mpr hxpos.le)
  have hFnonneg : ∀ n, 0 ≤ F n := by
    intro n
    dsimp [F, f, g]
    split_ifs
    · positivity
    · exact div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (sq_nonneg _)
  have hFmono :
      ∀ ⦃m n⦄, 0 < m → m ≤ n → F n ≤ F m := by
    intro m n hm hmn
    by_cases hm1 : m = 1
    · subst m
      by_cases hn1 : n = 1
      · subst n
        rfl
      · have hn2 : 2 ≤ n := by omega
        have hreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        have hanti' := hanti (show (2 : ℝ) ∈ Ici 2 by simp)
          (show (n : ℝ) ∈ Ici 2 by simpa) hreal
        simpa [F, f, hn1] using hanti'
    · have hm2 : 2 ≤ m := by omega
      have hn2 : 2 ≤ n := hm2.trans hmn
      have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      have hanti' := hanti
        (show (m : ℝ) ∈ Ici 2 by exact_mod_cast hm2)
        (show (n : ℝ) ∈ Ici 2 by exact_mod_cast hn2) hcast
      have hn1 : n ≠ 1 := by omega
      simpa [F, f, hm1, hn1] using hanti'
  have hp :
      Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    summable_one_div_nat_pow.mpr (by norm_num)
  have hpShift :
      Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr hp
  have hlog2 :
      Real.log (2 : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hcondShift :
      Summable (fun k : ℕ =>
        (2 : ℝ) ^ (k + 1) * F (2 ^ (k + 1))) := by
    have hs :=
      hpShift.mul_left ((Real.log (2 : ℝ))⁻²)
    refine hs.congr ?_
    intro k
    have hpow : (2 : ℕ) ^ (k + 1) ≠ 1 := by
      have hkpos : 0 < k + 1 := by omega
      have hge : 2 ≤ (2 : ℕ) ^ (k + 1) := by
        exact Nat.le_pow hkpos (by norm_num)
      omega
    simp [F, f, g, hpow, Nat.cast_pow, Real.log_pow]
    field_simp [hlog2]
    ring
  have hcond :
      Summable (fun k : ℕ => (2 : ℝ) ^ k * F (2 ^ k)) :=
    (summable_nat_add_iff 1).mp (by
      simpa [Nat.cast_add, Nat.cast_one] using hcondShift)
  have hFs : Summable F :=
    (summable_condensed_iff_of_nonneg hFnonneg hFmono).mp hcond
  have hFshift : Summable (fun n : ℕ => F (n + 2)) :=
    (summable_nat_add_iff 2).mpr hFs
  have hfshift : Summable (fun n : ℕ => f (n + 2)) := by
    refine hFshift.congr ?_
    intro n
    simp [F]
  have hfs : Summable f :=
    (summable_nat_add_iff 2).mp hfshift
  simpa [f, g] using hfs

/-- One-trapezoid approximation used internally for the midpoint estimate. -/
private noncomputable def vfMidTrapIntegral
    (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a) / 2 * (f a + f b)

/-- Signed one-trapezoid error. -/
private noncomputable def vfMidTrapError
    (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  vfMidTrapIntegral f a b - ∫ x in a..b, f x

@[simp] private theorem vfMidTrapError_same
    (f : ℝ → ℝ) (a : ℝ) :
    vfMidTrapError f a a = 0 := by
  simp [vfMidTrapError, vfMidTrapIntegral]

/-- C2 one-trapezoid error bound on an ordered nonempty interval.
This is the only numerical-analysis estimate needed to build the midpoint
quadrature bridge on the repository's pinned Mathlib 4.24. -/
private theorem vfMidTrapError_le_of_lt
    {f : ℝ → ℝ} {ζ a b : ℝ}
    (hab : a < b)
    (hdf : DifferentiableOn ℝ f (Icc a b))
    (hddf : DifferentiableOn ℝ (derivWithin f (Icc a b)) (Icc a b))
    (hbound : ∀ x, |iteratedDerivWithin 2 f (Icc a b) x| ≤ ζ) :
    |vfMidTrapError f a b| ≤ (b - a) ^ 3 * ζ / 12 := by
  let g (t : ℝ) := vfMidTrapError f a t
  let dg (t : ℝ) :=
    (1 / 2) * (f a + f t) +
      ((t - a) / 2) * (derivWithin f (Icc a b) t) - f t
  let ddg (t : ℝ) :=
    ((t - a) / 2) * (iteratedDerivWithin 2 f (Icc a b) t)
  have hdg (y : ℝ) (hy : y ∈ Icc a b) :
      HasDerivWithinAt g (dg y) (Icc a b) y := by
    unfold g vfMidTrapError vfMidTrapIntegral
    refine fun_sub
      (fun_mul
        (div_const (sub_const _ (hasDerivWithinAt_id _ _)) _)
        (const_add _ (hdf y hy).hasDerivWithinAt))
      ?_
    have := Fact.mk hy
    apply integral_hasDerivWithinAt_right
    · exact
        (hdf.continuousOn.mono (Icc_subset_Icc le_rfl hy.2)).intervalIntegrable_of_Icc hy.1
    · exact hdf.continuousOn.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc y
    · exact hdf.continuousOn.continuousWithinAt hy
  have hddg (y : ℝ) (hy : y ∈ Icc a b) :
      HasDerivWithinAt dg (ddg y) (Icc a b) y := by
    let dfy := derivWithin f (Icc a b) y
    rw [(by ring :
      ddg y = (1 / 2) * dfy + ((1 / 2) * dfy + ddg y) - dfy)]
    refine fun_sub
      (fun_add
        (const_mul _ (const_add _ (hdf y hy).hasDerivWithinAt))
        (fun_mul (div_const (sub_const _ (hasDerivWithinAt_id _ _)) _) ?_))
      (hdf y hy).hasDerivWithinAt
    rw [iteratedDerivWithin_eq_iterate]
    exact (hddf y hy).hasDerivWithinAt
  have hddgBound (x : ℝ) (hx : x ∈ Icc a b) :
      |ddg x| ≤ (ζ / 2) * (x - a) := by
    simp_rw [ddg, abs_mul, abs_div, abs_two]
    grw [hbound x, abs_of_nonneg (sub_nonneg.mpr hx.1), div_mul_comm]
  have key {φ φ' : ℝ → ℝ}
      (hderiv : ∀ x ∈ Icc a b,
        HasDerivWithinAt φ (φ' x) (Icc a b) x)
      (hzero : φ a = 0)
      {cc : ℝ} {n : ℕ}
      (hφ : ∀ t ∈ Icc a b, |φ' t| ≤ cc * (t - a) ^ n) :
      ∀ t ∈ Icc a b,
        |φ t| ≤ cc / (n + 1) * (t - a) ^ (n + 1) := by
    intro t ht
    have hB (x : ℝ) :
        HasDerivAt
          (fun y => cc / (n + 1) * (y - a) ^ (n + 1))
          (cc * (x - a) ^ n) x := by
      convert!
        (hasDerivAt_const x (cc / (n + 1))).mul
          (((hasDerivAt_id x).sub (hasDerivAt_const x a)).pow (n + 1)) using 1
      simp [sub_eq_add_neg, field]
    simpa [Real.norm_eq_abs, hzero] using
      image_norm_le_of_norm_deriv_right_le_deriv_boundary
        (fun x hx => (hderiv x hx).continuousWithinAt)
        (fun x hx => by grind [Icc_mem_nhdsGE_of_mem, mono_of_mem_nhdsWithin])
        (by simp [hzero]) hB
        (fun x hx => hφ x (Ico_subset_Icc_self hx)) ht
  exact
    (key hdg (vfMidTrapError_same f a)
      (key hddg (by ring) (fun x hx => by
        simpa [pow_one] using hddgBound x hx))
      b ⟨hab.le, le_rfl⟩).trans_eq (by ring_nf)

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
    PrimeLiVonKochBoundedStatement ↔ VFMidRiemannHypothesisStatement

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
    VFMidRiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (primeLiVonKochBounded_of_vfMid hquad hvf)

end RHLean.Analysis
