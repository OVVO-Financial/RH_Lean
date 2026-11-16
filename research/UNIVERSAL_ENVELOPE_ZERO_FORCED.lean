import «research.UNIVERSAL_ENVELOPE_KERNEL»
import PrimeNumberTheoremAnd.ZetaBounds

/-!
# A zeta zero forces the actual historical envelope

The only analytic input is PNT+'s proved Euler-summation formula and its
absolute remainder estimate on `Re(s)>0`.  At an actual zero, the complete
kernel is bounded.  Finite Möbius inversion and Abel summation then force
historical Mertens amplitude at every sufficiently large scale.

The constants below are deliberately coarse.  They depend on the specified
zero and never on the historical cutoff.  There is no RH assumption,
simple-zero assumption, derivative-of-zeta denominator, or assumed Mertens
growth estimate in this file.
-/

set_option maxHeartbeats 1500000

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators Topology
open Complex Finset Set Filter MeasureTheory

namespace RHLean.Analysis.UniversalEnvelope

/-- The bounded-at-a-zero kernel seed. -/
def zeroSeed (ρ : ℂ) (u : ℝ) : ℂ := (1 - ρ) * (u : ℂ) ^ ρ - 1

/-- Its logarithmic primitive, normalized to vanish at one. -/
def zeroPotential (ρ : ℂ) (u : ℝ) : ℂ :=
  (1 - ρ) / ρ * ((u : ℂ) ^ ρ - 1) - (Real.log u : ℂ)

@[simp] theorem zeroPotential_one (ρ : ℂ) : zeroPotential ρ 1 = 0 := by
  simp [zeroPotential]

theorem zeroPotential_hasDerivAt {ρ : ℂ} (hρ : ρ ≠ 0) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (zeroPotential ρ) (zeroSeed ρ u / (u : ℂ)) u := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hp := (hasDerivAt_ofReal_cpow_const hu.ne' hρ).sub_const 1
  have hl : HasDerivAt (fun v : ℝ => (Real.log v : ℂ))
      (1 / (u : ℂ)) u := by
    simpa only [one_div, Complex.ofReal_inv] using! (Real.hasDerivAt_log hu.ne').ofReal_comp
  have hd := (hp.const_mul ((1 - ρ) / ρ)).sub hl
  have hcoef : (1 - ρ) / ρ * (ρ * (u : ℂ) ^ (ρ - 1)) - 1 / (u : ℂ) =
      zeroSeed ρ u / (u : ℂ) := by
    rw [Complex.cpow_sub _ _ huC, Complex.cpow_one]
    unfold zeroSeed
    field_simp [hρ, huC]
  simpa only [zeroPotential, hcoef] using! hd

theorem zeroSeed_kernel_formula (ρ : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    divisorKernel (zeroSeed ρ) u =
      (1 - ρ) * (u : ℂ) ^ ρ *
        (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, 1 / (n : ℂ) ^ ρ) - (⌊u⌋₊ : ℂ) := by
  classical
  unfold divisorKernel
  calc
    (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, zeroSeed ρ (u / n)) =
      ∑ n ∈ Finset.Icc 1 ⌊u⌋₊,
        ((1 - ρ) * (u : ℂ) ^ ρ * (1 / (n : ℂ) ^ ρ) - 1) := by
      apply Finset.sum_congr rfl
      intro n hn
      unfold zeroSeed
      rw [Complex.ofReal_div,
        Complex.div_cpow_ofReal_nonneg hu (Nat.cast_nonneg n)]
      simp only [Complex.ofReal_natCast]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp

private theorem zeta_prefix_Icc_eq_range {ρ : ℂ} (hρ : ρ ≠ 0) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ ρ) =
      ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ρ := by
  rw [Nat.range_succ_eq_Icc_zero,
    ← Finset.insert_Icc_add_one_left_eq_Icc N.zero_le,
    Finset.sum_insert (by aesop)]
  simp [hρ]

/-- A convenient explicit bound for the integer-cutoff kernel. -/
def zeroKernelIntegerConstant (ρ : ℂ) : ℝ :=
  ‖1 - ρ‖ * (1 + ‖ρ‖ / ρ.re)

theorem zeroSeed_kernel_nat_norm_le {ρ : ℂ} (hzero : riemannZeta ρ = 0)
    (hβ : 0 < ρ.re) (hρ1 : ρ ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖divisorKernel (zeroSeed ρ) (N : ℝ)‖ ≤ zeroKernelIntegerConstant ρ := by
  have hρ0 : ρ ≠ 0 := Complex.ne_zero_of_re_pos hβ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hone : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr hρ1.symm
  let S : ℂ := ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ρ
  let J : ℂ := ∫ x in Set.Ioi (N : ℝ),
    (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (ρ + 1)
  have hJ : ‖J‖ ≤ (N : ℝ) ^ (-ρ.re) / ρ.re := by
    simpa only [Complex.re_add_im] using
      (ZetaBnd_aux1b N hN (σ := ρ.re) (t := ρ.im) hβ)
  have hz := Zeta0EqZeta (N := N) (by omega) hβ hρ1
  rw [hzero] at hz
  change S + (-(N : ℂ) ^ (1 - ρ)) / (1 - ρ) +
    (-(N : ℂ) ^ (-ρ)) / 2 + ρ * J = 0 at hz
  have hS : S = (N : ℂ) ^ (1 - ρ) / (1 - ρ) +
      (N : ℂ) ^ (-ρ) / 2 - ρ * J := by
    simp only [neg_div] at hz
    linear_combination hz
  have hmain : (1 - ρ) * (N : ℂ) ^ ρ *
      ((N : ℂ) ^ (1 - ρ) / (1 - ρ)) = (N : ℂ) := by
    have hp : (N : ℂ) ^ ρ * (N : ℂ) ^ (1 - ρ) = (N : ℂ) := by
      rw [← Complex.cpow_add _ _ hNC]
      rw [show ρ + (1 - ρ) = 1 by ring, Complex.cpow_one]
    calc
      (1 - ρ) * (N : ℂ) ^ ρ * ((N : ℂ) ^ (1 - ρ) / (1 - ρ)) =
          (N : ℂ) ^ ρ * (N : ℂ) ^ (1 - ρ) := by field_simp [hone]
      _ = (N : ℂ) := hp
  have hcancel : (N : ℂ) ^ ρ * (N : ℂ) ^ (-ρ) = 1 := by
    rw [← Complex.cpow_add _ _ hNC]
    simp
  have hrepr : divisorKernel (zeroSeed ρ) (N : ℝ) =
      (1 - ρ) / 2 - (1 - ρ) * ρ * (N : ℂ) ^ ρ * J := by
    rw [zeroSeed_kernel_formula ρ hNpos.le, Nat.floor_natCast,
      zeta_prefix_Icc_eq_range hρ0]
    change (1 - ρ) * (N : ℂ) ^ ρ * S - N = _
    rw [hS]
    calc
      (1 - ρ) * (N : ℂ) ^ ρ *
          ((N : ℂ) ^ (1 - ρ) / (1 - ρ) + (N : ℂ) ^ (-ρ) / 2 - ρ * J) - N =
        (1 - ρ) * (N : ℂ) ^ ρ * ((N : ℂ) ^ (1 - ρ) / (1 - ρ)) +
          (1 - ρ) * ((N : ℂ) ^ ρ * (N : ℂ) ^ (-ρ)) / 2 -
          (1 - ρ) * ρ * (N : ℂ) ^ ρ * J - N := by ring
      _ = _ := by rw [hmain, hcancel]; ring
  have hnormPow : ‖(N : ℂ) ^ ρ‖ = (N : ℝ) ^ ρ.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hNpos ρ
  have hrealcancel : (N : ℝ) ^ ρ.re * (N : ℝ) ^ (-ρ.re) = 1 := by
    rw [← Real.rpow_add hNpos]
    simp
  have htail : ‖(1 - ρ) * ρ * (N : ℂ) ^ ρ * J‖ ≤
      ‖1 - ρ‖ * ‖ρ‖ / ρ.re := by
    rw [norm_mul, norm_mul, norm_mul, hnormPow]
    calc
      ‖1 - ρ‖ * ‖ρ‖ * (N : ℝ) ^ ρ.re * ‖J‖ ≤
        ‖1 - ρ‖ * ‖ρ‖ * (N : ℝ) ^ ρ.re * ((N : ℝ) ^ (-ρ.re) / ρ.re) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = ‖1 - ρ‖ * ‖ρ‖ / ρ.re := by
        calc
          _ = ‖1 - ρ‖ * ‖ρ‖ *
              ((N : ℝ) ^ ρ.re * (N : ℝ) ^ (-ρ.re)) / ρ.re := by ring
          _ = _ := by rw [hrealcancel]; ring
  rw [hrepr]
  calc
    ‖(1 - ρ) / 2 - (1 - ρ) * ρ * (N : ℂ) ^ ρ * J‖ ≤
      ‖(1 - ρ) / 2‖ + ‖(1 - ρ) * ρ * (N : ℂ) ^ ρ * J‖ := norm_sub_le _ _
    _ ≤ ‖1 - ρ‖ / 2 + ‖1 - ρ‖ * ‖ρ‖ / ρ.re := by
      norm_num only [norm_div, norm_ofNat]
      exact add_le_add le_rfl htail
    _ ≤ zeroKernelIntegerConstant ρ := by
      unfold zeroKernelIntegerConstant
      rw [mul_add, mul_one, ← mul_div_assoc]
      linarith [norm_nonneg (1 - ρ)]

/-- A power on the positive ray is Lipschitz on `[1,r]` when its real
exponent is at most one. -/
theorem norm_cpow_sub_one_le {ρ : ℂ} (hρ : ρ ≠ 0) (hβ : ρ.re ≤ 1)
    {r : ℝ} (hr : 1 ≤ r) :
    ‖(r : ℂ) ^ ρ - 1‖ ≤ ‖ρ‖ * (r - 1) := by
  have hd : ∀ x ∈ Set.Icc (1 : ℝ) r,
      HasDerivWithinAt (fun t : ℝ => (t : ℂ) ^ ρ)
        (ρ * (x : ℂ) ^ (ρ - 1)) (Set.Icc 1 r) x := by
    intro x hx
    exact (hasDerivAt_ofReal_cpow_const (by linarith [hx.1] : x ≠ 0) hρ).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico (1 : ℝ) r,
      ‖ρ * (x : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ‖ := by
    intro x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1]),
      Complex.sub_re, Complex.one_re]
    exact mul_le_of_le_one_right (norm_nonneg ρ)
      (Real.rpow_le_one_of_one_le_of_nonpos hx.1 (by linarith))
  simpa only [Complex.ofReal_one, Complex.one_cpow] using
    norm_image_sub_le_of_norm_deriv_le_segment' hd hb r ⟨hr, le_rfl⟩

/-- Explicit positive constant for every real cutoff. -/
def zeroKernelConstant (ρ : ℂ) : ℝ :=
  2 * zeroKernelIntegerConstant ρ + ‖ρ‖ + 1

theorem zeroKernelConstant_pos {ρ : ℂ} (hβ : 0 < ρ.re) :
    0 < zeroKernelConstant ρ := by
  unfold zeroKernelConstant zeroKernelIntegerConstant
  positivity

theorem zeroSeed_kernel_norm_le {ρ : ℂ} (hzero : riemannZeta ρ = 0)
    (hβ : 0 < ρ.re) (hβ1 : ρ.re < 1) {u : ℝ} (hu : 1 ≤ u) :
    ‖divisorKernel (zeroSeed ρ) u‖ ≤ zeroKernelConstant ρ := by
  have hρ0 : ρ ≠ 0 := Complex.ne_zero_of_re_pos hβ
  have hρ1 : ρ ≠ 1 := by intro h; simp [h] at hβ1
  let N : ℕ := ⌊u⌋₊
  let r : ℝ := u / N
  have hN : 1 ≤ N := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hu)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNle : (N : ℝ) ≤ u := Nat.floor_le (by linarith)
  have huN : u < (N : ℝ) + 1 := Nat.lt_floor_add_one u
  have hr : 1 ≤ r := by
    dsimp [r]
    exact (le_div_iff₀ hNpos).mpr (by simpa using hNle)
  have hr2 : r ≤ 2 := by
    dsimp [r]
    apply (div_le_iff₀ hNpos).mpr
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hpower : (r : ℂ) ^ ρ * (N : ℂ) ^ ρ = (u : ℂ) ^ ρ := by
    dsimp [r]
    rw [Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg (by linarith : 0 ≤ u) hNpos.le]
    simp only [Complex.ofReal_natCast]
    have hp : (N : ℂ) ^ ρ ≠ 0 := Complex.cpow_ne_zero_iff.mpr
      (Or.inl (by exact_mod_cast hNpos.ne'))
    exact div_mul_cancel₀ _ hp
  have hscale : divisorKernel (zeroSeed ρ) u =
      (r : ℂ) ^ ρ * divisorKernel (zeroSeed ρ) (N : ℝ) +
        (N : ℂ) * ((r : ℂ) ^ ρ - 1) := by
    rw [zeroSeed_kernel_formula ρ (by linarith), zeroSeed_kernel_formula ρ hNpos.le,
      Nat.floor_natCast]
    simp only [Complex.ofReal_natCast]
    change (1 - ρ) * (u : ℂ) ^ ρ *
        (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ ρ) - N = _
    rw [← hpower]
    ring
  have hpr : ‖(r : ℂ) ^ ρ‖ ≤ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < r)]
    exact (Real.rpow_le_self_of_one_le hr hβ1.le).trans hr2
  have hmain : ‖(r : ℂ) ^ ρ * divisorKernel (zeroSeed ρ) (N : ℝ)‖ ≤
      2 * zeroKernelIntegerConstant ρ := by
    rw [norm_mul]
    exact mul_le_mul hpr (zeroSeed_kernel_nat_norm_le hzero hβ hρ1 hN)
      (norm_nonneg _) (by norm_num)
  have htail : ‖(N : ℂ) * ((r : ℂ) ^ ρ - 1)‖ ≤ ‖ρ‖ := by
    rw [norm_mul, Complex.norm_natCast]
    calc
      (N : ℝ) * ‖(r : ℂ) ^ ρ - 1‖ ≤ (N : ℝ) * (‖ρ‖ * (r - 1)) :=
        mul_le_mul_of_nonneg_left (norm_cpow_sub_one_le hρ0 hβ1.le hr) hNpos.le
      _ = ‖ρ‖ * (u - N) := by dsimp [r]; field_simp [hNpos.ne']
      _ ≤ ‖ρ‖ := by
        have hgap : u - (N : ℝ) ≤ 1 := by linarith
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hgap (norm_nonneg ρ)
  rw [hscale]
  exact (norm_add_le _ _).trans (by
    unfold zeroKernelConstant
    linarith)

/-- The finite, actual-zero historical estimate, before lower-order terms
are absorbed or asymptotic notation is introduced. -/
theorem zeroPotential_norm_le_historical_sqrt {ρ : ℂ}
    (hzero : riemannZeta ρ = 0) (hβ : 0 < ρ.re) (hβ1 : ρ.re < 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖zeroPotential ρ N‖ ≤
      8 * zeroKernelConstant ρ * Real.sqrt (RHLean.Proof.squareRootHistoricalK N) *
        Real.sqrt (N : ℝ) := by
  apply potential_norm_le_historical_sqrt (zeroPotential_one ρ)
    (fun v hv => zeroPotential_hasDerivAt (Complex.ne_zero_of_re_pos hβ) (by linarith))
    (zeroKernelConstant_pos hβ).le
    (fun u hu => zeroSeed_kernel_norm_le hzero hβ hβ1 hu) hN

/-- A direct finite lower bound for the primitive. -/
theorem zeroPotential_norm_lower (ρ : ℂ) {u : ℝ} (hu : 1 ≤ u) :
    ‖(1 - ρ) / ρ‖ * (u ^ ρ.re - 1) - Real.log u ≤ ‖zeroPotential ρ u‖ := by
  have hu0 : 0 < u := by linarith
  have hidentity : zeroPotential ρ u + ((1 - ρ) / ρ + (Real.log u : ℂ)) =
      ((1 - ρ) / ρ) * (u : ℂ) ^ ρ := by unfold zeroPotential; ring
  have htriangle := norm_add_le (zeroPotential ρ u) ((1 - ρ) / ρ + (Real.log u : ℂ))
  rw [hidentity, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0] at htriangle
  have herror := norm_add_le ((1 - ρ) / ρ) (Real.log u : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hu)] at herror
  nlinarith

/-- Explicit finite zero exclusion in the original strict-history coordinate.
This uses the coarse fully proved kernel constant rather than an unproved
sharp integral constant. -/
theorem zero_forces_historical_finite {ρ : ℂ} (hzero : riemannZeta ρ = 0)
    (hβ : 0 < ρ.re) (hβ1 : ρ.re < 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖(1 - ρ) / ρ‖ * ((N : ℝ) ^ ρ.re - 1) - Real.log (N : ℝ) ≤
      8 * zeroKernelConstant ρ * Real.sqrt (RHLean.Proof.squareRootHistoricalK N) *
        Real.sqrt (N : ℝ) :=
  (zeroPotential_norm_lower ρ (by exact_mod_cast hN)).trans
    (zeroPotential_norm_le_historical_sqrt hzero hβ hβ1 hN)

/-- The primitive has a power-sized norm at every sufficiently large scale.
The logarithmic and constant terms are absorbed with a fixed positive margin.
-/
theorem zeroPotential_eventually_norm_ge {ρ : ℂ} (hβ : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      c * (N : ℝ) ^ ρ.re ≤ ‖zeroPotential ρ N‖ := by
  have hρ0 : ρ ≠ 0 := Complex.ne_zero_of_re_pos hβ
  let A : ℝ := ‖(1 - ρ) / ρ‖
  have hA : 0 < A := norm_pos_iff.mpr
    (div_ne_zero (sub_ne_zero.mpr hρ1.symm) hρ0)
  have hlog : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.log x‖ ≤ (A / 4) * ‖x ^ ρ.re‖ :=
    (_root_.isLittleO_log_rpow_atTop hβ).bound (by positivity)
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop, 4 ≤ x ^ ρ.re :=
    (_root_.tendsto_rpow_atTop hβ).eventually (eventually_ge_atTop 4)
  have hreal : ∀ᶠ x : ℝ in Filter.atTop,
      (A / 2) * x ^ ρ.re ≤ ‖zeroPotential ρ x‖ := by
    filter_upwards [hlog, hlarge, eventually_ge_atTop (1 : ℝ)] with x hxlog hxlarge hx
    have hxpos : 0 < x := by linarith
    have hxpow : 0 < x ^ ρ.re := Real.rpow_pos_of_pos hxpos _
    have hconstant : A ≤ (A / 4) * x ^ ρ.re := by nlinarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxpow] at hxlog
    have hidentity : zeroPotential ρ x + ((1 - ρ) / ρ + (Real.log x : ℂ)) =
        ((1 - ρ) / ρ) * (x : ℂ) ^ ρ := by
      unfold zeroPotential
      ring
    have htriangle := norm_add_le (zeroPotential ρ x)
      ((1 - ρ) / ρ + (Real.log x : ℂ))
    rw [hidentity, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos] at htriangle
    have herror := norm_add_le ((1 - ρ) / ρ) (Real.log x : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at herror
    change A * x ^ ρ.re ≤ _ at htriangle
    change _ ≤ A + |Real.log x| at herror
    nlinarith
  refine ⟨A / 2, by positivity, ?_⟩
  exact (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop).eventually hreal

/-- ENV-2 in the form required by the exponent consumers: every actual
off-critical zero forces a positive power of the true strict historical
maximum at **every** sufficiently large integer root.

The conclusion is eventual only because the lower-order terms in the
primitive are absorbed.  The constant is selected before the scale.
-/
theorem zero_forces_historical_power {ρ : ℂ} (hzero : riemannZeta ρ = 0)
    (hβ : (1 / 2 : ℝ) < ρ.re) (hβ1 : ρ.re < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ R : ℕ in Filter.atTop,
      c * (R : ℝ) ^ (2 * ρ.re - 1) ≤ RHLean.Proof.squareRootHistoricalK R := by
  have hβ0 : 0 < ρ.re := by linarith
  have hρ1 : ρ ≠ 1 := by intro h; simp [h] at hβ1
  let C := zeroKernelConstant ρ
  have hC : 0 < C := zeroKernelConstant_pos hβ0
  obtain ⟨c₀, hc₀, hlower⟩ := zeroPotential_eventually_norm_ge hβ0 hρ1
  refine ⟨(c₀ / (8 * C)) ^ 2, by positivity, ?_⟩
  filter_upwards [hlower, eventually_ge_atTop (1 : ℕ)] with R hRlower hR
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hK : 0 ≤ RHLean.Proof.squareRootHistoricalK R :=
    RHLean.Proof.squareRootHistoricalK_nonneg R
  have hupper : ‖zeroPotential ρ R‖ ≤
      8 * C * Real.sqrt (RHLean.Proof.squareRootHistoricalK R) * Real.sqrt (R : ℝ) :=
    zeroPotential_norm_le_historical_sqrt hzero hβ0 hβ1 hR
  have hboth := hRlower.trans hupper
  have hsq : (c₀ * (R : ℝ) ^ ρ.re) ^ 2 ≤
      (8 * C * Real.sqrt (RHLean.Proof.squareRootHistoricalK R) * Real.sqrt (R : ℝ)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hboth
  simp only [mul_pow, Real.sq_sqrt hK, Real.sq_sqrt hRpos.le] at hsq
  have hpower : ((R : ℝ) ^ ρ.re) ^ 2 =
      (R : ℝ) ^ (2 * ρ.re - 1) * (R : ℝ) := by
    calc
      ((R : ℝ) ^ ρ.re) ^ 2 = (R : ℝ) ^ (ρ.re + ρ.re) := by
        rw [Real.rpow_add hRpos]
        ring
      _ = (R : ℝ) ^ ((2 * ρ.re - 1) + 1) := by congr 1; ring
      _ = (R : ℝ) ^ (2 * ρ.re - 1) * (R : ℝ) := by
        rw [Real.rpow_add hRpos, Real.rpow_one]
  rw [hpower] at hsq
  have hcancel : c₀ ^ 2 * (R : ℝ) ^ (2 * ρ.re - 1) ≤
      (8 * C) ^ 2 * RHLean.Proof.squareRootHistoricalK R := by
    apply le_of_mul_le_mul_right (a := (R : ℝ)) _ hRpos
    simpa only [mul_pow, mul_assoc] using hsq
  have hdivide : (c₀ ^ 2 * (R : ℝ) ^ (2 * ρ.re - 1)) / (8 * C) ^ 2 ≤
      RHLean.Proof.squareRootHistoricalK R := by
    apply (div_le_iff₀ (by positivity : 0 < (8 * C) ^ 2)).mpr
    simpa only [mul_comm] using hcancel
  convert hdivide using 1
  rw [div_pow]
  ring

end RHLean.Analysis.UniversalEnvelope
