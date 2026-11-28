import RHLean.Analysis.AlpogeNativeBoundHandoff
import RHLean.Analysis.MobiusRenewalTelescope
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-! The three-scale residual on the complete real clock and its rational
cyclotomic product. The rounding estimate is uniform in the signs and
uses the divisor sum only for the rounding error. -/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open Finset
namespace RHLean.Analysis.PrimitiveCertificate

private def ramp (y : ℝ) : ℝ := if 0 < y ∧ y ≤ 1 then 1 / y - 1 else 0

private def invertedRamp (y : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 ⌊1 / y⌋₊, (μ j : ℝ) * ramp (j * y)

private def reflect (total : ℝ) (upper : ℝ → ℝ) (y : ℝ) : ℝ :=
  if y ∈ Set.Icc 0 1 then
    if y < 1 / 2 then total - upper (1 - y) else upper y
  else 0

private def profileA := reflect 2 (fun t => 1 / t - 1)
private def profileB := reflect 0 (fun t => invertedRamp (t / 2) - profileA (t / 2))
private def profileC₀ := reflect 0 (fun t => if t ≤ 2 / 3 then 0 else
  invertedRamp (t / 4) - profileA (t / 4) - profileB (t / 2))
private def tent := reflect 0 (fun t => max (1 - |12 * t - 7|) 0)

private def splitIntegral (f : ℝ → ℝ) : ℝ :=
  ∫ t in (1 / 2 : ℝ)..1, f t * Real.log (t / (1 - t))

private def calibration : ℝ :=
  4 * (Real.log 2 - Real.eulerMascheroniConstant - splitIntegral profileA -
    splitIntegral profileB / 2 - splitIntegral profileC₀ / 4) / splitIntegral tent

/-- The fixed physical profile in the three-scale calibration. -/
def profile (y : ℝ) : ℝ :=
  profileA y + profileB (2 * y) + (profileC₀ (4 * y) + calibration * tent (4 * y))

/-- The residual on its compact support. -/
def residual (y : ℝ) : ℝ :=
  if 0 < y ∧ y ≤ 1 then (∑ j ∈ Icc 1 ⌊1 / y⌋₊, profile (j * y)) - (1 / y - 1)
  else 0

/-- Exact transfer at a real argument, with every prime power present. -/
theorem statementOCGz_add_residual {x : ℝ} (hx : 0 < x) :
    AlpogeNativeBoundHandoff.statementOCGz x +
      ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * residual (n / x) =
    (∑ k ∈ Icc 1 ⌊x⌋₊, Real.log k * profile (k / x)) -
      x * Real.log x + (1 + Real.eulerMascheroniConstant) * x := by
  let N := ⌊x⌋₊
  let f (d j : ℕ) : ℝ := Λ d * profile ((d * j : ℕ) / x)
  have swap := congrArg Complex.re (sum_Icc_divisorsAntidiagonal_eq_sum_div
    (fun d j => ((f d j : ℝ) : ℂ)) N)
  simp only [Complex.re_sum, Complex.ofReal_re] at swap
  have lhs : (∑ k ∈ Icc 1 N, ∑ z ∈ k.divisorsAntidiagonal, f z.1 z.2) =
      ∑ k ∈ Icc 1 N, Real.log k * profile (k / x) := by
    apply sum_congr rfl
    intro k _
    calc
      _ = ∑ z ∈ k.divisorsAntidiagonal, Λ z.1 * profile (k / x) :=
        sum_congr rfl fun z hz => by simp only [f, (Nat.mem_divisorsAntidiagonal.mp hz).1]
      _ = _ := by rw [← sum_mul, Nat.sum_divisorsAntidiagonal (fun i _ => (Λ i : ℝ)),
        ArithmeticFunction.vonMangoldt_sum]
  have rhs : (∑ d ∈ Icc 1 N, (Λ d * (x / d - 1) + Λ d * residual (d / x))) =
      ∑ d ∈ Icc 1 N, ∑ j ∈ Icc 1 (N / d), f d j := by
    apply sum_congr rfl
    intro d hd
    have hd0 : 0 < (d : ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
    have hdx : (d : ℝ) ≤ x := (Nat.cast_le.mpr (mem_Icc.mp hd).2).trans (Nat.floor_le hx.le)
    have inv : 1 / ((d : ℝ) / x) = x / d := by simp [div_eq_mul_inv, mul_comm]
    rw [residual, if_pos ⟨div_pos hd0 hx, (div_le_one hx).mpr hdx⟩, inv, Nat.floor_div_natCast]
    rw [mul_sub, ← add_sub_assoc, add_sub_cancel_left]
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    simp only [f, Nat.cast_mul]
    ring_nf
  have eqn := (rhs.trans swap.symm).trans lhs
  rw [sum_add_distrib] at eqn
  unfold AlpogeNativeBoundHandoff.statementOCGz AlpogeNativeBoundHandoff.statementOCSz
  dsimp only [N] at eqn
  linarith only [eqn]

/-- Rational smoothing parameter. -/
def radius (c : ℕ) : ℚ := c / ((c : ℚ) + 1)

private theorem radius_mem (c : ℕ) : 0 ≤ radius c ∧ radius c < 1 := by
  unfold radius
  constructor
  · positivity
  · exact (div_lt_one (by positivity)).2 (by linarith)

private theorem factor_pos (c : ℕ) {d : ℕ} (hd : 0 < d) : 0 < 1 - radius c ^ d :=
  sub_pos.mpr (pow_lt_one₀ (radius_mem c).1 (radius_mem c).2 hd.ne')

/-- Divisor-product evaluation of the normalized primitive determinant. -/
def block (c n : ℕ) : ℚ :=
  ∏ d ∈ n.divisors, (1 - radius c ^ d) ^ μ (n / d)

theorem block_pos (c n : ℕ) : 0 < block c n :=
  prod_pos fun d hd => zpow_pos (factor_pos c (Nat.pos_of_mem_divisors hd)) _

/-- The same rational is the homogeneous cyclotomic determinant divided
by (c+1)^φ(n), including the degree in the normalization. -/
theorem block_eq_cyclotomic {c n : ℕ} (hc : 0 < c) (hn : 0 < n) :
    block c n = radius c ^ n.totient * (Polynomial.cyclotomic n ℚ).eval (radius c)⁻¹ := by
  let r := radius c
  let F (k : ℕ) := r ^ k.totient * (Polynomial.cyclotomic k ℚ).eval r⁻¹
  have hr : r ≠ 0 := by
    dsimp [r, radius]
    positivity
  have prodF (k : ℕ) (hk : 0 < k) : ∏ d ∈ k.divisors, F d = 1 - r ^ k := by
    have ev := congrArg (Polynomial.eval r⁻¹) (Polynomial.prod_cyclotomic_eq_X_pow_sub_one hk ℚ)
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at ev
    simp only [F, prod_mul_distrib, prod_pow_eq_pow_sum, Nat.sum_totient, ev]
    rw [inv_pow, mul_sub, mul_inv_cancel₀ (pow_ne_zero k hr), mul_one]
  have nz (k : ℕ) (hk : 0 < k) : F k ≠ 0 := by
    have h : (∏ d ∈ k.divisors, F d) ≠ 0 := (prodF k hk).trans_ne (factor_pos c hk).ne'
    exact prod_ne_zero_iff.mp h k (Nat.mem_divisors_self _ hk.ne')
  have e := (ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero nz
    (fun k hk => (factor_pos c hk).ne')).mp prodF n hn
  rwa [Nat.prod_divisorsAntidiagonal' (fun i j => (1 - r ^ j) ^ μ i)] at e

private theorem log_factor_bound (c : ℕ) {d : ℕ} (hd : 0 < d) :
    |Real.log ((1 - radius c ^ d : ℚ) : ℝ)| ≤ Real.log ((c : ℝ) + 1) := by
  have hpos : (0 : ℝ) < ((1 - radius c ^ d : ℚ) : ℝ) := by exact_mod_cast factor_pos c hd
  have hu : (1 - radius c ^ d : ℚ) ≤ 1 := sub_le_self _ (pow_nonneg (radius_mem c).1 _)
  have hq : 1 / ((c : ℚ) + 1) ≤ 1 - radius c ^ d := by
    have h := pow_le_of_le_one (radius_mem c).1 (radius_mem c).2.le hd.ne'
    rw [show 1 / ((c : ℚ) + 1) = 1 - radius c by unfold radius; field_simp <;> ring]
    linarith
  have hl : 1 / ((c : ℝ) + 1) ≤ ((1 - radius c ^ d : ℚ) : ℝ) := by exact_mod_cast hq
  have low := Real.log_le_log (by positivity) hl
  rw [one_div, Real.log_inv] at low
  rw [abs_of_nonpos (Real.log_nonpos hpos.le (by exact_mod_cast hu))]
  linarith

theorem abs_log_block_le (c n : ℕ) :
    |Real.log (block c n : ℝ)| ≤ n.divisors.card * Real.log ((c : ℝ) + 1) := by
  unfold block
  rw [Rat.cast_prod, Real.log_prod (fun d hd => by
    exact_mod_cast (zpow_pos (factor_pos c (Nat.pos_of_mem_divisors hd)) (μ (n / d))).ne')]
  simp only [Rat.cast_zpow, Real.log_zpow]
  calc
    _ ≤ _ := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, Real.log ((c : ℝ) + 1) := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul]
      have hm : |((μ (n / d) : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n / d))
      simpa only [one_mul] using mul_le_mul hm (log_factor_bound c (Nat.pos_of_mem_divisors hd))
        (abs_nonneg _) zero_le_one
    _ = _ := by simp [nsmul_eq_mul]

private theorem divisor_count_le (N : ℕ) :
    (∑ n ∈ Icc 2 N, (n.divisors.card : ℝ)) ≤ N * (1 + Real.log N) := by
  have swap := congrArg Complex.re (sum_Icc_divisorsAntidiagonal_eq_sum_div
    (fun _ _ => (1 : ℂ)) N)
  simp only [Complex.re_sum, Complex.one_re] at swap
  have row (n : ℕ) : (∑ _z ∈ n.divisorsAntidiagonal, (1 : ℝ)) = n.divisors.card := by
    rw [Nat.sum_divisorsAntidiagonal (f := fun _ _ => (1 : ℝ))]
    simp
  simp_rw [row] at swap
  have hh : (harmonic N : ℝ) = ∑ d ∈ Icc 1 N, (1 : ℝ) / d := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) := sum_le_sum_of_subset_of_nonneg
      (Icc_subset_Icc (by decide) le_rfl) (by intros; positivity)
    _ = _ := swap
    _ ≤ ∑ d ∈ Icc 1 N, (N : ℝ) / d := by
      apply sum_le_sum
      intro d _
      simpa [Nat.card_Icc] using (Nat.cast_div_le : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d)
    _ = N * (harmonic N : ℝ) := by rw [hh, mul_sum]; simp [div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (Nat.cast_nonneg _)

/-- The common scaling c on the original real clock. -/
def scale (x : ℝ) : ℕ := ⌊Real.sqrt x⌋₊

/-- Signed integral multiplicity of the complete calibrated residual. -/
def multiplicity (x : ℝ) (n : ℕ) : ℤ := round ((scale x : ℝ) * residual (n / x))

/-- One positive rational before choosing a finite place. -/
def certificate (x : ℝ) : ℚ :=
  ∏ n ∈ Icc 2 ⌊x⌋₊, block (scale x) n ^ multiplicity x n

theorem certificate_pos (x : ℝ) : 0 < certificate x :=
  prod_pos fun n _ => zpow_pos (block_pos _ n) _

/-- All labels contribute with their original sign. The absolute sum is
used only for the errors of rounding to the nearest integer. -/
theorem certificate_rounding (x : ℝ) :
    |Real.log (certificate x : ℝ) -
      (scale x : ℝ) * ∑ n ∈ Icc 2 ⌊x⌋₊, residual (n / x) * Real.log (block (scale x) n : ℝ)| ≤
    ((⌊x⌋₊ : ℝ) * (1 + Real.log ⌊x⌋₊)) * (Real.log ((scale x : ℝ) + 1) / 2) := by
  unfold certificate
  rw [Rat.cast_prod, Real.log_prod (fun n _ => by
    exact_mod_cast (zpow_pos (block_pos (scale x) n) (multiplicity x n)).ne')]
  simp only [Rat.cast_zpow, Real.log_zpow]
  rw [mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ _ := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 2 ⌊x⌋₊, (n.divisors.card : ℝ) * (Real.log ((scale x : ℝ) + 1) / 2) := by
      apply sum_le_sum
      intro n _
      rw [← mul_assoc, ← sub_mul, abs_mul, abs_sub_comm]
      have h := mul_le_mul (abs_sub_round ((scale x : ℝ) * residual (n / x)))
        (abs_log_block_le (scale x) n) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      dsimp only [multiplicity]
      linarith only [h]
    _ = _ := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (divisor_count_le _)
      (div_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (scale x)])) (by norm_num))

end RHLean.Analysis.PrimitiveCertificate
