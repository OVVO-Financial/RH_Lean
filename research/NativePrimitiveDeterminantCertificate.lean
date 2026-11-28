import RHLean.Analysis.AlpogeNativeBoundHandoff
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Analysis.RamanujanDivisorBoundary
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
    have hy : 0 < (d : ℝ) / x ∧ (d : ℝ) / x ≤ 1 :=
      ⟨div_pos hd0 hx, (div_le_one hx).mpr hdx⟩
    simp only [residual, hy.1, hy.2, and_self, ↓reduceIte, inv, Nat.floor_div_natCast]
    calc
      _ = Λ d * ∑ j ∈ Icc 1 (N / d), profile (j * ((d : ℝ) / x)) := by
        rw [← mul_add]
        congr 1
        abel
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        have h : (j : ℝ) * ((d : ℝ) / x) = ((d * j : ℕ) : ℝ) / x := by push_cast; ring
        rw [h]
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
  prod_pos fun _d hd => zpow_pos (factor_pos c (Nat.pos_of_mem_divisors hd)) _

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
    rw [show 1 / ((c : ℚ) + 1) = 1 - radius c by unfold radius; field_simp; ring]
    linarith
  have hl : 1 / ((c : ℝ) + 1) ≤ ((1 - radius c ^ d : ℚ) : ℝ) := calc
    _ = ((1 / ((c : ℚ) + 1) : ℚ) : ℝ) := by simp
    _ ≤ _ := Rat.cast_le.mpr hq
  have low := Real.log_le_log (by positivity) hl
  rw [one_div, Real.log_inv] at low
  rw [abs_of_nonpos (Real.log_nonpos hpos.le (by exact_mod_cast hu))]
  linarith

private theorem log_block (c n : ℕ) :
    Real.log (block c n : ℝ) =
      ∑ d ∈ n.divisors, (μ (n / d) : ℝ) * Real.log ((1 - radius c ^ d : ℚ) : ℝ) := by
  unfold block
  rw [Rat.cast_prod, Real.log_prod (fun d hd => by
    exact_mod_cast (zpow_pos (factor_pos c (Nat.pos_of_mem_divisors hd)) (μ (n / d))).ne')]
  simp only [Rat.cast_zpow, Real.log_zpow]

theorem abs_log_block_le (c n : ℕ) :
    |Real.log (block c n : ℝ)| ≤ n.divisors.card * Real.log ((c : ℝ) + 1) := by
  rw [log_block]
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

private theorem sum_multiples {d : ℕ} (hd : 0 < d) (H : ℕ) (g : ℕ → ℝ) :
    (∑ j ∈ Icc 1 H, if d ∣ j then g j else 0) =
      ∑ i ∈ range (H / d), g (d * (i + 1)) := by
  classical
  have im : (range (H / d)).image (fun i => d * (i + 1)) = (Icc 1 H).filter (d ∣ ·) := by
    ext j
    simp only [mem_image, mem_range, mem_filter, mem_Icc]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨Nat.mul_pos hd (Nat.succ_pos _), by
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp (Nat.succ_le_of_lt hi)⟩,
        dvd_mul_right _ _⟩
    · rintro ⟨⟨hj, hH⟩, k, rfl⟩
      cases k with
      | zero => simp at hj
      | succ k =>
        exact ⟨k, (Nat.le_div_iff_mul_le hd).mpr (by simpa only [Nat.mul_comm] using hH), rfl⟩
  rw [← sum_filter, ← im, sum_image]
  intro i _ j _ h
  exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_left hd h)

private def partialLog (z : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ range m, z ^ (i + 1) / ((i : ℝ) + 1)

private theorem trace_divisors (n H : ℕ) (r : ℝ) :
    (∑ j ∈ Icc 1 H, r ^ j / j * (ramanujanDivisorKernel n j 0 : ℝ)) =
      ∑ d ∈ n.divisors, (μ (n / d) : ℝ) * partialLog (r ^ d) (H / d) := by
  simp only [ramanujanDivisorKernel, Int.cast_sum, Nat.modEq_zero_iff_dvd,
    Int.cast_ite, Int.cast_mul, Int.cast_natCast, Int.cast_zero, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  have hd₀ := Nat.pos_of_mem_divisors hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd₀.ne'
  simp_rw [mul_ite, mul_zero]
  rw [sum_multiples hd₀, partialLog, mul_sum]
  apply sum_congr rfl
  intro i _
  simp only [pow_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hdR]

private theorem trace_tail (c n H : ℕ) :
    |(∑ j ∈ Icc 1 H, (radius c : ℝ) ^ j / j * (ramanujanDivisorKernel n j 0 : ℝ)) +
      Real.log (block c n : ℝ)| ≤
    n.divisors.card * ((radius c : ℝ) ^ H / (1 - (radius c : ℝ))) := by
  let r : ℝ := radius c
  have hr₀ : 0 ≤ r := by
    change (0 : ℝ) ≤ (radius c : ℝ)
    exact_mod_cast (radius_mem c).1
  have hr₁ : r < 1 := by
    change (radius c : ℝ) < (1 : ℝ)
    exact_mod_cast (radius_mem c).2
  rw [trace_divisors, log_block, ← sum_add_distrib]
  calc
    _ ≤ _ := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, r ^ H / (1 - r) := by
      apply sum_le_sum
      intro d hd
      have hd₀ := Nat.pos_of_mem_divisors hd
      have hpow := pow_nonneg hr₀ d
      have hlt := pow_lt_one₀ hr₀ hr₁ hd₀.ne'
      have terr := Real.abs_log_sub_add_sum_range_le
        (show |r ^ d| < 1 by rwa [abs_of_nonneg hpow]) (H / d)
      rw [abs_of_nonneg hpow, ← pow_mul] at terr
      have num := pow_le_pow_of_le_one hr₀ hr₁.le (Nat.lt_mul_div_succ H hd₀).le
      have den := sub_le_sub_left (pow_le_of_le_one hr₀ hr₁.le hd₀.ne') 1
      have logerr : |partialLog (r ^ d) (H / d) + Real.log (1 - r ^ d)| ≤ r ^ H / (1-r) :=
        terr.trans (div_le_div₀ (pow_nonneg hr₀ _) num (sub_pos.mpr hr₁) den)
      have hm : |((μ (n / d) : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n / d))
      rw [← mul_add, abs_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_pow]
      simpa only [one_mul] using mul_le_mul hm logerr (abs_nonneg _) zero_le_one
    _ = _ := by simp [r, nsmul_eq_mul]

/-- Full primitive population using the native Ramanujan divisor kernel. -/
def tracePopulation (x : ℝ) (j : ℕ) : ℝ :=
  ∑ n ∈ Icc 2 ⌊x⌋₊, residual (n / x) * (ramanujanDivisorKernel n j 0 : ℝ)

private def stepSize (x : ℝ) : ℝ := Real.log (1 + 1 / (scale x : ℝ))

def traceCutoff (x : ℝ) : ℕ := ⌈4 * Real.log (2 * x) / stepSize x⌉₊

private def logCorrection (u : ℝ) : ℝ :=
  if u = 0 then 0 else Real.log ((1 - Real.exp (-u)) / u)

private def correctionCoeff (j : ℕ) : ℝ :=
  if j = 1 then -(1 / 2) else if 0 < j ∧ Even j then
    (-1 : ℝ) ^ (j / 2 + 1) * (riemannZeta j).re / ((j / 2 : ℕ) * (2 * Real.pi) ^ j)
  else 0

/-- The reference from the primitive admission calculation, evaluated with
Möbius values through c, real integrals and absolutely convergent zeta values. -/
def reference (x : ℝ) : ℝ :=
  let c := scale x
  let t := x * stepSize x
  let J := ⌈Real.log (2 * x) / Real.log Real.pi⌉₊
  x * (∑ k ∈ Icc 1 c, (μ k : ℝ) / k *
      ∫ y in (0 : ℝ)..1, residual y * logCorrection (t * y / k)) +
    x * ∑ j ∈ Icc 1 J, correctionCoeff j * t ^ j *
      (∫ y in (0 : ℝ)..1, y ^ j * residual y) *
      (1 / (riemannZeta ((j : ℂ) + 1)).re -
        ∑ k ∈ Icc 1 c, (μ k : ℝ) / (k : ℝ) ^ (j + 1))

/-- Finite error in replacing the specified signed trace and reference by
the opposite rational log and the same independently evaluated reference. -/
theorem trace_reference_rounding {x : ℝ} (hc : 0 < scale x) :
    let c := scale x
    let r : ℝ := radius c
    let H := traceCutoff x
    let N := ⌊x⌋₊
    |((∑ j ∈ Icc 1 H, r ^ j / j * tracePopulation x j) + reference x) -
      (reference x - Real.log (certificate x : ℝ) / c)| ≤
    (∑ n ∈ Icc 2 N, |residual (n / x)| * n.divisors.card) * (r ^ H / (1 - r)) +
      ((N : ℝ) * (1 + Real.log N)) * (Real.log ((c : ℝ) + 1) / 2) / c := by
  intro c r H N
  let T := ∑ j ∈ Icc 1 H, r ^ j / j * tracePopulation x j
  let W := ∑ n ∈ Icc 2 N, residual (n / x) * Real.log (block c n : ℝ)
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have tr : T = ∑ n ∈ Icc 2 N, residual (n / x) *
      ∑ j ∈ Icc 1 H, r ^ j / j * (ramanujanDivisorKernel n j 0 : ℝ) := by
    dsimp only [T, tracePopulation]
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro j _
    ring
  have ht : |T + W| ≤ (∑ n ∈ Icc 2 N, |residual (n / x)| * n.divisors.card) *
      (r ^ H / (1 - r)) := by
    rw [tr]
    dsimp only [W]
    rw [← sum_add_distrib, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    rw [← mul_add, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (trace_tail c n H) (abs_nonneg _)
  have hp := div_le_div_of_nonneg_right (certificate_rounding x) hcR.le
  have split : T + reference x - (reference x - Real.log (certificate x : ℝ) / c) =
      (T + W) + (Real.log (certificate x : ℝ) - (c : ℝ) * W) / c := by
    field_simp [hcR.ne']; ring
  rw [split]
  refine (abs_add_le ..).trans (add_le_add ht ?_)
  rwa [abs_div, abs_of_pos hcR]

private theorem reflect_abs_le (total : ℝ) {f : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ t : ℝ, 1 / 2 ≤ t → t ≤ 1 → |f t| ≤ B) (y : ℝ) :
    |reflect total f y| ≤ |total| + B := by
  unfold reflect
  split_ifs with h hlt
  · exact (abs_sub _ _).trans (add_le_add_left
      (hf (1 - y) (by linarith) (by linarith [(Set.mem_Icc.mp h).1])) _)
  · linarith only [hf y (le_of_not_gt hlt) (Set.mem_Icc.mp h).2, abs_nonneg total]
  · simpa only [abs_zero] using add_nonneg (abs_nonneg total) hB

private theorem invertedRamp_bound {y : ℝ} (hy : 1 / 8 ≤ y) : |invertedRamp y| ≤ 64 := by
  have hy₀ : 0 < y := by linarith
  have inv : 1 / y ≤ 8 := (div_le_iff₀ hy₀).mpr (by linarith)
  unfold invertedRamp
  calc
    _ ≤ _ := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Icc 1 ⌊1 / y⌋₊, (8 : ℝ) := by
      apply sum_le_sum
      intro j hj
      have hj₁ : 1 ≤ (j : ℝ) := by exact_mod_cast (mem_Icc.mp hj).1
      have hprod : y ≤ (j : ℝ) * y := le_mul_of_one_le_left hy₀.le hj₁
      have hp₀ := hy₀.trans_le hprod
      have rb : |ramp (j * y)| ≤ 8 := by
        unfold ramp
        split_ifs
        · exact abs_le.mpr ⟨by linarith [div_nonneg zero_le_one hp₀.le],
            by linarith [(div_le_iff₀ hp₀).mpr (show 1 ≤ 8 * (j * y) by linarith)]⟩
        · norm_num
      have hm : |((μ j : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := j))
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul hm rb (abs_nonneg _) zero_le_one
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      linarith [(Nat.floor_le (div_nonneg zero_le_one hy₀.le)).trans inv]

private theorem bounded_profile (y : ℝ) : |profile y| ≤ 204 + |calibration| := by
  have A (t : ℝ) : |profileA t| ≤ 3 := by
    refine (reflect_abs_le 2 (B := 1) (by norm_num) (fun s hs _ => ?_) t).trans (by norm_num)
    have hs₀ : 0 < s := by linarith
    have hu : 1 / s ≤ 2 := (div_le_iff₀ hs₀).mpr (by linarith)
    exact abs_le.mpr ⟨by linarith [div_nonneg zero_le_one hs₀.le], by linarith⟩
  have B (t : ℝ) : |profileB t| ≤ 67 := by
    refine (reflect_abs_le 0 (B := 67) (by norm_num) (fun s hs _ => ?_) t).trans (by norm_num)
    have hU := invertedRamp_bound (show 1 / 8 ≤ s / 2 by linarith)
    exact (abs_sub _ _).trans (by linarith only [hU, A (s / 2)])
  have C (t : ℝ) : |profileC₀ t| ≤ 134 := by
    refine (reflect_abs_le 0 (B := 134) (by norm_num) (fun s hs _ => ?_) t).trans (by norm_num)
    split_ifs
    · norm_num
    · have hU := invertedRamp_bound (show 1 / 8 ≤ s / 4 by linarith)
      have hDiff := abs_sub (invertedRamp (s / 4)) (profileA (s / 4))
      exact (abs_sub _ _).trans (by linarith only [hU, hDiff, A (s / 4), B (s / 2)])
  have D (t : ℝ) : |tent t| ≤ 1 := by
    refine (reflect_abs_le 0 (B := 1) (by norm_num) (fun s _ _ => ?_) t).trans (by norm_num)
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [abs_nonneg (12*s-7)]) zero_le_one
  have cost := mul_le_mul_of_nonneg_left (D (4*y)) (abs_nonneg calibration)
  unfold profile
  rw [mul_one, ← abs_mul] at cost
  linarith only [abs_add_le (profileA y + profileB (2*y)) (profileC₀ (4*y) + calibration * tent (4*y)),
    abs_add_le (profileA y) (profileB (2*y)), abs_add_le (profileC₀ (4*y)) (calibration * tent (4*y)),
    A y, B (2*y), C (4*y), cost]

private theorem residual_bound {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : 1 ≤ n) :
    |residual (n / x)| ≤ (205 + |calibration|) * x := by
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hx₀ : 0 < x := by linarith
  have hd : 0 < (n : ℝ) / x := div_pos (by linarith) hx₀
  have hi : 1 / ((n : ℝ) / x) ≤ x := by
    rw [show 1 / ((n : ℝ) / x) = x / n by simp [div_eq_mul_inv, mul_comm]]
    exact div_le_self hx₀.le hn₁
  unfold residual
  split_ifs
  · have hs : |∑ j ∈ Icc 1 ⌊1 / ((n : ℝ) / x)⌋₊, profile (j * ((n : ℝ) / x))| ≤
        x * (204 + |calibration|) := by
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (fun _j _ => bounded_profile _)).trans ?_)
      simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      exact mul_le_mul_of_nonneg_right ((Nat.floor_le (div_nonneg zero_le_one hd.le)).trans hi) (by positivity)
    have hm : |1 / ((n : ℝ) / x) - 1| ≤ x := abs_le.mpr
      ⟨by linarith [div_nonneg zero_le_one hd.le], by linarith⟩
    exact (abs_sub _ _).trans (by linarith only [hs, hm])
  · rw [abs_zero]
    positivity

private theorem scale_bounds {x : ℝ} (hx : 4 ≤ x) :
    0 < scale x ∧ (scale x : ℝ) ≤ Real.sqrt x ∧ Real.sqrt x ≤ 2 * (scale x : ℝ) := by
  have hs : (2 : ℝ) ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hc : 1 ≤ scale x := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hc₁ : 1 ≤ (scale x : ℝ) := by exact_mod_cast hc
  exact ⟨hc, Nat.floor_le (Real.sqrt_nonneg _),
    by linarith only [show Real.sqrt x < (scale x : ℝ) + 1 from Nat.lt_floor_add_one _, hc₁]⟩

private theorem cutoff_decay {x : ℝ} (hx : 4 ≤ x) :
    ((radius (scale x) : ℝ) ^ traceCutoff x) * (2*x)^4 ≤ 1 := by
  let c : ℝ := scale x
  let r : ℝ := radius (scale x)
  have hc : 0 < c := Nat.cast_pos.mpr (scale_bounds hx).1
  have hs : 0 < stepSize x := Real.log_pos (by change 1 < 1 + 1/c; linarith [one_div_pos.mpr hc])
  have rinv : r = (1 + 1/c)⁻¹ := by
    dsimp only [r, radius]
    push_cast
    change c / (c + 1) = (1 + 1/c)⁻¹
    rw [show 1 + 1 / c = (c + 1) / c by rw [add_div, div_self hc.ne'], inv_div]
  have hr : 0 < r := rinv ▸ inv_pos.mpr (by positivity)
  have hlog : Real.log r = -stepSize x := by rw [rinv, Real.log_inv]; rfl
  have hH : 4 * Real.log (2*x) ≤ (traceCutoff x : ℝ) * stepSize x :=
    (div_le_iff₀ hs).mp (Nat.le_ceil _)
  change r ^ traceCutoff x * (2*x)^4 ≤ 1
  apply (Real.log_le_log_iff (mul_pos (pow_pos hr _) (by positivity)) zero_lt_one).mp
  rw [Real.log_mul (pow_ne_zero _ hr.ne') (by positivity), Real.log_pow, Real.log_pow, hlog, Real.log_one]
  norm_num
  linarith only [hH]

/-- Uniform error at every real x ≥ 4. The constant comes only from the
ordinary integrals in the fixed three-scale calibration. -/
theorem trace_reference_uniform {x : ℝ} (hx : 4 ≤ x) :
    let c := scale x
    let r : ℝ := radius c
    |((∑ j ∈ Icc 1 (traceCutoff x), r ^ j / j * tracePopulation x j) + reference x) -
      (reference x - Real.log (certificate x : ℝ) / c)| ≤
    (205 + |calibration|) + Real.sqrt x * (1 + Real.log x)^2 := by
  intro c r
  let N := ⌊x⌋₊
  let B := 205 + |calibration|
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ : 0 < x := by linarith
  obtain ⟨hc, hcs, hsc⟩ := scale_bounds hx
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  change (c:ℝ) ≤ Real.sqrt x at hcs
  change Real.sqrt x ≤ 2*(c:ℝ) at hsc
  have hN₁ : 1 ≤ N := (Nat.one_le_floor_iff _).mpr hx₁
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN₁
  have hN : (N : ℝ) ≤ x := Nat.floor_le hx₀.le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsq := Real.sq_sqrt hx₀.le
  have hs : 2 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx₀.le).mpr (by linarith)
  have hcx : (c:ℝ)+1 ≤ x := by
    have hmul := mul_nonneg (show 0 ≤ Real.sqrt x - 2 by linarith) (Real.sqrt_nonneg x)
    nlinarith only [hcs, hs, hsq, hmul]
  have count : (∑ n ∈ Icc 2 N, (n.divisors.card : ℝ)) ≤ x*x := by
    refine (divisor_count_le N).trans (mul_le_mul hN ?_ (by positivity) hx₀.le)
    linarith only [Real.log_le_sub_one_of_pos hNpos, hN]
  have mass : (∑ n ∈ Icc 2 N, |residual (n / x)| * n.divisors.card) ≤ (B*x)*(x*x) := by
    calc
      _ ≤ ∑ n ∈ Icc 2 N, (B*x) * n.divisors.card := by
        apply sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_right (residual_bound hx₁ (by have := (mem_Icc.mp hn).1; omega))
          (Nat.cast_nonneg _)
      _ = _ := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left count (mul_nonneg hB hx₀.le)
  have r₀ : 0 ≤ r := by
    change (0 : ℝ) ≤ (radius c : ℝ)
    exact_mod_cast (radius_mem c).1
  have r₁ : r < 1 := by
    change (radius c : ℝ) < (1 : ℝ)
    exact_mod_cast (radius_mem c).2
  have norm : 1 / (1 - r) = (c:ℝ)+1 := by
    dsimp [r, radius]
    push_cast
    field_simp <;> ring
  have decay := cutoff_decay hx
  change r ^ traceCutoff x * (2*x)^4 ≤ 1 at decay
  have tail : (∑ n ∈ Icc 2 N, |residual (n / x)| * n.divisors.card) *
      (r ^ traceCutoff x / (1-r)) ≤ B := by
    calc
      _ ≤ ((B*x)*(x*x)) * (r ^ traceCutoff x / (1-r)) := mul_le_mul_of_nonneg_right mass
        (div_nonneg (pow_nonneg r₀ _) (sub_pos.mpr r₁).le)
      _ = B * (r ^ traceCutoff x * (x^3 * ((c:ℝ)+1))) := by
        rw [div_eq_mul_one_div _ (1-r), norm]; ring
      _ ≤ B * (r ^ traceCutoff x * (2*x)^4) := by
        apply mul_le_mul_of_nonneg_left _ hB
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg r₀ _)
        calc
          _ ≤ x^3*x := mul_le_mul_of_nonneg_left hcx (by positivity)
          _ ≤ _ := by nlinarith only [show 0 ≤ x^4 by positivity]
      _ ≤ B := by simpa only [mul_one] using mul_le_mul_of_nonneg_left decay hB
  have hcLog := Real.log_le_log (show (0:ℝ)<c+1 by positivity) hcx
  have hNLog := Real.log_le_log hNpos hN
  have lN := Real.log_natCast_nonneg N
  have lx := Real.log_nonneg hx₁
  have bill : ((N:ℝ) * (1 + Real.log N)) * (Real.log ((c:ℝ)+1) / 2) / c ≤
      Real.sqrt x * (1 + Real.log x)^2 := by
    have cx : (N:ℝ) ≤ 2*(c:ℝ)*Real.sqrt x := hN.trans (by
      nlinarith only [hsq, mul_le_mul_of_nonneg_right hsc (Real.sqrt_nonneg x)])
    have h := mul_le_mul (mul_le_mul cx (add_le_add_left hNLog 1) (by linarith) (by positivity))
      (show Real.log ((c:ℝ)+1) ≤ 1 + Real.log x by linarith) (Real.log_nonneg (by linarith)) (by positivity)
    apply (div_le_iff₀ hcR).mpr
    linarith only [h]
  exact (trace_reference_rounding hc).trans (add_le_add tail bill)

#print axioms statementOCGz_add_residual
#print axioms block_eq_cyclotomic
#print axioms trace_reference_uniform

end RHLean.Analysis.PrimitiveCertificate
