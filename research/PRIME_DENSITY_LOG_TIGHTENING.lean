import «research.PRIME_DENSITY_UNIVERSAL_BASELINE»
import RHLean.Analysis.NativePNTMertens
import RHLean.Analysis.PrimeSieveQuotientPNTError

/-!
# Tail-sensitive and signed reciprocal density bounds

Extends the verified #803 baseline without changing its models or theorems.
The first estimate keeps the actual harmonic tail. The second reassembles the
unit-density transport by signed cofactors and uses the unconditional reciprocal
Mobius bound before estimating the fractional remainder. All statements are
finite, uniform inequalities; none asserts the missing FinalStokes estimate.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis
open RHLean.Arithmetic RHLean.Proof

private theorem densityTight_mertens_norm_le (n : ℕ) :
    ‖mertensSummatory n‖ ≤ (n : ℝ) := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory n]
  unfold cofactorMobiusPrefixMass
  calc
    ‖∑ m ∈ Finset.Icc 1 n, canonicalMoebiusWeight m‖ ≤
        ∑ m ∈ Finset.Icc 1 n, ‖canonicalMoebiusWeight m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 n, (1 : ℝ) :=
      Finset.sum_le_sum fun m _ => norm_canonicalMoebiusWeight_le_one m
    _ = (n : ℝ) := by simp

private theorem densityTight_reciprocal_step (a : ℝ) (ha : 0 < a) :
    (a + 1)⁻¹ ≤ Real.log (a + 1) - Real.log a := by
  have hb : 0 < a + 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at h
  have hid : a / (a + 1) - 1 = -(a + 1)⁻¹ := by
    field_simp
    ring
  rw [hid] at h
  linarith

/-- Keep the harmonic interval rather than enlarging it to a full prefix. -/
theorem densityTight_harmonic_tail_le_log
    {y x : ℕ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    (∑ q ∈ Finset.Ioc y x, (q : ℝ)⁻¹) ≤
      Real.log (x : ℝ) - Real.log (y : ℝ) := by
  induction x with
  | zero => omega
  | succ x ih =>
      by_cases h : y ≤ x
      · rw [Finset.sum_Ioc_succ_top h]
        have hx : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
        have hs := densityTight_reciprocal_step (x : ℝ) hx
        have hi := ih h
        push_cast
        linarith
      · have heq : y = x + 1 := by omega
        subst y
        simp

/-- The sharper common envelope, before choosing a density model. -/
theorem norm_densityWeightedTransport_le_harmonic_tail
    (d : ℕ → ℂ) (y x : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ q ∈ Finset.Ioc y x, ‖d q‖ ≤ L) :
    ‖∑ q ∈ Finset.Ioc y x, d q * mertensSummatory (x / q)‖ ≤
      L * (x : ℝ) * ∑ q ∈ Finset.Ioc y x, (q : ℝ)⁻¹ := by
  calc
    ‖∑ q ∈ Finset.Ioc y x, d q * mertensSummatory (x / q)‖ ≤
        ∑ q ∈ Finset.Ioc y x, ‖d q * mertensSummatory (x / q)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Ioc y x, L * ((x : ℝ) * (q : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqp : 0 < q := by have := (Finset.mem_Ioc.mp hq).1; omega
      have hqr : (0 : ℝ) < q := by exact_mod_cast hqp
      have hdiv : ((x / q : ℕ) : ℝ) ≤ (x : ℝ) / (q : ℝ) := by
        apply (le_div_iff₀ hqr).2
        exact_mod_cast Nat.div_mul_le_self x q
      rw [norm_mul]
      exact (mul_le_mul (hd q hq) (densityTight_mertens_norm_le (x / q))
        (norm_nonneg _) hL).trans (by
          simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hdiv hL)
    _ = L * (x : ℝ) * ∑ q ∈ Finset.Ioc y x, (q : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring

/-- Any density capped by 1/log(y) costs at most x on a root-to-square tail. -/
theorem norm_densityWeightedTransport_le_endpoint
    (d : ℕ → ℂ) {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2)
    (hd : ∀ q ∈ Finset.Ioc y x, ‖d q‖ ≤ (Real.log (y : ℝ))⁻¹) :
    ‖∑ q ∈ Finset.Ioc y x, d q * mertensSummatory (x / q)‖ ≤ (x : ℝ) := by
  by_cases hyx : y ≤ x
  · have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hl : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hs := densityTight_harmonic_tail_le_log (by omega : 1 ≤ y) hyx
    have hxlog : Real.log (x : ℝ) ≤ 2 * Real.log (y : ℝ) := by
      calc
        Real.log (x : ℝ) ≤ Real.log ((y : ℝ) ^ 2) :=
          Real.log_le_log hxpos (by exact_mod_cast hxy)
        _ = 2 * Real.log (y : ℝ) := by rw [Real.log_pow]; norm_num
    have htail : (∑ q ∈ Finset.Ioc y x, (q : ℝ)⁻¹) ≤ Real.log (y : ℝ) := by linarith
    have hb := norm_densityWeightedTransport_le_harmonic_tail d y x (inv_nonneg.mpr hl.le) hd
    calc
      _ ≤ (Real.log (y : ℝ))⁻¹ * (x : ℝ) * ∑ q ∈ Finset.Ioc y x, (q : ℝ)⁻¹ := hb
      _ ≤ (Real.log (y : ℝ))⁻¹ * (x : ℝ) * Real.log (y : ℝ) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = (x : ℝ) := by field_simp
  · rw [Finset.Ioc_eq_empty_of_le (Nat.le_of_not_ge hyx)]
    simp

/-- Constant improvement 4*x -> x for the unchanged equal-density model. -/
theorem norm_primeSieveEqualDensityBulk_le_endpoint
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    ‖primeSieveEqualDensityBulk y x‖ ≤ (x : ℝ) := by
  apply norm_densityWeightedTransport_le_endpoint _ hy hxy
  intro q _
  have h : 0 ≤ (Real.log (y : ℝ))⁻¹ := by
    apply inv_nonneg.mpr
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  change ‖(((Real.log (y : ℝ))⁻¹ : ℝ) : ℂ)‖ ≤ (Real.log (y : ℝ))⁻¹
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h, le_refl]

/-- Constant improvement 4*x -> x for the existing Li-increment model. -/
theorem norm_primeSievePNTBulk_le_endpoint
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    ‖primeSievePNTBulk y x‖ ≤ (x : ℝ) := by
  apply norm_densityWeightedTransport_le_endpoint _ hy hxy
  intro q hq
  exact norm_primeSievePNTDensity_le_inv_log hy (Finset.mem_Ioc.mp hq).1

/-- Exact signed cofactor formula, with the original integer floors retained. -/
theorem primeSieveUnitDensityBulk_eq_cofactor_sum (y x : ℕ) :
    primeSieveUnitDensityBulk y x =
      ∑ m ∈ Finset.Icc 1 (x / (y + 1)),
        canonicalMoebiusWeight m *
          ((((x / m : ℕ) : ℝ) - (y : ℝ) : ℝ) : ℂ) := by
  classical
  let n := x / (y + 1)
  have hmertens (q : ℕ) (hq : q ∈ Finset.Ioc y x) :
      mertensSummatory (x / q) =
        ∑ m ∈ Finset.Icc 1 n,
          if m * q ≤ x then canonicalMoebiusWeight m else 0 := by
    have hqp : 0 < q := by have := (Finset.mem_Ioc.mp hq).1; omega
    have hqn : x / q ≤ n :=
      (Finset.mem_Icc.mp (div_mem_primeSieveQuotientSupport_of_mem_Ioc hq)).2
    rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
    unfold cofactorMobiusPrefixMass
    rw [← Finset.sum_filter]
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hm1, hmq⟩
      exact ⟨⟨hm1, hmq.trans hqn⟩, (Nat.le_div_iff_mul_le hqp).mp hmq⟩
    · rintro ⟨⟨hm1, _⟩, hmul⟩
      exact ⟨hm1, (Nat.le_div_iff_mul_le hqp).mpr hmul⟩
  unfold primeSieveUnitDensityBulk
  rw [Finset.sum_congr rfl hmertens, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hmp : 0 < m := (Finset.mem_Icc.mp hm).1
  have hmN : m ≤ n := (Finset.mem_Icc.mp hm).2
  have hmul : m * (y + 1) ≤ x := (Nat.le_div_iff_mul_le (by omega)).mp hmN
  have hydiv : y ≤ x / m := by
    apply (Nat.le_div_iff_mul_le hmp).mpr
    nlinarith
  have hf : (Finset.Ioc y x).filter (fun q => m * q ≤ x) = Finset.Ioc y (x / m) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hyq, _⟩, hmq⟩
      exact ⟨hyq, (Nat.le_div_iff_mul_le hmp).mpr (by simpa [Nat.mul_comm] using hmq)⟩
    · rintro ⟨hyq, hqdiv⟩
      exact ⟨⟨hyq, hqdiv.trans (Nat.div_le_self x m)⟩,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hmp).mp hqdiv⟩
  rw [← Finset.sum_filter, hf, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  push_cast [Nat.cast_sub hydiv]
  ring

/-- Signed reciprocal cancellation improves the unit-density bound to 2*x,
for every pair of natural cutoffs, not just the square clock. -/
theorem norm_primeSieveUnitDensityBulk_le_two_mul (y x : ℕ) :
    ‖primeSieveUnitDensityBulk y x‖ ≤ 2 * (x : ℝ) := by
  classical
  let n := x / (y + 1)
  let r : ℕ → ℝ := fun m => (y : ℝ) + (x : ℝ) / (m : ℝ) - ((x / m : ℕ) : ℝ)
  have hr (m : ℕ) (hm : m ∈ Finset.Icc 1 n) : 0 ≤ r m ∧ r m ≤ (y : ℝ) + 1 := by
    have hmp : 0 < m := (Finset.mem_Icc.mp hm).1
    have hmr : (0 : ℝ) < m := by exact_mod_cast hmp
    have hlo : ((x / m : ℕ) : ℝ) ≤ (x : ℝ) / (m : ℝ) := by
      apply (le_div_iff₀ hmr).mpr
      exact_mod_cast Nat.div_mul_le_self x m
    have hhi : (x : ℝ) / (m : ℝ) < ((x / m : ℕ) : ℝ) + 1 := by
      apply (div_lt_iff₀ hmr).mpr
      exact_mod_cast Nat.lt_mul_div_succ x hmp
    dsimp [r]
    constructor <;> linarith
  have hid : primeSieveUnitDensityBulk y x =
      (x : ℂ) * (nativeMertensRecip n : ℂ) -
        ∑ m ∈ Finset.Icc 1 n, canonicalMoebiusWeight m * (r m : ℂ) := by
    rw [primeSieveUnitDensityBulk_eq_cofactor_sum]
    unfold nativeMertensRecip
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    dsimp [r]
    simp only [canonicalMoebiusWeight]
    push_cast
    ring
  have herr : ‖∑ m ∈ Finset.Icc 1 n, canonicalMoebiusWeight m * (r m : ℂ)‖ ≤ (x : ℝ) := by
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 n, ‖canonicalMoebiusWeight m * (r m : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc 1 n, ((y : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr m hm).1]
        exact (mul_le_mul_of_nonneg_right (norm_canonicalMoebiusWeight_le_one m) (hr m hm).1).trans (by simpa using (hr m hm).2)
      _ = (n : ℝ) * ((y : ℝ) + 1) := by simp
      _ ≤ (x : ℝ) := by exact_mod_cast Nat.div_mul_le_self x (y + 1)
  rw [hid]
  calc
    _ ≤ ‖(x : ℂ) * (nativeMertensRecip n : ℂ)‖ +
        ‖∑ m ∈ Finset.Icc 1 n, canonicalMoebiusWeight m * (r m : ℂ)‖ := norm_sub_le _ _
    _ ≤ (x : ℝ) * 1 + (x : ℝ) := by
      apply add_le_add _ herr
      rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (nativeMertensRecip_abs_le_one n) (Nat.cast_nonneg x)
    _ = 2 * (x : ℝ) := by ring

/-- A logarithmic improvement obtained from actual signed Mobius cancellation. -/
theorem norm_primeSieveEqualDensityBulk_le_two_div_log
    {y : ℕ} (hy : 2 ≤ y) (x : ℕ) :
    ‖primeSieveEqualDensityBulk y x‖ ≤ 2 * (x : ℝ) / Real.log (y : ℝ) := by
  have hl : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  rw [primeSieveEqualDensityBulk_eq_scaled_unit, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hl)]
  calc
    _ ≤ (Real.log (y : ℝ))⁻¹ * (2 * (x : ℝ)) :=
      mul_le_mul_of_nonneg_left (norm_primeSieveUnitDensityBulk_le_two_mul y x) (by positivity)
    _ = 2 * (x : ℝ) / Real.log (y : ℝ) := by ring

/-- Retain the better of the old-scale and logarithmically improved envelopes. -/
theorem primeSieveEqualDensityBulk_energy_tight
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    ‖primeSieveEqualDensityBulk y x‖ ^ 2 ≤
      min ((x : ℝ) ^ 2) (4 * (x : ℝ) ^ 2 / Real.log (y : ℝ) ^ 2) := by
  have ha := mul_self_le_mul_self (norm_nonneg _) (norm_primeSieveEqualDensityBulk_le_endpoint hy hxy)
  have hb := mul_self_le_mul_self (norm_nonneg _) (norm_primeSieveEqualDensityBulk_le_two_div_log hy x)
  apply le_min
  · nlinarith
  · convert hb using 1 <;> ring

/-- Improved error constant with the exact signed subtraction unchanged. -/
theorem norm_primeSievePNTError_le_two_mul
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) (hroot : Nat.sqrt x < y) :
    ‖primeSievePNTError y x‖ ≤ 2 * (x : ℝ) := by
  rw [primeSievePNTError_eq_tail_sub_bulk]
  exact (norm_sub_le _ _).trans (by
    have ht := norm_primeSieveMertensPrimeTail_le_endpoint hroot
    have hb := norm_primeSievePNTBulk_le_endpoint hy hxy
    linarith)

/-- Signed diagonal transfer with an explicit daughter-coefficient budget.
This is conditional algebra, not a new arithmetic hypothesis or an RH proof. -/
theorem densityTight_signed_energy_budget
    (a e D E L b d Cb Ce θ : ℝ)
    (hθ : 0 < θ) (hD : D ≤ 3 * L)
    (hb : a ^ 2 - D ≤ b * E + Cb * L)
    (he : e ^ 2 ≤ d * E + Ce * L) :
    (a - e) ^ 2 - D ≤
      ((1 + θ) * b + (1 + θ⁻¹) * d) * E +
      ((1 + θ) * Cb + (1 + θ⁻¹) * Ce + 3 * θ) * L := by
  have hθ0 : 0 ≤ θ := hθ.le
  have hi : 0 ≤ θ⁻¹ := inv_nonneg.mpr hθ0
  have hprod : θ * θ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hθ)
  have hs := mul_nonneg hi (sq_nonneg (θ * a + e))
  have hy : (a - e) ^ 2 ≤ (1 + θ) * a ^ 2 + (1 + θ⁻¹) * e ^ 2 := by
    have hid : θ⁻¹ * (θ * a + e) ^ 2 = θ * a ^ 2 + 2 * a * e + θ⁻¹ * e ^ 2 := by
      field_simp
      ring
    rw [hid] at hs
    nlinarith
  have hbb := mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ 1 + θ)
  have hee := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ 1 + θ⁻¹)
  have hdd := mul_le_mul_of_nonneg_left hD hθ0
  nlinarith

end RHLean.Analysis
