import Mathlib
import RHLean.Analysis.PrimeSievePNTCentering

/-!
# Universal finite bounds for equal-density and PNT-density transport

This is an unconditional baseline for iteration, not an RH-scale estimate.
The PNT model is the EXISTING Li-increment model, including its exact error.
The equal-density model freezes the density at 1/log(y) on every integer site.
All signed terms are assembled in their existing sums before energy is taken.
The coarse estimates intentionally use the triangle inequality only to obtain
an explicit all-scale starting bound; no cancellation saving is asserted.

For 2 <= y and x <= y^2, both model amplitudes are at most 4*x, hence
both model energies are at most 16*x^2. Above sqrt(x), the exact prime
transport has amplitude at most x; its Li-model error is at most 5*x.
No asymptotic PNT error theorem, numerical cutoff, or analytic assumption is used.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace RHLean.Analysis
open RHLean.Arithmetic RHLean.Proof

/-- Constant density, frozen at the lower endpoint. Each site represents
spacing log(y); this is a comparison measure, not a replacement prime system. -/
def primeSieveEqualDensityBulk (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x,
    (((Real.log (y : ℝ))⁻¹ : ℝ) : ℂ) * mertensSummatory (x / q)

/-- Unit-spacing reference, before the constant density is applied. -/
def primeSieveUnitDensityBulk (y x : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc y x, mertensSummatory (x / q)

/-- Exact equal-density factorization. -/
theorem primeSieveEqualDensityBulk_eq_scaled_unit (y x : ℕ) :
    primeSieveEqualDensityBulk y x =
      (((Real.log (y : ℝ))⁻¹ : ℝ) : ℂ) * primeSieveUnitDensityBulk y x := by
  unfold primeSieveEqualDensityBulk primeSieveUnitDensityBulk
  rw [Finset.mul_sum]

private theorem densityBaseline_mertens_norm_le (n : ℕ) :
    ‖mertensSummatory n‖ ≤ (n : ℝ) := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory n]
  unfold cofactorMobiusPrefixMass
  calc
    ‖∑ m ∈ Finset.Icc 1 n, canonicalMoebiusWeight m‖ ≤
        ∑ m ∈ Finset.Icc 1 n, ‖canonicalMoebiusWeight m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m _hm
      exact norm_canonicalMoebiusWeight_le_one m
    _ = (n : ℝ) := by simp

/-- A uniform coefficient cap gives an explicit harmonic envelope on the
complete signed transport. This helper works for arbitrary complex weights. -/
theorem norm_densityWeightedTransport_le_harmonic
    (d : ℕ → ℂ) (y x : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ q ∈ Finset.Ioc y x, ‖d q‖ ≤ L) :
    ‖∑ q ∈ Finset.Ioc y x, d q * mertensSummatory (x / q)‖ ≤
      L * (x : ℝ) * (harmonic x : ℝ) := by
  have hsum :
      (∑ q ∈ Finset.Ioc y x, (q : ℝ)⁻¹) ≤
        ∑ q ∈ Finset.Icc 1 x, (q : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      rcases Finset.mem_Ioc.mp hq with ⟨hqy, hqx⟩
      exact Finset.mem_Icc.mpr ⟨by omega, hqx⟩
    · intro q _hq _hnot
      positivity
  calc
    ‖∑ q ∈ Finset.Ioc y x, d q * mertensSummatory (x / q)‖ ≤
        ∑ q ∈ Finset.Ioc y x, ‖d q * mertensSummatory (x / q)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Ioc y x, L * ((x : ℝ) * (q : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := by
        have := (Finset.mem_Ioc.mp hq).1
        omega
      have hqr : (0 : ℝ) < q := by exact_mod_cast hqpos
      have hdiv : ((x / q : ℕ) : ℝ) ≤ (x : ℝ) / (q : ℝ) := by
        apply (le_div_iff₀ hqr).2
        exact_mod_cast Nat.div_mul_le_self x q
      rw [norm_mul]
      calc
        ‖d q‖ * ‖mertensSummatory (x / q)‖ ≤ L * ((x / q : ℕ) : ℝ) :=
          mul_le_mul (hd q hq) (densityBaseline_mertens_norm_le (x / q))
            (norm_nonneg _) hL
        _ ≤ L * ((x : ℝ) * (q : ℝ)⁻¹) := by
          simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hdiv hL
    _ = L * (x : ℝ) * ∑ q ∈ Finset.Ioc y x, (q : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring
    _ ≤ L * (x : ℝ) * ∑ q ∈ Finset.Icc 1 x, (q : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hL (Nat.cast_nonneg x))
    _ = L * (x : ℝ) * (harmonic x : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- Universal unit-spacing baseline, retaining the explicit logarithmic loss. -/
theorem norm_primeSieveUnitDensityBulk_le (y x : ℕ) :
    ‖primeSieveUnitDensityBulk y x‖ ≤ (x : ℝ) * (1 + Real.log (x : ℝ)) := by
  have h := norm_densityWeightedTransport_le_harmonic (fun _ => 1) y x
    (L := 1) (by norm_num) (by intro q _hq; norm_num)
  simp only [one_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log x)
    (Nat.cast_nonneg x))

private theorem densityBaseline_half_le_log {y : ℕ} (hy : 2 ≤ y) :
    (1 / 2 : ℝ) ≤ Real.log (y : ℝ) := by
  have hyr : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hypos : (0 : ℝ) < y := by linarith
  have hinv : (y : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    (inv_le_inv₀ hypos (by norm_num)).2 hyr
  have hlog := Real.one_sub_inv_le_log_of_pos hypos
  norm_num at hinv
  linarith

private theorem densityBaseline_harmonic_div_log_le_four
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    (harmonic x : ℝ) / Real.log (y : ℝ) ≤ 4 := by
  have hhalf := densityBaseline_half_le_log hy
  have hlogpos : 0 < Real.log (y : ℝ) := by linarith
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxpos : (0 : ℝ) < x := by exact_mod_cast Nat.pos_of_ne_zero hx0
  have hlogx : Real.log (x : ℝ) ≤ 2 * Real.log (y : ℝ) := by
    calc
      Real.log (x : ℝ) ≤ Real.log ((y : ℝ) ^ 2) :=
        Real.log_le_log hxpos (by exact_mod_cast hxy)
      _ = 2 * Real.log (y : ℝ) := by rw [Real.log_pow]; norm_num
  apply (div_le_iff₀ hlogpos).2
  have hH := harmonic_le_one_add_log x
  linarith

private theorem densityBaseline_norm_le_four_mul
    (d : ℕ → ℂ) {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2)
    (hd : ∀ q ∈ Finset.Ioc y x, ‖d q‖ ≤ (Real.log (y : ℝ))⁻¹) :
    ‖∑ q ∈ Finset.Ioc y x, d q * mertensSummatory (x / q)‖ ≤ 4 * (x : ℝ) := by
  have hlog0 : 0 ≤ Real.log (y : ℝ) := (densityBaseline_half_le_log hy).trans' (by norm_num)
  have h := norm_densityWeightedTransport_le_harmonic d y x
    (inv_nonneg.mpr hlog0) hd
  calc
    ‖∑ q ∈ Finset.Ioc y x, d q * mertensSummatory (x / q)‖ ≤
        (Real.log (y : ℝ))⁻¹ * (x : ℝ) * (harmonic x : ℝ) := h
    _ = (x : ℝ) * ((harmonic x : ℝ) / Real.log (y : ℝ)) := by ring
    _ ≤ (x : ℝ) * 4 := mul_le_mul_of_nonneg_left
      (densityBaseline_harmonic_div_log_le_four hy hxy) (Nat.cast_nonneg x)
    _ = 4 * (x : ℝ) := by ring

/-- Every root-to-square equal-density model has universal amplitude constant 4. -/
theorem norm_primeSieveEqualDensityBulk_le_four_mul
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    ‖primeSieveEqualDensityBulk y x‖ ≤ 4 * (x : ℝ) := by
  apply densityBaseline_norm_le_four_mul _ hy hxy
  intro q _hq
  have hl : 0 ≤ (Real.log (y : ℝ))⁻¹ :=
    inv_nonneg.mpr (le_trans (by norm_num) (densityBaseline_half_le_log hy))
  change ‖(((Real.log (y : ℝ))⁻¹ : ℝ) : ℂ)‖ ≤ (Real.log (y : ℝ))⁻¹
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl, le_refl]

private theorem densityBaseline_invLog_intervalIntegrable
    {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := (le_min ha hb).trans ht.1
  exact ((Real.continuousAt_log (by linarith)).inv₀
    (ne_of_gt (Real.log_pos (by linarith)))).continuousWithinAt

/-- The actual Li increment is bounded by the frozen lower-end density.
The integral endpoints are unchanged; no lattice or rounding term is dropped. -/
theorem norm_primeSievePNTDensity_le_inv_log
    {y q : ℕ} (hy : 2 ≤ y) (hyq : y < q) :
    ‖primeSievePNTDensity q‖ ≤ (Real.log (y : ℝ))⁻¹ := by
  have hpred : q - 1 + 1 = q := by omega
  have hyPred : y ≤ q - 1 := by omega
  have ha2 : (2 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ q - 1 by omega)
  have hb2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 2 ≤ q by omega)
  have hab : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.sub_le q 1
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (densityBaseline_invLog_intervalIntegrable (a := 2) (by norm_num) ha2)
    (densityBaseline_invLog_intervalIntegrable ha2 hb2)
  have hdiff : logarithmicIntegralFromTwo (q : ℝ) -
        logarithmicIntegralFromTwo ((q - 1 : ℕ) : ℝ) =
      ∫ t in ((q - 1 : ℕ) : ℝ)..(q : ℝ), (Real.log t)⁻¹ := by
    unfold logarithmicIntegralFromTwo
    linarith [hadd]
  have hylog : 0 < Real.log (y : ℝ) := by
    have := densityBaseline_half_le_log hy
    linarith
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := ((q - 1 : ℕ) : ℝ)) (b := (q : ℝ))
    (C := (Real.log (y : ℝ))⁻¹) (f := fun t : ℝ => (Real.log t)⁻¹) (by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have hyt : (y : ℝ) ≤ t := le_trans (by exact_mod_cast hyPred) ht.1.le
      have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
      have hlog := Real.log_le_log hypos hyt
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hylog.trans_le hlog))]
      exact (inv_le_inv₀ (hylog.trans_le hlog) hylog).2 hlog)
  have hlen : |(q : ℝ) - ((q - 1 : ℕ) : ℝ)| = 1 := by
    have hp : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by exact_mod_cast hpred
    rw [show (q : ℝ) - ((q - 1 : ℕ) : ℝ) = 1 by linarith]
    norm_num
  rw [hlen, mul_one] at hbound
  simpa only [primeSievePNTDensity, hdiff, Complex.norm_real, Real.norm_eq_abs] using hbound

/-- Universal bound on the existing, non-redefined Li-density transport. -/
theorem norm_primeSievePNTBulk_le_four_mul
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    ‖primeSievePNTBulk y x‖ ≤ 4 * (x : ℝ) := by
  apply densityBaseline_norm_le_four_mul _ hy hxy
  intro q hq
  exact norm_primeSievePNTDensity_le_inv_log hy (Finset.mem_Ioc.mp hq).1

/-- Before estimating, reassemble the real prime transport as one signed
largest-prime source packet. This avoids counting a source more than once. -/
theorem norm_primeSieveMertensPrimeTail_le_endpoint
    {y x : ℕ} (hroot : Nat.sqrt x < y) :
    ‖primeSieveMertensPrimeTail y x‖ ≤ (x : ℝ) := by
  classical
  have hid : (∑ n ∈ primeSieveHighSourceSet y x, canonicalMoebiusWeight n) =
      -primeSieveMertensPrimeTail y x := by
    rw [sum_primeSieveHighSourceSet_eq_pairProducts y x hroot,
      sum_primeSieveTransportPairSet_eq_neg_cofactorMass y x hroot,
      primeSieveTransportCofactorMass_eq_mertensPrimeTail y x]
  have hcard : (primeSieveHighSourceSet y x).card ≤ x := by
    calc
      (primeSieveHighSourceSet y x).card ≤ (Finset.Icc 1 x).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = x := by simp
  calc
    ‖primeSieveMertensPrimeTail y x‖ =
        ‖∑ n ∈ primeSieveHighSourceSet y x, canonicalMoebiusWeight n‖ := by
      rw [hid, norm_neg]
    _ ≤ ∑ n ∈ primeSieveHighSourceSet y x, ‖canonicalMoebiusWeight n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ primeSieveHighSourceSet y x, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _hn
      exact norm_canonicalMoebiusWeight_le_one n
    _ = ((primeSieveHighSourceSet y x).card : ℝ) := by simp
    _ ≤ (x : ℝ) := by exact_mod_cast hcard

/-- Exact model subtraction, with the original signed error retained. -/
theorem primeSievePNTError_eq_tail_sub_bulk (y x : ℕ) :
    primeSievePNTError y x = primeSieveMertensPrimeTail y x - primeSievePNTBulk y x := by
  rw [primeSieveMertensPrimeTail_eq_pntBulk_add_error]
  ring

/-- Universal all-scale bound for the actual prime-minus-Li substitution error. -/
theorem norm_primeSievePNTError_le_five_mul
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) (hroot : Nat.sqrt x < y) :
    ‖primeSievePNTError y x‖ ≤ 5 * (x : ℝ) := by
  rw [primeSievePNTError_eq_tail_sub_bulk]
  calc
    ‖primeSieveMertensPrimeTail y x - primeSievePNTBulk y x‖ ≤
        ‖primeSieveMertensPrimeTail y x‖ + ‖primeSievePNTBulk y x‖ := norm_sub_le _ _
    _ ≤ (x : ℝ) + 4 * (x : ℝ) := add_le_add
      (norm_primeSieveMertensPrimeTail_le_endpoint hroot)
      (norm_primeSievePNTBulk_le_four_mul hy hxy)
    _ = 5 * (x : ℝ) := by ring

/-- Equal-density energy baseline with one universal constant. -/
theorem primeSieveEqualDensityBulk_energy_le_sixteen
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    ‖primeSieveEqualDensityBulk y x‖ ^ 2 ≤ 16 * (x : ℝ) ^ 2 := by
  have h := mul_self_le_mul_self (norm_nonneg _) (norm_primeSieveEqualDensityBulk_le_four_mul hy hxy)
  nlinarith

/-- PNT-density energy baseline on the existing signed bulk. -/
theorem primeSievePNTBulk_energy_le_sixteen
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    ‖primeSievePNTBulk y x‖ ^ 2 ≤ 16 * (x : ℝ) ^ 2 := by
  have h := mul_self_le_mul_self (norm_nonneg _) (norm_primeSievePNTBulk_le_four_mul hy hxy)
  nlinarith

/-- Error-energy baseline: no numerical range and no assumed PNT remainder. -/
theorem primeSievePNTError_energy_le_twentyFive
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) (hroot : Nat.sqrt x < y) :
    ‖primeSievePNTError y x‖ ^ 2 ≤ 25 * (x : ℝ) ^ 2 := by
  have h := mul_self_le_mul_self (norm_nonneg _) (norm_primeSievePNTError_le_five_mul hy hxy hroot)
  nlinarith

/-- Real signed energy-transfer identity. The cross term is retained, not
silently absorbed when replacing the true prime packet by a density model. -/
theorem densityBaseline_signed_energy_transfer (model error diagonal : ℝ) :
    (model - error) ^ 2 - diagonal =
      (model ^ 2 - diagonal) - 2 * model * error + error ^ 2 := by
  ring

/-- Direct production-clock corollary: one universal quartic bound for each
model and for the exact Li-substitution error, for every root R >= 2. -/
theorem primeDensity_squareEndpoint_universal (R : ℕ) (hR : 2 ≤ R) :
    ‖primeSieveEqualDensityBulk R (R ^ 2 - 1)‖ ^ 2 ≤ 16 * (R : ℝ) ^ 4 ∧
    ‖primeSievePNTBulk R (R ^ 2 - 1)‖ ^ 2 ≤ 16 * (R : ℝ) ^ 4 ∧
    ‖primeSievePNTError R (R ^ 2 - 1)‖ ^ 2 ≤ 25 * (R : ℝ) ^ 4 := by
  have hx : R ^ 2 - 1 ≤ R ^ 2 := Nat.sub_le _ _
  have hroot : Nat.sqrt (R ^ 2 - 1) < R := by
    apply Nat.sqrt_lt.mpr
    have hp : 0 < R * R := Nat.mul_pos (by omega) (by omega)
    simpa only [pow_two] using Nat.sub_lt hp (by norm_num : 0 < 1)
  have hxr : ((R ^ 2 - 1 : ℕ) : ℝ) ≤ (R : ℝ) ^ 2 := by exact_mod_cast hx
  have hxx := mul_self_le_mul_self (Nat.cast_nonneg (R ^ 2 - 1) : (0 : ℝ) ≤ _) hxr
  have heq := primeSieveEqualDensityBulk_energy_le_sixteen hR hx
  have hpnt := primeSievePNTBulk_energy_le_sixteen hR hx
  have herr := primeSievePNTError_energy_le_twentyFive hR hx hroot
  constructor
  · nlinarith
  constructor <;> nlinarith

end RHLean.Analysis
