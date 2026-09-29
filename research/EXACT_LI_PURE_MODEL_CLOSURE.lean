import Mathlib
import «research.ALL_SCALE_LI_DISPLACEMENT_REDUCTION»
import RHLean.Proof.FinitePartialMoments

/-!
# Pure exact-Li model closure spine

This file isolates the model-only closure mechanism needed after PR #814.

There are no actual-prime indicators and no prime-count discrepancy terms in the
main theorem below.  The theorem says that a uniformly bounded continuous
reference model plus an O(R) discrete/continuous transfer is already enough to
prove the exact all-scale Li square-root target.

The file also records degree-zero partial mass separately from the generic
natural-power API.  This avoids the 0^0 convention and matches the CDF/VaR
meaning of degree zero used by the NNS partial-moment formulation.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Proof

/-- Degree-zero lower partial mass: the weighted CDF/counting functional.
This is deliberately separate from `lowerPartialMomentNat 0`. -/
def degreeZeroLowerMass {ι : Type*}
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, if x i ≤ t then w i else 0

/-- Degree-zero upper partial mass. -/
def degreeZeroUpperMass {ι : Type*}
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, if t < x i then w i else 0

/-- Degree-zero lower plus upper mass is exactly the common total weight. -/
theorem degreeZeroLowerMass_add_upperMass
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) :
    degreeZeroLowerMass s w x t + degreeZeroUpperMass s w x t =
      ∑ i ∈ s, w i := by
  unfold degreeZeroLowerMass degreeZeroUpperMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : x i ≤ t
  · have hn : ¬ t < x i := not_lt.mpr h
    simp [h, hn]
  · have ht : t < x i := lt_of_not_ge h
    simp [h, ht]


/-! ## Degree-one transport control -/

/-- Weighted degree-one lower partial mass.  With threshold `t`, the point
`x i` contributes `w i * max (t - x i) 0`. -/
def weightedDegreeOneLowerMass {ι : Type*}
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, w i * negativePart (x i - t)

/-- Positive part is 1-Lipschitz. -/
theorem abs_positivePart_sub_positivePart_le (a b : ℝ) :
    |positivePart a - positivePart b| ≤ |a - b| := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · simp [positivePart, ha, hb]
    · have hb' : b ≤ 0 := le_of_not_ge hb
      have hab : 0 ≤ a - b := by linarith
      have hle : a ≤ a - b := by linarith
      simp [positivePart, ha, hb', abs_of_nonneg ha, abs_of_nonneg hab, hle]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    by_cases hb : 0 ≤ b
    · have hba : 0 ≤ b - a := by linarith
      have hle : b ≤ b - a := by linarith
      rw [abs_sub_comm a b]
      simp [positivePart, ha', hb, abs_of_nonneg hb, abs_of_nonneg hba, hle]
    · have hb' : b ≤ 0 := le_of_not_ge hb
      simp [positivePart, ha', hb']

/-- Negative part is 1-Lipschitz. -/
theorem abs_negativePart_sub_negativePart_le (a b : ℝ) :
    |negativePart a - negativePart b| ≤ |a - b| := by
  unfold negativePart
  have h := abs_positivePart_sub_positivePart_le (-a) (-b)
  calc
    |positivePart (-a) - positivePart (-b)| ≤ |-a - (-b)| := h
    _ = |a - b| := by
      rw [show -a - (-b) = -(a - b) by ring, abs_neg]

/-- **Degree-one common-mass transport inequality.**
For nonnegative common weights, moving support point `x i` to `y i` changes
the degree-one lower partial mass by at most mass times transport distance. -/
theorem abs_weightedDegreeOneLowerMass_sub_le_transport
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x y : ι → ℝ) (t : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    |weightedDegreeOneLowerMass s w x t -
        weightedDegreeOneLowerMass s w y t| ≤
      ∑ i ∈ s, w i * |x i - y i| := by
  unfold weightedDegreeOneLowerMass
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ s,
        (w i * negativePart (x i - t) -
          w i * negativePart (y i - t))|
        ≤ ∑ i ∈ s,
            |w i * negativePart (x i - t) -
              w i * negativePart (y i - t)| := by
            exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s,
          w i * |negativePart (x i - t) -
            negativePart (y i - t)| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← mul_sub, abs_mul, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ s, w i * |x i - y i| := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_left _ (hw i hi)
          have h := abs_negativePart_sub_negativePart_le (x i - t) (y i - t)
          simpa [sub_sub_sub_cancel_right] using h


/-! ## Critical Li collision summability -/

/-- The elementary logarithmic-harmonic tail used for the critical
freshness correction. -/
def exactLiLogHarmonicTail (p n : ℕ) : ℝ :=
  1 / (((n + 3 : ℕ) : ℝ) * (Real.log ((n + 3 : ℕ) : ℝ)) ^ p)

/-- Cauchy condensation gives summability for every logarithmic power p > 1.
This is entirely model-side real analysis. -/
theorem exactLiLogHarmonicTail_summable {p : ℕ} (hp : 1 < p) :
    Summable (exactLiLogHarmonicTail p) := by
  have hnonneg : ∀ n, 0 ≤ exactLiLogHarmonicTail p n := by
    intro n
    unfold exactLiLogHarmonicTail
    positivity
  have hmono : ∀ ⦃m n⦄, 0 < m → m ≤ n →
      exactLiLogHarmonicTail p n ≤ exactLiLogHarmonicTail p m := by
    intro m n _hm hmn
    unfold exactLiLogHarmonicTail
    have hmnNat : m + 3 ≤ n + 3 := by omega
    have hmnR : (((m + 3 : ℕ) : ℝ)) ≤ ((n + 3 : ℕ) : ℝ) := by
      exact_mod_cast hmnNat
    have hmpos : 0 < (((m + 3 : ℕ) : ℝ)) := by positivity
    have hlogm : 0 ≤ Real.log ((m + 3 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 3 by omega))
    have hlogmpos : 0 < Real.log ((m + 3 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m + 3 by omega))
    have hlogle :
        Real.log ((m + 3 : ℕ) : ℝ) ≤ Real.log ((n + 3 : ℕ) : ℝ) :=
      Real.log_le_log hmpos hmnR
    have hpowle : (Real.log ((m + 3 : ℕ) : ℝ)) ^ p ≤
        (Real.log ((n + 3 : ℕ) : ℝ)) ^ p :=
      pow_le_pow_left₀ hlogm hlogle p
    have hdenle :
        (((m + 3 : ℕ) : ℝ)) * (Real.log ((m + 3 : ℕ) : ℝ)) ^ p ≤
          ((n + 3 : ℕ) : ℝ) * (Real.log ((n + 3 : ℕ) : ℝ)) ^ p := by
      exact mul_le_mul hmnR hpowle (by positivity) (by positivity)
    exact one_div_le_one_div_of_le
      (mul_pos hmpos (pow_pos hlogmpos p)) hdenle
  rw [← summable_condensed_iff_of_nonneg hnonneg hmono]
  rw [← summable_nat_add_iff 1 (G := ℝ)]
  let D : ℝ := 1 / (Real.log 2) ^ p
  have hpseries0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) :=
    Real.summable_one_div_nat_pow.mpr hp
  have hpseries : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ p)) :=
    (summable_nat_add_iff 1 (G := ℝ)).2 hpseries0
  have hmajor :
      Summable (fun k : ℕ => D * (1 / (((k + 1 : ℕ) : ℝ) ^ p))) :=
    hpseries.mul_left D
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by positivity) (hnonneg (2 ^ (k + 1)))) ?_ hmajor
  intro k
  let q : ℕ := 2 ^ (k + 1)
  have hqNatPos : 0 < q := by
    dsimp [q]
    positivity
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqNatPos
  have hqleNat : q ≤ q + 3 := by omega
  have hqle : (q : ℝ) ≤ ((q + 3 : ℕ) : ℝ) := by exact_mod_cast hqleNat
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log (q : ℝ) =
      ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
    dsimp [q]
    push_cast
    rw [Real.log_pow]
    push_cast
    rfl
  have hlogle : Real.log (q : ℝ) ≤ Real.log ((q + 3 : ℕ) : ℝ) :=
    Real.log_le_log hqpos hqle
  have hlogqpos : 0 < Real.log (q : ℝ) := by
    rw [hlogq]
    positivity
  have hpowle : (Real.log (q : ℝ)) ^ p ≤
      (Real.log ((q + 3 : ℕ) : ℝ)) ^ p :=
    pow_le_pow_left₀ hlogqpos.le hlogle p
  have hsmallpos : 0 < (q : ℝ) * (Real.log (q : ℝ)) ^ p := by positivity
  have hq3nat : 1 < q + 3 := by omega
  have hq3 : (1 : ℝ) < ((q + 3 : ℕ) : ℝ) := by exact_mod_cast hq3nat
  have hlogbigpos : 0 < Real.log ((q + 3 : ℕ) : ℝ) := Real.log_pos hq3
  have hbigpos :
      0 < ((q + 3 : ℕ) : ℝ) * (Real.log ((q + 3 : ℕ) : ℝ)) ^ p :=
    mul_pos (by positivity) (pow_pos hlogbigpos p)
  have hdenle : (q : ℝ) * (Real.log (q : ℝ)) ^ p ≤
      ((q + 3 : ℕ) : ℝ) * (Real.log ((q + 3 : ℕ) : ℝ)) ^ p := by
    exact mul_le_mul hqle hpowle (by positivity) (by positivity)
  have hquot :
      (q : ℝ) /
          (((q + 3 : ℕ) : ℝ) * (Real.log ((q + 3 : ℕ) : ℝ)) ^ p) ≤
        (q : ℝ) / ((q : ℝ) * (Real.log (q : ℝ)) ^ p) := by
    exact (div_le_div_iff_of_pos_left hqpos hbigpos hsmallpos).2 hdenle
  calc
    (2 : ℝ) ^ (k + 1) * exactLiLogHarmonicTail p (2 ^ (k + 1)) =
        (q : ℝ) /
          (((q + 3 : ℕ) : ℝ) * (Real.log ((q + 3 : ℕ) : ℝ)) ^ p) := by
      dsimp [q, exactLiLogHarmonicTail]
      push_cast
      ring
    _ ≤ (q : ℝ) / ((q : ℝ) * (Real.log (q : ℝ)) ^ p) := hquot
    _ = 1 / (Real.log (q : ℝ)) ^ p := by
      field_simp [ne_of_gt hqpos]
    _ = D * (1 / (((k + 1 : ℕ) : ℝ) ^ p)) := by
      dsimp [D]
      rw [hlogq, mul_pow]
      field_simp [ne_of_gt hlog2]


private theorem exactLi_invLog_intervalIntegrable
    {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := (le_min ha hb).trans ht.1
  exact ((Real.continuousAt_log (by linarith)).inv₀
    (ne_of_gt (Real.log_pos (by linarith)))).continuousWithinAt

/-- One exact Li singleton mass is at most the inverse logarithm at any
integer lower anchor inside its unit bin. -/
theorem exactLi_norm_pntDensity_le_inv_log
    {y q : ℕ} (hy : 2 ≤ y) (hyq : y < q) :
    ‖primeSievePNTDensity q‖ ≤ (Real.log (y : ℝ))⁻¹ := by
  have hpred : q - 1 + 1 = q := by omega
  have hyPred : y ≤ q - 1 := by omega
  have ha2 : (2 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ q - 1 by omega)
  have hb2 : (2 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (show 2 ≤ q by omega)
  have hab : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.sub_le q 1
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (exactLi_invLog_intervalIntegrable (a := 2) (by norm_num) ha2)
    (exactLi_invLog_intervalIntegrable ha2 hb2)
  have hdiff : logarithmicIntegralFromTwo (q : ℝ) -
        logarithmicIntegralFromTwo ((q - 1 : ℕ) : ℝ) =
      ∫ t in ((q - 1 : ℕ) : ℝ)..(q : ℝ), (Real.log t)⁻¹ := by
    unfold logarithmicIntegralFromTwo
    linarith [hadd]
  have hylog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := ((q - 1 : ℕ) : ℝ)) (b := (q : ℝ))
    (C := (Real.log (y : ℝ))⁻¹) (f := fun t : ℝ => (Real.log t)⁻¹) (by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have hyt : (y : ℝ) ≤ t :=
        le_trans (by exact_mod_cast hyPred) ht.1.le
      have hypos : (0 : ℝ) < y := by
        exact_mod_cast (show 0 < y by omega)
      have hlog := Real.log_le_log hypos hyt
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hylog.trans_le hlog))]
      exact (inv_le_inv₀ (hylog.trans_le hlog) hylog).2 hlog)
  have hlen : |(q : ℝ) - ((q - 1 : ℕ) : ℝ)| = 1 := by
    have hp : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
      exact_mod_cast hpred
    rw [show (q : ℝ) - ((q - 1 : ℕ) : ℝ) = 1 by linarith]
    norm_num
  rw [hlen, mul_one] at hbound
  simpa only [primeSievePNTDensity, hdiff, Complex.norm_real,
    Real.norm_eq_abs] using hbound

/-- Critical freshness correction is absolutely summable.
For the repository's exact singleton Li masses w_q, the second-order
half-weighted correction |w_q|^2/q has finite total mass. -/
theorem exactLiCriticalCollision_summable :
    Summable (fun q : ℕ =>
      ‖primeSievePNTDensity q‖ ^ 2 / (q : ℝ)) := by
  rw [← summable_nat_add_iff 4 (G := ℝ)]
  have hmajor := exactLiLogHarmonicTail_summable (p := 2) (by norm_num)
  apply Summable.of_nonneg_of_le
    (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) ?_ hmajor
  intro n
  let q : ℕ := n + 4
  let y : ℕ := q - 1
  have hy2 : 2 ≤ y := by
    dsimp [q, y]
    omega
  have hyq : y < q := by
    dsimp [y]
    omega
  have hnorm : ‖primeSievePNTDensity q‖ ≤
      (Real.log (y : ℝ))⁻¹ :=
    exactLi_norm_pntDensity_le_inv_log hy2 hyq
  have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlogpos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hsq :
      ‖primeSievePNTDensity q‖ ^ 2 ≤
        ((Real.log (y : ℝ))⁻¹) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hyqR : (y : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.le_of_lt hyq)
  have hinv : (q : ℝ)⁻¹ ≤ (y : ℝ)⁻¹ :=
    (inv_le_inv₀ hqpos hypos).2 hyqR
  change ‖primeSievePNTDensity q‖ ^ 2 / (q : ℝ) ≤
    exactLiLogHarmonicTail 2 n
  rw [div_eq_mul_inv]
  calc
    ‖primeSievePNTDensity q‖ ^ 2 * (q : ℝ)⁻¹ ≤
        ((Real.log (y : ℝ))⁻¹) ^ 2 * (y : ℝ)⁻¹ := by
      exact mul_le_mul hsq hinv (by positivity) (sq_nonneg _)
    _ = exactLiLogHarmonicTail 2 n := by
      dsimp [exactLiLogHarmonicTail, q, y]
      simp only [one_div, mul_inv_rev, inv_pow]
      ring


/-! ## Sharp finite Abel return from the critical half-weight -/

/-- The increment recovered from a half-weighted prefix profile. -/
def sqrtAbelIncrement (A : ℕ → ℂ) (n : ℕ) : ℂ :=
  (Real.sqrt (n : ℝ) : ℂ) * (A n - A (n - 1))

private theorem sum_Ico_forwardDiff_real
    (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, (f (k + 1) - f k)) = f b - f a := by
  rw [Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub f b,
    Finset.sum_range_sub f a]
  abel

/-- Exact finite Abel identity at square-root weight. -/
theorem sum_sqrtAbelIncrement_eq
    (A : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, sqrtAbelIncrement A n) =
      (Real.sqrt (N : ℝ) : ℂ) * A N -
        ∑ n ∈ Finset.Ico 1 N,
          A n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) -
            Real.sqrt (n : ℝ) : ℝ) : ℂ) := by
  induction N with
  | zero =>
      simp [sqrtAbelIncrement]
  | succ N ih =>
      by_cases hN : N = 0
      · subst N
        norm_num [sqrtAbelIncrement]
      · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
        rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1),
          Finset.sum_Ico_succ_top hN1, ih]
        unfold sqrtAbelIncrement
        push_cast
        ring

/-- Square-root increments telescope exactly. -/
theorem sum_Ico_sqrt_step {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N,
      (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))) =
      Real.sqrt (N : ℝ) - 1 := by
  have h := sum_Ico_forwardDiff_real
    (fun n : ℕ => Real.sqrt (n : ℝ)) hN
  simpa using h

/-- Quantitative square-root Abel return.  A uniform bound B on the
half-weighted prefix profile costs at most 2 B sqrt(N) in the unweighted
reconstruction. -/
theorem norm_sum_sqrtAbelIncrement_le
    (A : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hN : 1 ≤ N) (hB : 0 ≤ B)
    (hA : ∀ n, n ≤ N → ‖A n‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc 1 N, sqrtAbelIncrement A n‖ ≤
      2 * Real.sqrt (N : ℝ) * B := by
  rw [sum_sqrtAbelIncrement_eq]
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hsqrtN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hhead :
      ‖(Real.sqrt (N : ℝ) : ℂ) * A N‖ ≤ Real.sqrt (N : ℝ) * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsqrtN]
    exact mul_le_mul_of_nonneg_left (hA N le_rfl) hsqrtN
  have htail :
      ‖∑ n ∈ Finset.Ico 1 N,
          A n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) -
            Real.sqrt (n : ℝ) : ℝ) : ℂ)‖ ≤
        (Real.sqrt (N : ℝ) - 1) * B := by
    calc
      ‖∑ n ∈ Finset.Ico 1 N,
          A n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) -
            Real.sqrt (n : ℝ) : ℝ) : ℂ)‖
          ≤ ∑ n ∈ Finset.Ico 1 N,
              ‖A n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) -
                Real.sqrt (n : ℝ) : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ico 1 N,
            B * (Real.sqrt ((n + 1 : ℕ) : ℝ) -
              Real.sqrt (n : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnle : n ≤ N := (Finset.mem_Ico.mp hn).2.le
          have hstep : 0 ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) -
              Real.sqrt (n : ℝ) := by
            exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by norm_num))
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hstep]
          exact mul_le_mul (hA n hnle) le_rfl hstep (norm_nonneg _)
      _ = B * (∑ n ∈ Finset.Ico 1 N,
            (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))) := by
          rw [Finset.mul_sum]
      _ = B * (Real.sqrt (N : ℝ) - 1) := by
          rw [sum_Ico_sqrt_step hN]
      _ = (Real.sqrt (N : ℝ) - 1) * B := by ring
  calc
    ‖(Real.sqrt (N : ℝ) : ℂ) * A N -
        ∑ n ∈ Finset.Ico 1 N,
          A n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) -
            Real.sqrt (n : ℝ) : ℝ) : ℂ)‖
        ≤ ‖(Real.sqrt (N : ℝ) : ℂ) * A N‖ +
          ‖∑ n ∈ Finset.Ico 1 N,
            A n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) -
              Real.sqrt (n : ℝ) : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ Real.sqrt (N : ℝ) * B +
        (Real.sqrt (N : ℝ) - 1) * B := add_le_add hhead htail
    _ ≤ 2 * Real.sqrt (N : ℝ) * B := by
      have hsqrt1 : 1 ≤ Real.sqrt (N : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
      nlinarith [mul_nonneg hB (sub_nonneg.mpr hsqrt1)]


/-! ## Critical half-prefix of the all-scale Li diagonal -/

/-- One increment of the diagonal all-scale state. -/
def allScaleLiDiagonalIncrement (L : ℕ → ℕ → ℂ) (n : ℕ) : ℂ :=
  L n n - L (n - 1) (n - 1)

/-- Critical half-weighted prefix of the diagonal increments. -/
def allScaleLiCriticalPrefix (L : ℕ → ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    allScaleLiDiagonalIncrement L n / (Real.sqrt (n : ℝ) : ℂ)

theorem allScaleLiCriticalPrefix_succ (L : ℕ → ℕ → ℂ) (N : ℕ) :
    allScaleLiCriticalPrefix L (N + 1) =
      allScaleLiCriticalPrefix L N +
        allScaleLiDiagonalIncrement L (N + 1) /
          (Real.sqrt ((N + 1 : ℕ) : ℝ) : ℂ) := by
  unfold allScaleLiCriticalPrefix
  rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1)]

/-- The Abel increment of the critical prefix is exactly the original diagonal
increment. -/
theorem sqrtAbelIncrement_allScaleLiCriticalPrefix
    (L : ℕ → ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    sqrtAbelIncrement (allScaleLiCriticalPrefix L) n =
      allScaleLiDiagonalIncrement L n := by
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hs := allScaleLiCriticalPrefix_succ L (n - 1)
  rw [hpred] at hs
  unfold sqrtAbelIncrement
  rw [hs]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsqrtne : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hsqrtpos)
  field_simp [hsqrtne]
  ring

/-- Diagonal increments telescope to the endpoint minus the zero endpoint. -/
theorem sum_allScaleLiDiagonalIncrement_eq (L : ℕ → ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, allScaleLiDiagonalIncrement L n) =
      L N N - L 0 0 := by
  induction N with
  | zero =>
      simp [allScaleLiDiagonalIncrement]
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1), ih]
      unfold allScaleLiDiagonalIncrement
      simp only [Nat.add_sub_cancel]
      ring

/-- Every all-scale Li state starts from the unit atom. -/
theorem allScaleLiState_zero_zero
    {L : ℕ → ℕ → ℂ} (hL : IsAllScaleLiState L) :
    L 0 0 = 1 := by
  change IsPrimeFrequencyState primeSievePNTDensity L at hL
  rw [hL 0 0]
  simp [primeFrequencyStep]

/-- The sole quantitative target left after the critical-coordinate reduction:
a universal bound on the half-weighted diagonal prefix. -/
def AllScaleLiCriticalPrefixBoundedStatement : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧
    ∀ (L : ℕ → ℕ → ℂ) (N : ℕ),
      IsAllScaleLiState L →
      ‖allScaleLiCriticalPrefix L N‖ ≤ B

/-- A bounded critical half-prefix already closes the pure all-scale Li
square-root theorem by the sharp finite Abel return. -/
theorem allScaleLiSquareRootBounded_of_criticalPrefixBounded
    (hcrit : AllScaleLiCriticalPrefixBoundedStatement) :
    AllScaleLiSquareRootBoundedStatement := by
  rcases hcrit with ⟨B, hB, hcrit⟩
  refine ⟨(2 * B + 1) ^ 2, sq_nonneg _, ?_⟩
  intro L R hL hsat hR
  let X : ℕ := squareRootEndpoint R
  have hX1 : 1 ≤ X := by
    dsimp [X, squareRootEndpoint]
    have hR2 : 4 ≤ R ^ 2 := by nlinarith
    omega
  have hprefix : ∀ n, n ≤ X → ‖allScaleLiCriticalPrefix L n‖ ≤ B := by
    intro n hn
    exact hcrit L n hL
  have habel :=
    norm_sum_sqrtAbelIncrement_le
      (allScaleLiCriticalPrefix L) X B hX1 hB hprefix
  have hsum :
      (∑ n ∈ Finset.Icc 1 X,
          sqrtAbelIncrement (allScaleLiCriticalPrefix L) n) =
        ∑ n ∈ Finset.Icc 1 X, allScaleLiDiagonalIncrement L n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact sqrtAbelIncrement_allScaleLiCriticalPrefix L (Finset.mem_Icc.mp hn).1
  rw [hsum, sum_allScaleLiDiagonalIncrement_eq L X,
    allScaleLiState_zero_zero hL] at habel
  have hXleR2 : (X : ℝ) ≤ (R : ℝ) ^ 2 := by
    dsimp [X, squareRootEndpoint]
    exact_mod_cast (Nat.sub_le (R ^ 2) 1)
  have hsqrtXleR : Real.sqrt (X : ℝ) ≤ (R : ℝ) := by
    calc
      Real.sqrt (X : ℝ) ≤ Real.sqrt ((R : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt hXleR2
      _ = (R : ℝ) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
        positivity
  have hnorm :
      ‖L X X‖ ≤ (2 * B + 1) * (R : ℝ) := by
    calc
      ‖L X X‖ = ‖(L X X - 1) + 1‖ := by ring_nf
      _ ≤ ‖L X X - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * Real.sqrt (X : ℝ) * B + 1 := by
        simpa using add_le_add habel (le_refl (1 : ℝ))
      _ ≤ 2 * (R : ℝ) * B + 1 := by
        nlinarith [mul_nonneg hB (sub_nonneg.mpr hsqrtXleR)]
      _ ≤ (2 * B + 1) * (R : ℝ) := by
        have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
        nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * B + 1) (sub_nonneg.mpr hR1)]
  have hsq := pow_le_pow_left₀ (norm_nonneg (L X X)) hnorm 2
  dsimp [X] at hsq ⊢
  calc
    ‖L (squareRootEndpoint R) (squareRootEndpoint R)‖ ^ 2
        ≤ ((2 * B + 1) * (R : ℝ)) ^ 2 := hsq
    _ = (2 * B + 1) ^ 2 * (R : ℝ) ^ 2 := by ring

/-- A uniformly bounded continuous/reference diagonal. -/
def UniformReferenceDiagonalBounded (M : ℕ → ℂ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℕ, ‖M x‖ ≤ B

/-- Linear discrete-to-reference transfer at square-root endpoints. -/
def AllScaleLiLinearReferenceTransfer (M : ℕ → ℂ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ (L : ℕ → ℕ → ℂ) (R : ℕ),
      IsAllScaleLiState L →
      PrimeFrequencySaturated L →
      2 ≤ R →
      ‖L (squareRootEndpoint R) (squareRootEndpoint R) -
          M (squareRootEndpoint R)‖ ≤ A * (R : ℝ)

/-- **Pure-model closure spine.**
A bounded continuous/reference model plus an O(R) transfer closes the intrinsic
all-scale Li theorem.  No actual-prime object occurs in the statement or proof. -/
theorem allScaleLiSquareRootBounded_of_uniformReference_linearTransfer
    (M : ℕ → ℂ)
    (hM : UniformReferenceDiagonalBounded M)
    (hT : AllScaleLiLinearReferenceTransfer M) :
    AllScaleLiSquareRootBoundedStatement := by
  rcases hM with ⟨B, hB, hMb⟩
  rcases hT with ⟨A, hA, hTb⟩
  refine ⟨(A + B) ^ 2, sq_nonneg (A + B), ?_⟩
  intro L R hL hsat hR
  have hR1n : 1 ≤ R := by omega
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1n
  have hBR : B ≤ B * (R : ℝ) := by
    nlinarith
  have hMscale :
      ‖M (squareRootEndpoint R)‖ ≤ B * (R : ℝ) :=
    (hMb (squareRootEndpoint R)).trans hBR
  have hdiff := hTb L R hL hsat hR
  have hnorm :
      ‖L (squareRootEndpoint R) (squareRootEndpoint R)‖ ≤
        (A + B) * (R : ℝ) := by
    calc
      ‖L (squareRootEndpoint R) (squareRootEndpoint R)‖ =
          ‖(L (squareRootEndpoint R) (squareRootEndpoint R) -
              M (squareRootEndpoint R)) + M (squareRootEndpoint R)‖ := by
                congr 1
                ring
      _ ≤ ‖L (squareRootEndpoint R) (squareRootEndpoint R) -
              M (squareRootEndpoint R)‖ +
            ‖M (squareRootEndpoint R)‖ := norm_add_le _ _
      _ ≤ A * (R : ℝ) + B * (R : ℝ) := add_le_add hdiff hMscale
      _ = (A + B) * (R : ℝ) := by ring
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hright : 0 ≤ (A + B) * (R : ℝ) := mul_nonneg hAB hR0
  have hsquare :=
    mul_self_le_mul_self (norm_nonneg
      (L (squareRootEndpoint R) (squareRootEndpoint R))) hnorm
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsquare


/-! ## Exact residual propagation for a reference model -/

/-- Residual of an arbitrary reference state against the same prime-frequency
recursion.  For the continuous/Dickman reference this is exactly where the
unit-bin discretization error is to be estimated. -/
def primeFrequencyReferenceResidual
    (w : ℕ → ℂ) (C : ℕ → ℕ → ℂ) (x y : ℕ) : ℂ :=
  C x y - primeFrequencyStep w C x y

/-- An exact state has zero reference residual. -/
theorem primeFrequencyReferenceResidual_eq_zero
    {w : ℕ → ℂ} {C : ℕ → ℕ → ℂ}
    (hC : IsPrimeFrequencyState w C) (x y : ℕ) :
    primeFrequencyReferenceResidual w C x y = 0 := by
  unfold primeFrequencyReferenceResidual
  rw [hC x y]
  ring

/-- **Exact Duhamel/Volterra propagation identity.**
If `L` is the exact discrete frequency state and `C` is any reference
state, their difference is the propagated child difference plus only the local
reference residual.  No actual-prime or prime-discrepancy object occurs. -/
theorem primeFrequencyState_sub_reference_eq_propagated_sub_residual
    {w : ℕ → ℂ} {L C : ℕ → ℕ → ℂ}
    (hL : IsPrimeFrequencyState w L) (x y : ℕ) :
    L x y - C x y =
      -(∑ q ∈ Finset.Ioc 1 (min x y),
          w q * (L (x / q) (q - 1) - C (x / q) (q - 1))) -
        primeFrequencyReferenceResidual w C x y := by
  have hsum :
      (∑ q ∈ Finset.Ioc 1 (min x y),
          w q * (L (x / q) (q - 1) - C (x / q) (q - 1))) =
        (∑ q ∈ Finset.Ioc 1 (min x y), w q * L (x / q) (q - 1)) -
          ∑ q ∈ Finset.Ioc 1 (min x y), w q * C (x / q) (q - 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hL x y, hsum]
  unfold primeFrequencyReferenceResidual primeFrequencyStep
  ring

/-- Specialization to the all-scale singleton-Li weights. -/
theorem allScaleLiState_sub_reference_eq_propagated_sub_residual
    {L C : ℕ → ℕ → ℂ}
    (hL : IsAllScaleLiState L) (x y : ℕ) :
    L x y - C x y =
      -(∑ q ∈ Finset.Ioc 1 (min x y),
          primeSievePNTDensity q *
            (L (x / q) (q - 1) - C (x / q) (q - 1))) -
        primeFrequencyReferenceResidual primeSievePNTDensity C x y :=
  primeFrequencyState_sub_reference_eq_propagated_sub_residual hL x y

end RHLean.Analysis
