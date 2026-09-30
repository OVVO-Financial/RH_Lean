import Mathlib
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Analysis.PrimeSieveFiniteDifferenceModulus
import «research.ALL_SCALE_LI_DISPLACEMENT_REDUCTION»
import «research.PRIME_DENSITY_PNT_LOG_BOUND»
import RHLean.Proof.FinitePartialMoments
import «research.EXACT_LI_DICKMAN_FORMAL»

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



/-! ## One-sided degree-one conservatism -/

/-- Moving a support point to the right can only reduce its lower partial
mass.  This is the pointwise order statement behind the continuous-vs-discrete
degree-one comparison. -/
theorem negativePart_antitone {a b : ℝ} (hab : a ≤ b) :
    negativePart b ≤ negativePart a := by
  unfold negativePart
  exact max_le_max (neg_le_neg hab) le_rfl

/-- **Degree-zero/CDF support dominance.**
For common nonnegative weights, moving every support point to the right can
only decrease the lower cumulative mass. -/
theorem degreeZeroLowerMass_anti_support
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x y : ι → ℝ) (t : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hxy : ∀ i ∈ s, x i ≤ y i) :
    degreeZeroLowerMass s w y t ≤ degreeZeroLowerMass s w x t := by
  unfold degreeZeroLowerMass
  apply Finset.sum_le_sum
  intro i hi
  by_cases hy : y i ≤ t
  · have hx : x i ≤ t := (hxy i hi).trans hy
    simp [hy, hx]
  · by_cases hx : x i ≤ t
    · simp [hy, hx, hw i hi]
    · simp [hy, hx]

/-- **Degree-one continuous-conservative support dominance.**
For common nonnegative weights, moving every support point to the right can
only decrease the lower degree-one partial mass.  Equivalently, a left-shifted
continuous allocation is conservative relative to its right-endpoint discrete
allocation in LPM_1. -/
theorem weightedDegreeOneLowerMass_anti_support
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x y : ι → ℝ) (t : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hxy : ∀ i ∈ s, x i ≤ y i) :
    weightedDegreeOneLowerMass s w y t ≤
      weightedDegreeOneLowerMass s w x t := by
  unfold weightedDegreeOneLowerMass
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hw i hi)
  apply negativePart_antitone
  exact sub_le_sub_right (hxy i hi) t


/-! ## Zero-target partial-moment error control -/

/-- Degree-one total partial-moment mass about target zero.
No mean-centering occurs: this is exactly upper plus lower mass at zero. -/
def zeroTargetDegreeOneErrorMass {ι : Type*}
    (s : Finset ι) (e : ι → ℝ) : ℝ :=
  upperPartialMass s e + lowerPartialMass s e

/-- Degree-two total partial-moment energy about target zero. -/
def zeroTargetDegreeTwoErrorEnergy {ι : Type*}
    (s : Finset ι) (e : ι → ℝ) : ℝ :=
  upperPartialMomentNat 2 s e + lowerPartialMomentNat 2 s e

/-- Degree one at target zero is exactly total absolute error mass. -/
theorem zeroTargetDegreeOneErrorMass_eq_finiteAbsoluteMass
    {ι : Type*} (s : Finset ι) (e : ι → ℝ) :
    zeroTargetDegreeOneErrorMass s e = finiteAbsoluteMass s e := by
  unfold zeroTargetDegreeOneErrorMass
  exact upperPartialMass_add_lowerPartialMass_eq_finiteAbsoluteMass s e

/-- Degree two at target zero is exactly the finite squared-error energy. -/
theorem zeroTargetDegreeTwoErrorEnergy_eq_sum_sq
    {ι : Type*} (s : Finset ι) (e : ι → ℝ) :
    zeroTargetDegreeTwoErrorEnergy s e =
      ∑ i ∈ s, e i ^ 2 := by
  unfold zeroTargetDegreeTwoErrorEnergy
  rw [upperPartialMomentNat_add_lowerPartialMomentNat 2 (by norm_num)]
  unfold absolutePowerMomentNat
  apply Finset.sum_congr rfl
  intro i hi
  simp only [sq_abs]

/-- **Zero-target degree hierarchy.**
The square of the degree-one absolute error mass is bounded by cardinality
times the degree-two error energy.  This is the finite Cauchy--Schwarz step
needed at square endpoints. -/
theorem zeroTargetDegreeOneErrorMass_sq_le_card_mul_degreeTwoErrorEnergy
    {ι : Type*} (s : Finset ι) (e : ι → ℝ) :
    zeroTargetDegreeOneErrorMass s e ^ 2 ≤
      (s.card : ℝ) * zeroTargetDegreeTwoErrorEnergy s e := by
  rw [zeroTargetDegreeOneErrorMass_eq_finiteAbsoluteMass,
    zeroTargetDegreeTwoErrorEnergy_eq_sum_sq]
  unfold finiteAbsoluteMass
  simpa only [sq_abs] using
    (sq_sum_le_card_mul_sum_sq
      (s := s) (f := fun i => |e i|))

/-- Complex/radial degree-two error energy about zero.
This is the normed-space analogue used by the Li state, whose bookkeeping is
complex-valued even though the exact Li weights are real. -/
def zeroTargetComplexDegreeTwoEnergy {ι : Type*}
    (s : Finset ι) (e : ι → ℂ) : ℝ :=
  ∑ i ∈ s, ‖e i‖ ^ 2

theorem zeroTargetComplexDegreeTwoEnergy_nonneg
    {ι : Type*} (s : Finset ι) (e : ι → ℂ) :
    0 ≤ zeroTargetComplexDegreeTwoEnergy s e := by
  unfold zeroTargetComplexDegreeTwoEnergy
  exact Finset.sum_nonneg fun i hi => sq_nonneg ‖e i‖

/-- **Zero-target complex energy domination.**
A finite sum of local complex errors has squared norm at most cardinality
times the degree-two radial error energy. -/
theorem norm_finset_sum_sq_le_card_mul_zeroTargetComplexDegreeTwoEnergy
    {ι : Type*} (s : Finset ι) (e : ι → ℂ) :
    ‖∑ i ∈ s, e i‖ ^ 2 ≤
      (s.card : ℝ) * zeroTargetComplexDegreeTwoEnergy s e := by
  have hnorm :
      ‖∑ i ∈ s, e i‖ ≤ ∑ i ∈ s, ‖e i‖ :=
    norm_sum_le _ _
  calc
    ‖∑ i ∈ s, e i‖ ^ 2
        ≤ (∑ i ∈ s, ‖e i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖e i‖ ^ 2 := by
          exact sq_sum_le_card_mul_sum_sq
    _ = (s.card : ℝ) * zeroTargetComplexDegreeTwoEnergy s e := by
          rfl


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



/-! ## Exact weighted floor dilation -/

/-- Weighted finite-difference prefix. -/
def weightedForwardDifferencePrefix
    (r : ℕ → ℂ) (F : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, r n * (F n - F (n - 1))

/-- One-step extension of a weighted finite-difference prefix. -/
theorem weightedForwardDifferencePrefix_succ
    (r : ℕ → ℂ) (F : ℕ → ℂ) (N : ℕ) :
    weightedForwardDifferencePrefix r F (N + 1) =
      weightedForwardDifferencePrefix r F N +
        r (N + 1) * (F (N + 1) - F N) := by
  unfold weightedForwardDifferencePrefix
  rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1)]
  simp only [Nat.add_sub_cancel]

/-- Exact floor-dilation law for multiplicative weights.
Only multiples of q survive the finite difference of F(n/q), and a
multiplicative weight factors at those sites. -/
theorem weightedForwardDifferencePrefix_floor_div
    (r : ℕ → ℂ) (F : ℕ → ℂ) (q : ℕ)
    (hrmul : ∀ a b : ℕ, r (a * b) = r a * r b) (N : ℕ) :
    weightedForwardDifferencePrefix r (fun n => F (n / q)) N =
      r q * weightedForwardDifferencePrefix r F (N / q) := by
  induction N with
  | zero =>
      simp [weightedForwardDifferencePrefix]
  | succ N ih =>
      rw [weightedForwardDifferencePrefix_succ, ih]
      by_cases hdvd : q ∣ N + 1
      · have hdiv : (N + 1) / q = N / q + 1 := by
          rw [Nat.succ_div, if_pos hdvd]
        have hmul : N + 1 = q * ((N + 1) / q) := by
          symm
          exact Nat.mul_div_cancel' hdvd
        rw [hdiv, weightedForwardDifferencePrefix_succ]
        rw [hmul, hrmul]
        rw [hdiv]
        ring
      · have hdiv : (N + 1) / q = N / q := by
          rw [Nat.succ_div, if_neg hdvd, add_zero]
        rw [hdiv]
        simp


/-! ## Critical square-root weight -/

/-- Critical multiplicative weight n^(-1/2). -/
def criticalSqrtWeight (n : ℕ) : ℂ :=
  (Real.sqrt (n : ℝ) : ℂ)⁻¹

/-- The critical square-root weight is exactly multiplicative. -/
theorem criticalSqrtWeight_mul (a b : ℕ) :
    criticalSqrtWeight (a * b) =
      criticalSqrtWeight a * criticalSqrtWeight b := by
  simp [criticalSqrtWeight, Nat.cast_mul,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (a : ℝ))]
  ring

/-- The generic floor-dilation law at the critical square-root weight. -/
theorem criticalSqrtWeightedPrefix_floor_div
    (F : ℕ → ℂ) (q N : ℕ) :
    weightedForwardDifferencePrefix criticalSqrtWeight
        (fun n => F (n / q)) N =
      criticalSqrtWeight q *
        weightedForwardDifferencePrefix criticalSqrtWeight F (N / q) := by
  exact weightedForwardDifferencePrefix_floor_div
    criticalSqrtWeight F q criticalSqrtWeight_mul N


/-! ## Critical transform of the largest-site recursion -/

/-- Linearity under subtraction for the weighted finite-difference prefix. -/
theorem weightedForwardDifferencePrefix_sub
    (r F G : ℕ → ℂ) (N : ℕ) :
    weightedForwardDifferencePrefix r (fun n => F n - G n) N =
      weightedForwardDifferencePrefix r F N -
        weightedForwardDifferencePrefix r G N := by
  unfold weightedForwardDifferencePrefix
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Constant functions have zero weighted finite-difference prefix. -/
theorem weightedForwardDifferencePrefix_const
    (r : ℕ → ℂ) (c : ℂ) (N : ℕ) :
    weightedForwardDifferencePrefix r (fun _ => c) N = 0 := by
  unfold weightedForwardDifferencePrefix
  apply Finset.sum_eq_zero
  intro n hn
  ring

/-- A constant scalar factors through the weighted prefix. -/
theorem weightedForwardDifferencePrefix_const_mul
    (r : ℕ → ℂ) (c : ℂ) (F : ℕ → ℂ) (N : ℕ) :
    weightedForwardDifferencePrefix r (fun n => c * F n) N =
      c * weightedForwardDifferencePrefix r F N := by
  unfold weightedForwardDifferencePrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Finite sums commute with the weighted finite-difference prefix. -/
theorem weightedForwardDifferencePrefix_finset_sum
    {ι : Type*} [DecidableEq ι]
    (r : ℕ → ℂ) (s : Finset ι) (F : ι → ℕ → ℂ) (N : ℕ) :
    weightedForwardDifferencePrefix r
        (fun n => ∑ i ∈ s, F i n) N =
      ∑ i ∈ s, weightedForwardDifferencePrefix r (F i) N := by
  unfold weightedForwardDifferencePrefix
  calc
    ∑ n ∈ Finset.Icc 1 N,
        r n * ((∑ i ∈ s, F i n) - ∑ i ∈ s, F i (n - 1)) =
        ∑ n ∈ Finset.Icc 1 N,
          ∑ i ∈ s, r n * (F i n - F i (n - 1)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    _ = ∑ i ∈ s,
          ∑ n ∈ Finset.Icc 1 N,
            r n * (F i n - F i (n - 1)) := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ s, weightedForwardDifferencePrefix r (F i) N := by
      rfl

/-- A floor-child is active only once its owner site has entered. -/
def activatedFloorChild (F : ℕ → ℂ) (q n : ℕ) : ℂ :=
  if q ≤ n then F (n / q) else 0

theorem activatedFloorChild_eq_floor_sub_ltStep
    (F : ℕ → ℂ) (q n : ℕ) :
    activatedFloorChild F q n =
      F (n / q) - (if n < q then F 0 else 0) := by
  unfold activatedFloorChild
  by_cases h : q ≤ n
  · have hn : ¬ n < q := not_lt.mpr h
    simp [h, hn]
  · have hn : n < q := lt_of_not_ge h
    have hdiv : n / q = 0 := Nat.div_eq_of_lt hn
    simp [h, hn, hdiv]


/-- Activated floor dilations compose multiplicatively. -/
theorem activatedFloorChild_comp
    (F : ℕ → ℂ) {q r x : ℕ}
    (hq : 1 ≤ q) (hr : 1 ≤ r) :
    activatedFloorChild
        (fun m => activatedFloorChild F r m) q x =
      activatedFloorChild F (q * r) x := by
  have hqpos : 0 < q := by omega
  by_cases hqr : q * r ≤ x
  · have hqx : q ≤ x := by
      calc
        q = q * 1 := by simp
        _ ≤ q * r := Nat.mul_le_mul_left q hr
        _ ≤ x := hqr
    have hrdiv : r ≤ x / q := by
      apply (Nat.le_div_iff_mul_le hqpos).2
      simpa [Nat.mul_comm] using hqr
    simp [activatedFloorChild, hqx, hrdiv, hqr,
      Nat.div_div_eq_div_mul]
  · by_cases hqx : q ≤ x
    · have hrnot : ¬ r ≤ x / q := by
        intro hrdiv
        have hmul := (Nat.le_div_iff_mul_le hqpos).1 hrdiv
        apply hqr
        simpa [Nat.mul_comm] using hmul
      simp [activatedFloorChild, hqx, hrnot, hqr]
    · simp [activatedFloorChild, hqx, hqr]

/-- Activated floor dilations commute. -/
theorem activatedFloorChild_comm
    (F : ℕ → ℂ) {q r x : ℕ}
    (hq : 1 ≤ q) (hr : 1 ≤ r) :
    activatedFloorChild
        (fun m => activatedFloorChild F r m) q x =
      activatedFloorChild
        (fun m => activatedFloorChild F q m) r x := by
  rw [activatedFloorChild_comp F hq hr,
    activatedFloorChild_comp F hr hq, Nat.mul_comm]




/-- Activated floor dilation is linear under subtraction. -/
theorem activatedFloorChild_sub
    (F G : ℕ → ℂ) (q x : ℕ) :
    activatedFloorChild (fun m => F m - G m) q x =
      activatedFloorChild F q x - activatedFloorChild G q x := by
  unfold activatedFloorChild
  by_cases h : q ≤ x <;> simp [h]

/-- Activated floor dilation commutes with a constant scalar. -/
theorem activatedFloorChild_const_mul
    (c : ℂ) (F : ℕ → ℂ) (q x : ℕ) :
    activatedFloorChild (fun m => c * F m) q x =
      c * activatedFloorChild F q x := by
  unfold activatedFloorChild
  by_cases h : q ≤ x <;> simp [h]

/-- One fresh-site hard-core update. -/
def frequencyHardCoreUpdate
    (a : ℂ) (q : ℕ) (F : ℕ → ℂ) (x : ℕ) : ℂ :=
  F x - a * activatedFloorChild F q x

/-- **Exact sequential cutoff law.**
Once the cutoff is at least one, adjoining the next site is literally the
hard-core update `I - w(q) A_q`, where `A_q` is the activated floor
dilation. -/
theorem primeFrequencyState_cutoff_succ
    {w : ℕ → ℂ} {S : ℕ → ℕ → ℂ}
    (hS : IsPrimeFrequencyState w S)
    (x y : ℕ) (hy : 1 ≤ y) :
    S x (y + 1) =
      frequencyHardCoreUpdate (w (y + 1)) (y + 1)
        (fun m => S m y) x := by
  unfold frequencyHardCoreUpdate
  change S x (y + 1) =
    S x y - w (y + 1) * activatedFloorChild (fun m => S m y) (y + 1) x
  by_cases henter : y + 1 ≤ x
  · have hyx : y ≤ x := by omega
    rw [hS x (y + 1), hS x y]
    unfold primeFrequencyStep
    rw [min_eq_right henter, min_eq_right hyx,
      Finset.sum_Ioc_succ_top hy]
    simp [activatedFloorChild, henter]
    ring
  · have hxle : x ≤ y := by omega
    rw [hS x (y + 1), hS x y]
    unfold primeFrequencyStep
    rw [min_eq_left (hxle.trans (Nat.le_succ y)), min_eq_left hxle]
    simp [activatedFloorChild, henter]


/-- Fresh-site hard-core updates commute because the activated floor
dilations commute. -/
theorem frequencyHardCoreUpdate_comm
    (a b : ℂ) (F : ℕ → ℂ) {q r x : ℕ}
    (hq : 1 ≤ q) (hr : 1 ≤ r) :
    frequencyHardCoreUpdate a q
        (fun m => frequencyHardCoreUpdate b r F m) x =
      frequencyHardCoreUpdate b r
        (fun m => frequencyHardCoreUpdate a q F m) x := by
  unfold frequencyHardCoreUpdate
  rw [activatedFloorChild_sub, activatedFloorChild_const_mul,
    activatedFloorChild_sub, activatedFloorChild_const_mul]
  have hcomm := activatedFloorChild_comm F hq hr (x := x)
  rw [hcomm]
  ring


/-- Iterate the hard-core factors at sites 2,...,k+1. -/
def frequencyHardCoreIterate
    (w : ℕ → ℂ) : ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | 0, F => F
  | k + 1, F =>
      fun x =>
        frequencyHardCoreUpdate (w (k + 2)) (k + 2)
          (frequencyHardCoreIterate w k F) x

/-- **Exact finite hard-core product representation.**
Every frequency state is obtained by successively adjoining the sites
2,...,k+1 to the unit state. -/
theorem primeFrequencyState_eq_hardCoreIterate
    {w : ℕ → ℂ} {S : ℕ → ℕ → ℂ}
    (hS : IsPrimeFrequencyState w S)
    (k x : ℕ) :
    S x (k + 1) =
      frequencyHardCoreIterate w k (fun _ => 1) x := by
  induction k generalizing x with
  | zero =>
      rw [hS x 1]
      simp [primeFrequencyStep, frequencyHardCoreIterate]
  | succ k ih =>
      have hy : 1 ≤ k + 1 := by omega
      have hstep :=
        primeFrequencyState_cutoff_succ hS x (k + 1) hy
      have ihfun :
          (fun m => S m (k + 1)) =
            frequencyHardCoreIterate w k (fun _ => 1) := by
        funext m
        exact ih m
      rw [hstep, ihfun]
      rfl

/-- The finite difference of the pre-entry step is a single negative atom at
the owner site. -/
theorem weightedForwardDifferencePrefix_ltStep
    (r : ℕ → ℂ) (c : ℂ) {q N : ℕ}
    (hq : 1 ≤ q) (hqN : q ≤ N) :
    weightedForwardDifferencePrefix r
        (fun n => if n < q then c else 0) N =
      -(r q * c) := by
  unfold weightedForwardDifferencePrefix
  have hqmem : q ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hq, hqN⟩
  calc
    ∑ n ∈ Finset.Icc 1 N,
        r n * ((if n < q then c else 0) -
          (if n - 1 < q then c else 0)) =
        r q * ((if q < q then c else 0) -
          (if q - 1 < q then c else 0)) := by
      apply Finset.sum_eq_single_of_mem q
      · exact hqmem
      · intro n hn hne
        by_cases hnq : n < q
        · have hpred : n - 1 < q := (Nat.sub_le n 1).trans_lt hnq
          simp [hnq, hpred]
        · have hqn : q < n := by omega
          have hpred : ¬ n - 1 < q := by omega
          simp [hnq, hpred]
    _ = -(r q * c) := by
      have hpred : q - 1 < q := by omega
      simp [hpred]

/-- Activated floor dilation.  Compared with the ordinary floor-dilation law,
the first activation contributes the missing base value F(0). -/
theorem weightedForwardDifferencePrefix_activatedFloor
    (r F : ℕ → ℂ) {q N : ℕ}
    (hrmul : ∀ a b : ℕ, r (a * b) = r a * r b)
    (hq : 1 ≤ q) (hqN : q ≤ N) :
    weightedForwardDifferencePrefix r (activatedFloorChild F q) N =
      r q * (F 0 + weightedForwardDifferencePrefix r F (N / q)) := by
  have hfun :
      activatedFloorChild F q =
        fun n => F (n / q) - (if n < q then F 0 else 0) := by
    funext n
    exact activatedFloorChild_eq_floor_sub_ltStep F q n
  rw [hfun, weightedForwardDifferencePrefix_sub,
    weightedForwardDifferencePrefix_floor_div r F q hrmul N,
    weightedForwardDifferencePrefix_ltStep r (F 0) hq hqN]
  ring

/-- Rewrite a state recurrence against one fixed ambient owner set.  Owners
which have not yet entered are represented by an activated floor child. -/
theorem primeFrequencyState_eq_fixedAmbientActivated
    {w : ℕ → ℂ} {S : ℕ → ℕ → ℂ}
    (hS : IsPrimeFrequencyState w S)
    {n X y : ℕ} (hnX : n ≤ X) :
    S n y =
      1 - ∑ q ∈ Finset.Ioc 1 (min X y),
        w q * activatedFloorChild (fun m => S m (q - 1)) q n := by
  rw [hS n y]
  unfold primeFrequencyStep
  have hsub :
      Finset.Ioc 1 (min n y) ⊆ Finset.Ioc 1 (min X y) := by
    intro q hq
    rcases Finset.mem_Ioc.mp hq with ⟨hq1, hqtop⟩
    apply Finset.mem_Ioc.mpr
    constructor
    · exact hq1
    · have hqn : q ≤ n := hqtop.trans (min_le_left n y)
      have hqy : q ≤ y := hqtop.trans (min_le_right n y)
      exact le_min (hqn.trans hnX) hqy
  congr 1
  calc
    (∑ q ∈ Finset.Ioc 1 (min n y),
        w q * S (n / q) (q - 1) : ℂ) =
        ∑ q ∈ Finset.Ioc 1 (min n y),
          w q * activatedFloorChild (fun m => S m (q - 1)) q n := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqn : q ≤ n := by
        exact (Finset.mem_Ioc.mp hq).2.trans (min_le_left n y)
      simp [activatedFloorChild, hqn]
    _ = ∑ q ∈ Finset.Ioc 1 (min X y),
          w q * activatedFloorChild (fun m => S m (q - 1)) q n := by
      apply Finset.sum_subset hsub
      intro q hqBig hqNot
      rcases Finset.mem_Ioc.mp hqBig with ⟨hq1, hqtop⟩
      have hqy : q ≤ y := hqtop.trans (min_le_right X y)
      have hqn : ¬ q ≤ n := by
        intro hqn
        apply hqNot
        exact Finset.mem_Ioc.mpr
          ⟨hq1, le_min hqn hqy⟩
      simp [activatedFloorChild, hqn]

/-- Exact weighted recursion for the critical transform of any frequency
state.  The owner weight is multiplied by the multiplicative test weight r(q). -/
theorem weightedForwardDifferencePrefix_primeFrequencyState
    {w r : ℕ → ℂ} {S : ℕ → ℕ → ℂ}
    (hS : IsPrimeFrequencyState w S)
    (hrmul : ∀ a b : ℕ, r (a * b) = r a * r b)
    (x y : ℕ) :
    weightedForwardDifferencePrefix r (fun n => S n y) x =
      -(∑ q ∈ Finset.Ioc 1 (min x y),
          w q * r q *
            (S 0 (q - 1) +
              weightedForwardDifferencePrefix r
                (fun m => S m (q - 1)) (x / q))) := by
  let owners := Finset.Ioc 1 (min x y)
  let A : ℕ → ℂ := fun n =>
    ∑ q ∈ owners,
      w q * activatedFloorChild (fun m => S m (q - 1)) q n
  have hpoint : ∀ n, n ≤ x → S n y = 1 - A n := by
    intro n hnx
    simpa [owners, A] using
      primeFrequencyState_eq_fixedAmbientActivated hS hnx
  have hpref :
      weightedForwardDifferencePrefix r (fun n => S n y) x =
        weightedForwardDifferencePrefix r (fun n => 1 - A n) x := by
    unfold weightedForwardDifferencePrefix
    apply Finset.sum_congr rfl
    intro n hn
    have hnle : n ≤ x := (Finset.mem_Icc.mp hn).2
    have hpredle : n - 1 ≤ x := (Nat.sub_le n 1).trans hnle
    change r n * (S n y - S (n - 1) y) =
      r n * ((1 - A n) - (1 - A (n - 1)))
    rw [hpoint n hnle, hpoint (n - 1) hpredle]
  rw [hpref, weightedForwardDifferencePrefix_sub,
    weightedForwardDifferencePrefix_const]
  have hsum :
      weightedForwardDifferencePrefix r A x =
        ∑ q ∈ owners,
          w q *
            weightedForwardDifferencePrefix r
              (activatedFloorChild (fun m => S m (q - 1)) q) x := by
    unfold A
    rw [weightedForwardDifferencePrefix_finset_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [weightedForwardDifferencePrefix_const_mul]
  rw [hsum, zero_sub]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro q hq
  have hqdata := Finset.mem_Ioc.mp hq
  have hqone : 1 ≤ q := by omega
  have hqx : q ≤ x := hqdata.2.trans (min_le_left x y)
  rw [weightedForwardDifferencePrefix_activatedFloor
    r (fun m => S m (q - 1)) hrmul hqone hqx]
  ring

/-- Critical Li owner weight after the exact n^(-1/2) transform. -/
def criticalLiFrequencyWeight (q : ℕ) : ℂ :=
  primeSievePNTDensity q * criticalSqrtWeight q


/-- Exact critical norm: the square-root test contributes precisely one
reciprocal factor. -/
theorem norm_criticalSqrtWeight_sq (q : ℕ) :
    ‖criticalSqrtWeight q‖ ^ 2 = 1 / (q : ℝ) := by
  by_cases hq : q = 0
  · subst q
    simp [criticalSqrtWeight]
  · have hqpos : (0 : ℝ) < q := by
      exact_mod_cast Nat.pos_of_ne_zero hq
    have hsqrtpos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
    rw [criticalSqrtWeight, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrtpos]
    have hsqrt_sq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) :=
      Real.sq_sqrt hqpos.le
    rw [inv_pow, hsqrt_sq]
    simp [one_div]

/-- The square norm of one transformed Li owner is exactly the collision
summand already proved summable above. -/
theorem norm_criticalLiFrequencyWeight_sq (q : ℕ) :
    ‖criticalLiFrequencyWeight q‖ ^ 2 =
      ‖primeSievePNTDensity q‖ ^ 2 / (q : ℝ) := by
  unfold criticalLiFrequencyWeight
  rw [norm_mul, mul_pow, norm_criticalSqrtWeight_sq]
  ring

/-- **Critical transformed Li owners are square-summable.**
This is the precise second-order budget for replacing the hard-core
fresh-site product by a continuous/Poissonized reference. -/
theorem criticalLiFrequencyWeight_sq_summable :
    Summable (fun q : ℕ => ‖criticalLiFrequencyWeight q‖ ^ 2) := by
  apply exactLiCriticalCollision_summable.congr
  intro q
  exact (norm_criticalLiFrequencyWeight_sq q).symm


/-! ## Uniform multiplicative budget for hard-core/Poisson correction -/

/-- Total second-order mass of the critical transformed Li owner weights. -/
def criticalLiCollisionBudget : ℝ :=
  ∑' q : ℕ, ‖criticalLiFrequencyWeight q‖ ^ 2

theorem criticalLiCollisionBudget_nonneg :
    0 ≤ criticalLiCollisionBudget := by
  unfold criticalLiCollisionBudget
  exact tsum_nonneg (fun q => sq_nonneg ‖criticalLiFrequencyWeight q‖)

/-- Every finite collection of critical collision masses is bounded by the
single universal collision budget. -/
theorem criticalLiFrequencyWeight_sq_finset_sum_le
    (s : Finset ℕ) :
    (∑ q ∈ s, ‖criticalLiFrequencyWeight q‖ ^ 2) ≤
      criticalLiCollisionBudget := by
  unfold criticalLiCollisionBudget
  exact criticalLiFrequencyWeight_sq_summable.sum_le_tsum s
    (fun q hq => sq_nonneg ‖criticalLiFrequencyWeight q‖)

/-! ## Exact local hard-core / Poisson cancellation -/

/-- Scalar local correction factor comparing one hard-core factor `1-z`
against its Poissonized exponential factor `exp(-z)`.  Multiplying the latter
by this correction gives the former exactly. -/
def hardCorePoissonScalarCorrection (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp z

/-- The local correction is exactly the identity plus a second-order
remainder: the first-order term cancels. -/
theorem hardCorePoissonScalarCorrection_sub_one_eq (z : ℂ) :
    hardCorePoissonScalarCorrection z - 1 =
      (Complex.exp z - 1 - z) - z * (Complex.exp z - 1) := by
  unfold hardCorePoissonScalarCorrection
  ring

/-- **Quadratic local correction bound.**
Inside the unit ball, the hard-core/Poisson discrepancy is at most
`3 * ‖z‖^2`; in particular there is no first-order loss. -/
theorem norm_hardCorePoissonScalarCorrection_sub_one_le
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖hardCorePoissonScalarCorrection z - 1‖ ≤
      3 * ‖z‖ ^ 2 := by
  rw [hardCorePoissonScalarCorrection_sub_one_eq]
  calc
    ‖(Complex.exp z - 1 - z) - z * (Complex.exp z - 1)‖
        ≤ ‖Complex.exp z - 1 - z‖ +
            ‖z * (Complex.exp z - 1)‖ := norm_sub_le _ _
    _ = ‖Complex.exp z - 1 - z‖ +
          ‖z‖ * ‖Complex.exp z - 1‖ := by rw [norm_mul]
    _ ≤ ‖z‖ ^ 2 + ‖z‖ * (2 * ‖z‖) := by
          exact add_le_add
            (Complex.norm_exp_sub_one_sub_id_le hz)
            (mul_le_mul_of_nonneg_left
              (Complex.norm_exp_sub_one_le hz) (norm_nonneg z))
    _ = 3 * ‖z‖ ^ 2 := by ring

/-- Coefficient of `T^m` in the exact local correction
`(1 - z*T) * exp(z*T)`.  The formula makes the vanishing linear term
literal: coefficient zero is one and coefficient one is zero. -/
def hardCorePoissonCorrectionCoeff (z : ℂ) (m : ℕ) : ℂ :=
  ((1 : ℂ) - (m : ℂ)) * z ^ m / (Nat.factorial m : ℂ)

@[simp] theorem hardCorePoissonCorrectionCoeff_zero (z : ℂ) :
    hardCorePoissonCorrectionCoeff z 0 = 1 := by
  simp [hardCorePoissonCorrectionCoeff]

@[simp] theorem hardCorePoissonCorrectionCoeff_one (z : ℂ) :
    hardCorePoissonCorrectionCoeff z 1 = 0 := by
  simp [hardCorePoissonCorrectionCoeff]

/-- Exact norm of the genuinely corrective coefficient, indexed from degree
two. -/
theorem norm_hardCorePoissonCorrectionCoeff_add_two
    (z : ℂ) (m : ℕ) :
    ‖hardCorePoissonCorrectionCoeff z (m + 2)‖ =
      ((m + 1 : ℕ) : ℝ) * ‖z‖ ^ (m + 2) /
        (Nat.factorial (m + 2) : ℝ) := by
  have hnum :
      ‖(1 : ℂ) - ((m + 2 : ℕ) : ℂ)‖ = (((m + 1 : ℕ) : ℝ)) := by
    rw [show (1 : ℂ) - ((m + 2 : ℕ) : ℂ) =
        -(((m + 1 : ℕ) : ℂ)) by
          push_cast
          ring,
      norm_neg, Complex.norm_natCast]
  unfold hardCorePoissonCorrectionCoeff
  rw [norm_div, norm_mul, hnum, norm_pow, Complex.norm_natCast]

/-- Real nonnegative tail coefficient controlling the critical variation of
one local correction factor. -/
def hardCorePoissonCorrectionTailTerm (a : ℝ) (m : ℕ) : ℝ :=
  ((m + 1 : ℕ) : ℝ) * a ^ (m + 2) /
    (Nat.factorial (m + 2) : ℝ)

/-- Inside the unit interval, every correction-tail coefficient is bounded by
`a^2 / m!`.  This is the coefficient-level form of the second-order
cancellation. -/
theorem hardCorePoissonCorrectionTailTerm_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (m : ℕ) :
    hardCorePoissonCorrectionTailTerm a m ≤
      a ^ 2 * (1 / (Nat.factorial m : ℝ)) := by
  have hpowa : a ^ (m + 2) ≤ a ^ 2 := by
    calc
      a ^ (m + 2) = a ^ m * a ^ 2 := by rw [pow_add]
      _ ≤ 1 * a ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_one₀ ha0 ha1) (sq_nonneg a)
      _ = a ^ 2 := by ring
  have hfacNat :
      Nat.factorial (m + 2) =
        (m + 2) * (m + 1) * Nat.factorial m := by
    rw [show m + 2 = (m + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hfac :
      (Nat.factorial (m + 2) : ℝ) =
        (((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) *
          (Nat.factorial m : ℝ) := by
    exact_mod_cast hfacNat
  have hfm : (0 : ℝ) < (Nat.factorial m : ℝ) := by positivity
  have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hm2 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hratio :
      ((m + 1 : ℕ) : ℝ) / (Nat.factorial (m + 2) : ℝ) ≤
        1 / (Nat.factorial m : ℝ) := by
    rw [hfac]
    have heq :
        ((m + 1 : ℕ) : ℝ) /
            ((((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) *
              (Nat.factorial m : ℝ)) =
          1 / (((m + 2 : ℕ) : ℝ) * (Nat.factorial m : ℝ)) := by
      field_simp
    rw [heq]
    simp only [one_div]
    apply (inv_le_inv₀ (mul_pos hm2 hfm) hfm).2
    calc
      (Nat.factorial m : ℝ) =
          1 * (Nat.factorial m : ℝ) := by ring
      _ ≤ ((m + 2 : ℕ) : ℝ) * (Nat.factorial m : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast (show 1 ≤ m + 2 by omega)
        · exact hfm.le
  unfold hardCorePoissonCorrectionTailTerm
  calc
    ((m + 1 : ℕ) : ℝ) * a ^ (m + 2) /
          (Nat.factorial (m + 2) : ℝ)
        = a ^ (m + 2) *
            (((m + 1 : ℕ) : ℝ) /
              (Nat.factorial (m + 2) : ℝ)) := by ring
    _ ≤ a ^ 2 *
          (((m + 1 : ℕ) : ℝ) /
            (Nat.factorial (m + 2) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hpowa (by positivity)
    _ ≤ a ^ 2 * (1 / (Nat.factorial m : ℝ)) :=
          mul_le_mul_of_nonneg_left hratio (sq_nonneg a)

/-- The real tail majorant is nonnegative. -/
theorem hardCorePoissonCorrectionTailTerm_nonneg
    {a : ℝ} (ha0 : 0 ≤ a) (m : ℕ) :
    0 ≤ hardCorePoissonCorrectionTailTerm a m := by
  unfold hardCorePoissonCorrectionTailTerm
  exact div_nonneg
    (mul_nonneg (by positivity) (pow_nonneg ha0 _))
    (by positivity)

/-- The full absolute correction tail is summable on the unit interval. -/
theorem hardCorePoissonCorrectionTailTerm_summable
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Summable (hardCorePoissonCorrectionTailTerm a) := by
  have hfact :
      Summable (fun m : ℕ => 1 / (Nat.factorial m : ℝ)) := by
    simpa using Real.summable_pow_div_factorial 1
  have hmajor :
      Summable
        (fun m : ℕ => a ^ 2 * (1 / (Nat.factorial m : ℝ))) :=
    hfact.mul_left (a ^ 2)
  exact Summable.of_nonneg_of_le
    (fun m => hardCorePoissonCorrectionTailTerm_nonneg ha0 m)
    (fun m => hardCorePoissonCorrectionTailTerm_le ha0 ha1 m)
    hmajor

/-- The factorial majorant sums to exp(1). -/
private theorem tsum_one_div_factorial_eq_exp_one :
    (∑' m : ℕ, 1 / (Nat.factorial m : ℝ)) = Real.exp 1 := by
  have h :
      (∑' m : ℕ, (1 : ℝ) ^ m / (Nat.factorial m : ℝ)) =
        Real.exp 1 := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simpa using h

/-- **Coefficient-level quadratic correction bound.**
For 0 <= a <= 1, the complete absolute tail of
`(1-aT) exp(aT)` beyond degrees zero and one is at most `3 a^2`.
This is stronger than bounding the scalar value: it controls exactly the
degree-one/total-variation mass of the correction kernel about target zero. -/
theorem tsum_hardCorePoissonCorrectionTailTerm_le_three_sq
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑' m : ℕ, hardCorePoissonCorrectionTailTerm a m) ≤
      3 * a ^ 2 := by
  have htail :=
    hardCorePoissonCorrectionTailTerm_summable ha0 ha1
  have hfact :
      Summable (fun m : ℕ => 1 / (Nat.factorial m : ℝ)) := by
    simpa using Real.summable_pow_div_factorial 1
  have hmajor :
      Summable
        (fun m : ℕ => a ^ 2 * (1 / (Nat.factorial m : ℝ))) :=
    hfact.mul_left (a ^ 2)
  calc
    (∑' m : ℕ, hardCorePoissonCorrectionTailTerm a m)
        ≤ ∑' m : ℕ, a ^ 2 * (1 / (Nat.factorial m : ℝ)) := by
          exact Summable.tsum_le_tsum
            (fun m => hardCorePoissonCorrectionTailTerm_le ha0 ha1 m)
            htail hmajor
    _ = a ^ 2 * (∑' m : ℕ, 1 / (Nat.factorial m : ℝ)) := by
          rw [tsum_mul_left]
    _ = a ^ 2 * Real.exp 1 := by
          rw [tsum_one_div_factorial_eq_exp_one]
    _ ≤ a ^ 2 * 3 := by
          exact mul_le_mul_of_nonneg_left
            (Real.exp_one_lt_d9.trans (by norm_num)).le (sq_nonneg a)
    _ = 3 * a ^ 2 := by ring

/-- Every finite truncation of the absolute correction tail obeys the same
quadratic bound. -/
theorem sum_range_hardCorePoissonCorrectionTailTerm_le_three_sq
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (K : ℕ) :
    (∑ m ∈ Finset.range K, hardCorePoissonCorrectionTailTerm a m) ≤
      3 * a ^ 2 := by
  have hs :=
    hardCorePoissonCorrectionTailTerm_summable ha0 ha1
  calc
    (∑ m ∈ Finset.range K, hardCorePoissonCorrectionTailTerm a m)
        ≤ ∑' m : ℕ, hardCorePoissonCorrectionTailTerm a m := by
          exact hs.sum_le_tsum (Finset.range K)
            (fun m hm => hardCorePoissonCorrectionTailTerm_nonneg ha0 m)
    _ ≤ 3 * a ^ 2 :=
      tsum_hardCorePoissonCorrectionTailTerm_le_three_sq ha0 ha1

/-- Critical square-root test weights have norm at most one away from zero. -/
theorem norm_criticalSqrtWeight_le_one
    {q : ℕ} (hq : 1 ≤ q) :
    ‖criticalSqrtWeight q‖ ≤ 1 := by
  have hsq := norm_criticalSqrtWeight_sq q
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hinv : 1 / (q : ℝ) ≤ 1 := by
    have h := inv_le_one_of_one_le₀ hqR
    simpa [one_div] using h
  have hnonneg := norm_nonneg (criticalSqrtWeight q)
  nlinarith

/-- From site four onward, every critical Li owner lies in the unit ball. -/
theorem norm_criticalLiFrequencyWeight_le_one
    {q : ℕ} (hq : 4 ≤ q) :
    ‖criticalLiFrequencyWeight q‖ ≤ 1 := by
  let y : ℕ := q - 1
  have hy3 : 3 ≤ y := by
    dsimp [y]
    omega
  have hy2 : 2 ≤ y := by omega
  have hyq : y < q := by
    dsimp [y]
    omega
  have hw :=
    exactLi_norm_pntDensity_le_inv_log hy2 hyq
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_lt_log (Real.exp_pos 1)
    exact Real.exp_one_lt_d9.trans (by norm_num)
  have hyR : (3 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy3
  have hlogy : (1 : ℝ) ≤ Real.log (y : ℝ) := by
    have hmono :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 3) hyR
    linarith
  have hinv : (Real.log (y : ℝ))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hlogy
  have hw1 : ‖primeSievePNTDensity q‖ ≤ 1 := hw.trans hinv
  unfold criticalLiFrequencyWeight
  rw [norm_mul]
  exact (mul_le_mul hw1
    (norm_criticalSqrtWeight_le_one (by omega : 1 ≤ q))
    (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

/-- The first Li site is exactly null after critical weighting. -/
theorem criticalLiFrequencyWeight_two_eq_zero :
    criticalLiFrequencyWeight 2 = 0 := by
  have hLi2 :
      logarithmicIntegralFromTwo (((2 : ℕ) : ℝ)) = 0 := by
    norm_num [logarithmicIntegralFromTwo]
  have hLi1 :
      logarithmicIntegralFromTwo (((2 - 1 : ℕ) : ℝ)) = 0 := by
    norm_num [logarithmicIntegralFromTwo_one]
  unfold criticalLiFrequencyWeight primeSievePNTDensity
  rw [hLi2, hLi1]
  simp

/-- The only remaining exceptional small site, q=3, is still inside the
critical unit ball. -/
theorem norm_criticalLiFrequencyWeight_three_le_one :
    ‖criticalLiFrequencyWeight 3‖ ≤ 1 := by
  have hw :=
    exactLi_norm_pntDensity_le_inv_log
      (y := 2) (q := 3) (by norm_num) (by norm_num)
  have hlogpos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have h23 : (2 / 3 : ℝ) ≤ Real.log (2 : ℝ) := by
    have hl := Real.log_two_gt_d9
    nlinarith
  have h23pos : (0 : ℝ) < 2 / 3 := by norm_num
  have hinv0 :
      (Real.log (2 : ℝ))⁻¹ ≤ ((2 / 3 : ℝ))⁻¹ :=
    (inv_le_inv₀ hlogpos h23pos).2 h23
  have hinv : (Real.log (2 : ℝ))⁻¹ ≤ (3 / 2 : ℝ) := by
    norm_num at hinv0 ⊢
    exact hinv0
  have hw15 : ‖primeSievePNTDensity 3‖ ≤ (3 / 2 : ℝ) :=
    hw.trans hinv
  have hsquare := norm_criticalSqrtWeight_sq 3
  have hs0 : 0 ≤ ‖criticalSqrtWeight 3‖ := norm_nonneg _
  have hs23 : ‖criticalSqrtWeight 3‖ ≤ (2 / 3 : ℝ) := by
    nlinarith
  unfold criticalLiFrequencyWeight
  rw [norm_mul]
  calc
    ‖primeSievePNTDensity 3‖ * ‖criticalSqrtWeight 3‖
        ≤ (3 / 2 : ℝ) * (2 / 3 : ℝ) :=
      mul_le_mul hw15 hs23 hs0 (by norm_num)
    _ = 1 := by norm_num

/-- Every Li site occurring in the hard-core product is inside the critical
unit ball, including the two initial sites. -/
theorem norm_criticalLiFrequencyWeight_le_one_of_two_le
    {q : ℕ} (hq : 2 ≤ q) :
    ‖criticalLiFrequencyWeight q‖ ≤ 1 := by
  by_cases h2 : q = 2
  · subst q
    rw [criticalLiFrequencyWeight_two_eq_zero]
    simp
  by_cases h3 : q = 3
  · subst q
    exact norm_criticalLiFrequencyWeight_three_le_one
  exact norm_criticalLiFrequencyWeight_le_one (by omega)

/-- Absolute coefficient variation of one local hard-core/Poisson
correction factor at the critical coordinate.  Degree zero contributes one,
degree one vanishes, and the remaining degrees are indexed by the quadratic
tail above. -/
def criticalLiLocalCorrectionVariation (q : ℕ) : ℝ :=
  1 + ∑' m : ℕ,
    hardCorePoissonCorrectionTailTerm
      ‖criticalLiFrequencyWeight q‖ m

/-- One local correction has critical coefficient variation bounded by
`1 + 3 |z_q|^2`. -/
theorem criticalLiLocalCorrectionVariation_le
    {q : ℕ} (hq : 4 ≤ q) :
    criticalLiLocalCorrectionVariation q ≤
      1 + 3 * ‖criticalLiFrequencyWeight q‖ ^ 2 := by
  unfold criticalLiLocalCorrectionVariation
  have hz0 : 0 ≤ ‖criticalLiFrequencyWeight q‖ := norm_nonneg _
  have hz1 : ‖criticalLiFrequencyWeight q‖ ≤ 1 :=
    norm_criticalLiFrequencyWeight_le_one hq
  exact add_le_add_left
    (tsum_hardCorePoissonCorrectionTailTerm_le_three_sq hz0 hz1) 1

/-- The quadratic coefficient-variation estimate in fact holds at every site
used by the Li Euler product. -/
theorem criticalLiLocalCorrectionVariation_le_of_two_le
    {q : ℕ} (hq : 2 ≤ q) :
    criticalLiLocalCorrectionVariation q ≤
      1 + 3 * ‖criticalLiFrequencyWeight q‖ ^ 2 := by
  unfold criticalLiLocalCorrectionVariation
  have hz0 : 0 ≤ ‖criticalLiFrequencyWeight q‖ := norm_nonneg _
  have hz1 : ‖criticalLiFrequencyWeight q‖ ≤ 1 :=
    norm_criticalLiFrequencyWeight_le_one_of_two_le hq
  exact add_le_add_left
    (tsum_hardCorePoissonCorrectionTailTerm_le_three_sq hz0 hz1) 1

/-- The local coefficient variation is nonnegative. -/
theorem criticalLiLocalCorrectionVariation_nonneg (q : ℕ) :
    0 ≤ criticalLiLocalCorrectionVariation q := by
  unfold criticalLiLocalCorrectionVariation
  have hz0 : 0 ≤ ‖criticalLiFrequencyWeight q‖ := norm_nonneg _
  have hterm :
      ∀ m : ℕ, 0 ≤
        hardCorePoissonCorrectionTailTerm
          ‖criticalLiFrequencyWeight q‖ m :=
    fun m => hardCorePoissonCorrectionTailTerm_nonneg hz0 m
  exact add_nonneg zero_le_one (tsum_nonneg hterm)

/-- Critical Li specialization of the scalar hard-core/Poisson correction. -/
def criticalLiScalarCorrection (q : ℕ) : ℂ :=
  hardCorePoissonScalarCorrection (criticalLiFrequencyWeight q)

/-- One critical Li correction factor differs from one only at quadratic
order, hence its norm is controlled by `1 + 3 |z_q|^2`. -/
theorem norm_criticalLiScalarCorrection_le
    {q : ℕ} (hq : 4 ≤ q) :
    ‖criticalLiScalarCorrection q‖ ≤
      1 + 3 * ‖criticalLiFrequencyWeight q‖ ^ 2 := by
  have hz := norm_criticalLiFrequencyWeight_le_one hq
  have hquad :=
    norm_hardCorePoissonScalarCorrection_sub_one_le hz
  unfold criticalLiScalarCorrection
  calc
    ‖hardCorePoissonScalarCorrection (criticalLiFrequencyWeight q)‖ =
        ‖(hardCorePoissonScalarCorrection (criticalLiFrequencyWeight q) - 1) +
            1‖ := by
          congr 1
          ring
    _ ≤ ‖hardCorePoissonScalarCorrection (criticalLiFrequencyWeight q) - 1‖ +
          ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 3 * ‖criticalLiFrequencyWeight q‖ ^ 2 + 1 := by
          simpa using add_le_add hquad (le_refl (‖(1 : ℂ)‖))
    _ = 1 + 3 * ‖criticalLiFrequencyWeight q‖ ^ 2 := by ring

/-- Finite Euler product bound for the quadratic local correction envelopes. -/
private theorem criticalLi_prod_one_add_three_sq_le_exp_sum
    (s : Finset ℕ) :
    (∏ q ∈ s, (1 + 3 * ‖criticalLiFrequencyWeight q‖ ^ 2)) ≤
      Real.exp (∑ q ∈ s, 3 * ‖criticalLiFrequencyWeight q‖ ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert q s hq ih =>
      rw [Finset.prod_insert hq, Finset.sum_insert hq, Real.exp_add]
      have hfac :
          1 + 3 * ‖criticalLiFrequencyWeight q‖ ^ 2 ≤
            Real.exp (3 * ‖criticalLiFrequencyWeight q‖ ^ 2) := by
        simpa [add_comm] using
          (Real.add_one_le_exp (3 * ‖criticalLiFrequencyWeight q‖ ^ 2))
      exact mul_le_mul hfac ih (by positivity) (by positivity)

/-- **Uniform product bound for the coefficient-level correction kernels.**
For any finite family of sites beyond the initial exceptional range, the
product of their complete local critical variations is bounded by the same
universal exponential collision constant. -/
theorem prod_criticalLiLocalCorrectionVariation_le_exp_collisionBudget
    (s : Finset ℕ) (hs : ∀ q ∈ s, 4 ≤ q) :
    (∏ q ∈ s, criticalLiLocalCorrectionVariation q) ≤
      Real.exp (3 * criticalLiCollisionBudget) := by
  have hprod :
      (∏ q ∈ s, criticalLiLocalCorrectionVariation q) ≤
        ∏ q ∈ s, (1 + 3 * ‖criticalLiFrequencyWeight q‖ ^ 2) := by
    classical
    revert hs
    induction s using Finset.induction_on with
    | empty =>
        intro hs
        simp
    | @insert q s hq ih =>
        intro hs
        rw [Finset.prod_insert hq, Finset.prod_insert hq]
        have hq4 : 4 ≤ q := hs q (Finset.mem_insert_self q s)
        have hs4 : ∀ r ∈ s, 4 ≤ r := by
          intro r hr
          exact hs r (Finset.mem_insert_of_mem hr)
        exact mul_le_mul
          (criticalLiLocalCorrectionVariation_le hq4)
          (ih hs4)
          (Finset.prod_nonneg fun r hr =>
            criticalLiLocalCorrectionVariation_nonneg r)
          (by positivity)
  calc
    (∏ q ∈ s, criticalLiLocalCorrectionVariation q)
        ≤ ∏ q ∈ s,
            (1 + 3 * ‖criticalLiFrequencyWeight q‖ ^ 2) := hprod
    _ ≤ Real.exp
          (∑ q ∈ s, 3 * ‖criticalLiFrequencyWeight q‖ ^ 2) :=
          criticalLi_prod_one_add_three_sq_le_exp_sum s
    _ ≤ Real.exp (3 * criticalLiCollisionBudget) := by
          apply Real.exp_le_exp.mpr
          calc
            (∑ q ∈ s, 3 * ‖criticalLiFrequencyWeight q‖ ^ 2)
                = 3 * (∑ q ∈ s, ‖criticalLiFrequencyWeight q‖ ^ 2) := by
                    rw [Finset.mul_sum]
            _ ≤ 3 * criticalLiCollisionBudget :=
              mul_le_mul_of_nonneg_left
                (criticalLiFrequencyWeight_sq_finset_sum_le s) (by norm_num)

/-- **Uniform product bound including the initial Li sites.**
The exact q=2 cancellation and the direct q=3 unit-ball estimate remove the
last exceptional-site qualification from the coefficient variation product. -/
theorem prod_criticalLiLocalCorrectionVariation_le_exp_collisionBudget_of_two_le
    (s : Finset ℕ) (hs : ∀ q ∈ s, 2 ≤ q) :
    (∏ q ∈ s, criticalLiLocalCorrectionVariation q) ≤
      Real.exp (3 * criticalLiCollisionBudget) := by
  have hprod :
      (∏ q ∈ s, criticalLiLocalCorrectionVariation q) ≤
        ∏ q ∈ s, (1 + 3 * ‖criticalLiFrequencyWeight q‖ ^ 2) := by
    classical
    revert hs
    induction s using Finset.induction_on with
    | empty =>
        intro hs
        simp
    | @insert q s hq ih =>
        intro hs
        rw [Finset.prod_insert hq, Finset.prod_insert hq]
        have hq2 : 2 ≤ q := hs q (Finset.mem_insert_self q s)
        have hs2 : ∀ r ∈ s, 2 ≤ r := by
          intro r hr
          exact hs r (Finset.mem_insert_of_mem hr)
        exact mul_le_mul
          (criticalLiLocalCorrectionVariation_le_of_two_le hq2)
          (ih hs2)
          (Finset.prod_nonneg fun r hr =>
            criticalLiLocalCorrectionVariation_nonneg r)
          (by positivity)
  calc
    (∏ q ∈ s, criticalLiLocalCorrectionVariation q)
        ≤ ∏ q ∈ s,
            (1 + 3 * ‖criticalLiFrequencyWeight q‖ ^ 2) := hprod
    _ ≤ Real.exp
          (∑ q ∈ s, 3 * ‖criticalLiFrequencyWeight q‖ ^ 2) :=
          criticalLi_prod_one_add_three_sq_le_exp_sum s
    _ ≤ Real.exp (3 * criticalLiCollisionBudget) := by
          apply Real.exp_le_exp.mpr
          calc
            (∑ q ∈ s, 3 * ‖criticalLiFrequencyWeight q‖ ^ 2)
                = 3 * (∑ q ∈ s, ‖criticalLiFrequencyWeight q‖ ^ 2) := by
                    rw [Finset.mul_sum]
            _ ≤ 3 * criticalLiCollisionBudget :=
              mul_le_mul_of_nonneg_left
                (criticalLiFrequencyWeight_sq_finset_sum_le s) (by norm_num)

/-- **Uniform finite hard-core/Poisson correction product.**
For any finite collection of Li sites beyond the finitely many initial ones,
the full scalar correction is bounded by a single universal constant depending
only on the certified square-summable collision budget. -/
theorem norm_prod_criticalLiScalarCorrection_le_exp_collisionBudget
    (s : Finset ℕ) (hs : ∀ q ∈ s, 4 ≤ q) :
    ‖∏ q ∈ s, criticalLiScalarCorrection q‖ ≤
      Real.exp (3 * criticalLiCollisionBudget) := by
  rw [norm_prod]
  calc
    (∏ q ∈ s, ‖criticalLiScalarCorrection q‖)
        ≤ ∏ q ∈ s,
            (1 + 3 * ‖criticalLiFrequencyWeight q‖ ^ 2) := by
          classical
          revert hs
          induction s using Finset.induction_on with
          | empty =>
              intro hs
              simp
          | @insert q s hq ih =>
              intro hs
              rw [Finset.prod_insert hq, Finset.prod_insert hq]
              have hq4 : 4 ≤ q := hs q (Finset.mem_insert_self q s)
              have hs4 : ∀ r ∈ s, 4 ≤ r := by
                intro r hr
                exact hs r (Finset.mem_insert_of_mem hr)
              exact mul_le_mul
                (norm_criticalLiScalarCorrection_le hq4)
                (ih hs4) (by positivity) (by positivity)
    _ ≤ Real.exp
          (∑ q ∈ s, 3 * ‖criticalLiFrequencyWeight q‖ ^ 2) :=
          criticalLi_prod_one_add_three_sq_le_exp_sum s
    _ ≤ Real.exp (3 * criticalLiCollisionBudget) := by
          apply Real.exp_le_exp.mpr
          calc
            (∑ q ∈ s, 3 * ‖criticalLiFrequencyWeight q‖ ^ 2)
                = 3 * (∑ q ∈ s, ‖criticalLiFrequencyWeight q‖ ^ 2) := by
                    rw [Finset.mul_sum]
            _ ≤ 3 * criticalLiCollisionBudget :=
              mul_le_mul_of_nonneg_left
                (criticalLiFrequencyWeight_sq_finset_sum_le s) (by norm_num)

/-- Elementary finite Euler correction: a product of local factors 1+a_q is
controlled by exp(sum a_q). -/
private theorem criticalLi_prod_one_add_sq_le_exp_sum
    (s : Finset ℕ) :
    (∏ q ∈ s, (1 + ‖criticalLiFrequencyWeight q‖ ^ 2)) ≤
      Real.exp (∑ q ∈ s, ‖criticalLiFrequencyWeight q‖ ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert q s hq ih =>
      rw [Finset.prod_insert hq, Finset.sum_insert hq, Real.exp_add]
      have hfac :
          1 + ‖criticalLiFrequencyWeight q‖ ^ 2 ≤
            Real.exp (‖criticalLiFrequencyWeight q‖ ^ 2) := by
        simpa [add_comm] using
          (Real.add_one_le_exp (‖criticalLiFrequencyWeight q‖ ^ 2))
      exact mul_le_mul hfac ih (by positivity) (by positivity)

/-- **Uniform finite hard-core Euler correction bound.**
Square summability upgrades to a single multiplicative constant independent of
the number of Li sites. -/
theorem criticalLi_prod_one_add_sq_le_exp_budget
    (s : Finset ℕ) :
    (∏ q ∈ s, (1 + ‖criticalLiFrequencyWeight q‖ ^ 2)) ≤
      Real.exp criticalLiCollisionBudget := by
  calc
    (∏ q ∈ s, (1 + ‖criticalLiFrequencyWeight q‖ ^ 2))
        ≤ Real.exp (∑ q ∈ s, ‖criticalLiFrequencyWeight q‖ ^ 2) :=
          criticalLi_prod_one_add_sq_le_exp_sum s
    _ ≤ Real.exp criticalLiCollisionBudget := by
          exact Real.exp_le_exp.mpr
            (criticalLiFrequencyWeight_sq_finset_sum_le s)



/-! ## Formal power-series one-site hard-core / Poisson factorization -/

/-- Formal correction series at one critical owner.  This is the exact
coefficient object whose degree-zero coefficient is one, whose degree-one
coefficient vanishes, and whose higher coefficients are bounded above by
`hardCorePoissonCorrectionTailTerm`. -/
def hardCorePoissonCorrectionSeries (z : ℂ) : PowerSeries ℂ :=
  (1 - PowerSeries.C z * PowerSeries.X) *
    PowerSeries.rescale z (PowerSeries.exp ℂ)

/-- Formal Poisson exponential carrying the same one-site linear mass with
opposite sign. -/
def poissonExponentialSeries (z : ℂ) : PowerSeries ℂ :=
  PowerSeries.rescale (-z) (PowerSeries.exp ℂ)

/-- **Exact one-site factorization.**
The full hard-core factor is the bounded quadratic correction series followed
by the Poisson exponential.  No estimate occurs here: this is an identity of
formal power series. -/
theorem hardCorePoissonCorrectionSeries_mul_poissonExponentialSeries
    (z : ℂ) :
    hardCorePoissonCorrectionSeries z * poissonExponentialSeries z =
      1 - PowerSeries.C z * PowerSeries.X := by
  unfold hardCorePoissonCorrectionSeries poissonExponentialSeries
  rw [mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add z (-z)]
  simp


/-- The coefficient formula used by the quadratic variation budget is exactly
the coefficient sequence of the formal correction series above. -/
theorem coeff_hardCorePoissonCorrectionSeries
    (z : ℂ) (m : ℕ) :
    PowerSeries.coeff m (hardCorePoissonCorrectionSeries z) =
      hardCorePoissonCorrectionCoeff z m := by
  cases m with
  | zero =>
      simp only [hardCorePoissonCorrectionSeries,
        hardCorePoissonCorrectionCoeff, Nat.cast_zero, sub_zero, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one]
      rw [sub_mul, one_mul]
      simp only [map_sub, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_mul]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      simp
  | succ n =>
      let E : PowerSeries ℂ :=
        PowerSeries.rescale z (PowerSeries.exp ℂ)
      have hE (k : ℕ) :
          PowerSeries.coeff k E =
            z ^ k / (Nat.factorial k : ℂ) := by
        dsimp [E]
        rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
        simp [div_eq_mul_inv]
      change
        PowerSeries.coeff (n + 1)
            ((1 - PowerSeries.C z * PowerSeries.X) * E) =
          ((1 : ℂ) - ((n + 1 : ℕ) : ℂ)) * z ^ (n + 1) /
            (Nat.factorial (n + 1) : ℂ)
      rw [sub_mul, one_mul]
      simp only [map_sub]
      rw [mul_assoc, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, hE, hE, Nat.factorial_succ]
      push_cast
      have hfac : (Nat.factorial n : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      field_simp [hfac]
      ring





/-! ## Arithmetic-function coefficient factorization bridge -/

/-- Cumulative mass of an arithmetic coefficient sequence through an integer
endpoint. -/
def arithmeticCoefficientCumulative
    (f : ArithmeticFunction ℂ) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, f n

/-- **Finite cumulative Dirichlet-convolution identity.**
The cumulative mass of a coefficient convolution is the multiplicative
convolution of the first coefficient sequence with the cumulative second
sequence.  This is the exact bridge from local Euler-factor identities to the
finite cumulative convolution closure below. -/
theorem arithmeticCoefficientCumulative_mul
    (f g : ArithmeticFunction ℂ) (X : ℕ) :
    arithmeticCoefficientCumulative (f * g) X =
      ∑ a ∈ Finset.Icc 1 X,
        f a * arithmeticCoefficientCumulative g (X / a) := by
  unfold arithmeticCoefficientCumulative
  calc
    (∑ n ∈ Finset.Icc 1 X, (f * g) n) =
        ∑ n ∈ Finset.Icc 1 X,
          ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2 := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [ArithmeticFunction.mul_apply]
    _ = ∑ a ∈ Finset.Icc 1 X,
          ∑ b ∈ Finset.Icc 1 (X / a), f a * g b :=
        sum_Icc_divisorsAntidiagonal_eq_sum_div
          (fun a b => f a * g b) X
    _ = ∑ a ∈ Finset.Icc 1 X,
          f a * ∑ b ∈ Finset.Icc 1 (X / a), g b := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]



/-- Cumulative coefficient mass is linear under subtraction. -/
theorem arithmeticCoefficientCumulative_sub
    (f g : ArithmeticFunction ℂ) (X : ℕ) :
    arithmeticCoefficientCumulative (f - g) X =
      arithmeticCoefficientCumulative f X -
        arithmeticCoefficientCumulative g X := by
  unfold arithmeticCoefficientCumulative
  rw [← Finset.sum_sub_distrib]
  rfl

/-- One coefficient atom at a positive multiplicative site.  The explicit
`q ≠ 0` guard makes this an arithmetic function for all natural `q`; all
hard-core uses below have `q ≥ 1`. -/
def arithmeticSiteAtom (q : ℕ) (a : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = q ∧ q ≠ 0 then a else 0, by
    change (if (0 : ℕ) = q ∧ q ≠ 0 then a else 0) = 0
    have hfalse : ¬((0 : ℕ) = q ∧ q ≠ 0) := by
      rintro ⟨h0q, hq0⟩
      exact hq0 h0q.symm
    rw [if_neg hfalse]⟩

@[simp] theorem arithmeticSiteAtom_apply_of_pos
    {q : ℕ} (hq : 1 ≤ q) (a : ℂ) (n : ℕ) :
    arithmeticSiteAtom q a n = if n = q then a else 0 := by
  unfold arithmeticSiteAtom
  have hq0 : q ≠ 0 := by omega
  by_cases hn : n = q
  · simp [hn, hq0]
  · simp [hn]

/-- Convolving with one positive-site atom shifts the cumulative endpoint by
the exact floor quotient. -/
theorem arithmeticCoefficientCumulative_siteAtom_mul
    {q : ℕ} (hq : 1 ≤ q) (a : ℂ)
    (f : ArithmeticFunction ℂ) (X : ℕ) :
    arithmeticCoefficientCumulative (arithmeticSiteAtom q a * f) X =
      a * arithmeticCoefficientCumulative f (X / q) := by
  rw [arithmeticCoefficientCumulative_mul]
  by_cases hqX : q ≤ X
  · have hqmem : q ∈ Finset.Icc 1 X :=
      Finset.mem_Icc.mpr ⟨hq, hqX⟩
    simp [arithmeticSiteAtom_apply_of_pos hq, hqmem]
  · have hXq : X < q := lt_of_not_ge hqX
    have hdiv : X / q = 0 := Nat.div_eq_of_lt hXq
    have hqnot : q ∉ Finset.Icc 1 X := by
      simp [Finset.mem_Icc, hqX]
    rw [hdiv]
    simp [arithmeticCoefficientCumulative,
      arithmeticSiteAtom_apply_of_pos hq, hqnot]

/-- One exact hard-core Euler coefficient factor `1 - a δ_q`. -/
def arithmeticHardCoreLocalFactor
    (a : ℂ) (q : ℕ) : ArithmeticFunction ℂ :=
  1 - arithmeticSiteAtom q a

/-- **Coefficient-level hard-core update identity.**
Cumulative multiplication by `1-a δ_q` is exactly the activated floor
update used by the all-scale frequency recursion. -/
theorem arithmeticCoefficientCumulative_hardCoreLocalFactor_mul
    {q : ℕ} (hq : 1 ≤ q) (a : ℂ)
    (f : ArithmeticFunction ℂ) (X : ℕ) :
    arithmeticCoefficientCumulative
        (arithmeticHardCoreLocalFactor a q * f) X =
      arithmeticCoefficientCumulative f X -
        a * arithmeticCoefficientCumulative f (X / q) := by
  unfold arithmeticHardCoreLocalFactor
  rw [sub_mul, one_mul, arithmeticCoefficientCumulative_sub,
    arithmeticCoefficientCumulative_siteAtom_mul hq]


/-- Finite hard-core arithmetic coefficient product over the sites
`2,...,k+1`, in the same order as `frequencyHardCoreIterate`. -/
def arithmeticHardCoreProduct
    (w : ℕ → ℂ) : ℕ → ArithmeticFunction ℂ
  | 0 => 1
  | k + 1 =>
      arithmeticHardCoreLocalFactor (w (k + 2)) (k + 2) *
        arithmeticHardCoreProduct w k

/-- The cumulative unit arithmetic function is one at every positive endpoint. -/
theorem arithmeticCoefficientCumulative_one
    {X : ℕ} (hX : 1 ≤ X) :
    arithmeticCoefficientCumulative (1 : ArithmeticFunction ℂ) X = 1 := by
  unfold arithmeticCoefficientCumulative
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 X :=
    Finset.mem_Icc.mpr ⟨le_rfl, hX⟩
  simp [ArithmeticFunction.one_apply, h1]

/-- **Exact global hard-core coefficient realization.**
At every positive endpoint, the cumulative finite Euler coefficient product is
literally the same state produced by the recursive activated hard-core
operators. -/
theorem arithmeticHardCoreProduct_cumulative_eq_frequencyHardCoreIterate
    (w : ℕ → ℂ) (k X : ℕ) (hX : 1 ≤ X) :
    arithmeticCoefficientCumulative (arithmeticHardCoreProduct w k) X =
      frequencyHardCoreIterate w k (fun _ => 1) X := by
  induction k generalizing X with
  | zero =>
      simp [arithmeticHardCoreProduct, frequencyHardCoreIterate,
        arithmeticCoefficientCumulative_one hX]
  | succ k ih =>
      rw [arithmeticHardCoreProduct,
        arithmeticCoefficientCumulative_hardCoreLocalFactor_mul
          (q := k + 2) (by omega : 1 ≤ k + 2)]
      change
        arithmeticCoefficientCumulative (arithmeticHardCoreProduct w k) X -
            w (k + 2) *
              arithmeticCoefficientCumulative
                (arithmeticHardCoreProduct w k) (X / (k + 2)) =
          frequencyHardCoreUpdate (w (k + 2)) (k + 2)
            (frequencyHardCoreIterate w k (fun _ => 1)) X
      rw [ih X hX]
      unfold frequencyHardCoreUpdate
      by_cases henter : k + 2 ≤ X
      · have hqpos : 0 < k + 2 := by omega
        have hchild : 1 ≤ X / (k + 2) :=
          (Nat.one_le_div_iff hqpos).2 henter
        rw [ih (X / (k + 2)) hchild]
        simp [activatedFloorChild, henter]
      · have hlt : X < k + 2 := lt_of_not_ge henter
        have hdiv : X / (k + 2) = 0 := Nat.div_eq_of_lt hlt
        rw [hdiv]
        simp [activatedFloorChild, henter,
          arithmeticCoefficientCumulative]

/-- Every all-scale Li state diagonal is exactly the cumulative hard-core
arithmetic coefficient product through the same cutoff. -/
theorem allScaleLiState_diagonal_eq_hardCoreProductCumulative
    {L : ℕ → ℕ → ℂ} (X : ℕ) (hX : 1 ≤ X)
    (hL : IsAllScaleLiState L) :
    L X X =
      arithmeticCoefficientCumulative
        (arithmeticHardCoreProduct primeSievePNTDensity (X - 1)) X := by
  have hiter :=
    primeFrequencyState_eq_hardCoreIterate hL (X - 1) X
  have hpred : X - 1 + 1 = X := Nat.sub_add_cancel hX
  rw [hpred] at hiter
  rw [hiter]
  symm
  exact arithmeticHardCoreProduct_cumulative_eq_frequencyHardCoreIterate
    primeSievePNTDensity (X - 1) X hX


/-! ## Local backport: power series to arithmetic coefficients -/

/-- The antidiagonal of exponents embeds into the divisor antidiagonal of
`q^k`.  This is the only divisor lemma needed by the local power-series
embedding below; it is present in newer Mathlib but not in the revision pinned
by this repository. -/
private theorem li_antidiagonal_map_subset_divisorsAntidiagonal_pow
    {q : ℕ} (hq : 1 < q) (k : ℕ) :
    letI ι : ℕ ↪ ℕ :=
      ⟨fun j ↦ q ^ j, Nat.pow_right_injective hq⟩
    (Finset.antidiagonal k).map (.prodMap ι ι) ⊆
      (q ^ k).divisorsAntidiagonal := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  simp [Nat.mem_divisorsAntidiagonal,
    ← Finset.mem_antidiagonal.mp hi, pow_add, ne_zero_of_lt hq]

/-- Local ring-hom backport of the newer Mathlib power-series embedding.
For a fixed genuine site `q > 1`, it sends the coefficient of `T^k` to the
arithmetic site `q^k`.  A ring hom is sufficient here; the newer Mathlib
`Algebra` instance for arithmetic functions is not available at the revision
pinned by this repository. -/
private noncomputable def liArithmeticOfPowerSeries
    {q : ℕ} (hq : 1 < q) :
    PowerSeries ℂ →+* ArithmeticFunction ℂ where
  toFun F :=
    ⟨Function.extend (q ^ ·) (F.coeff ·) 0,
      by simp [Nat.ne_zero_of_lt hq]⟩
  map_zero' := by
    ext n
    by_cases hn : ∃ k, q ^ k = n
    · obtain ⟨k, rfl⟩ := hn
      simp [(Nat.pow_right_injective hq).extend_apply]
    · change
        Function.extend (q ^ ·)
            ((0 : PowerSeries ℂ).coeff ·) 0 n = 0
      rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply]
  map_one' := by
    ext n
    by_cases hn : ∃ k, q ^ k = n
    · obtain ⟨k, rfl⟩ := hn
      simp [(Nat.pow_right_injective hq).extend_apply,
        ArithmeticFunction.one_apply, hq.ne']
    · change
        Function.extend (q ^ ·)
            ((1 : PowerSeries ℂ).coeff ·) 0 n =
          (1 : ArithmeticFunction ℂ) n
      rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply]
      have hn1 : n ≠ 1 := by
        intro hn1
        apply hn
        exact ⟨0, by simp [hn1]⟩
      simp [hn1]
  map_add' F G := by
    ext n
    by_cases hn : ∃ k, q ^ k = n
    · obtain ⟨k, rfl⟩ := hn
      simp [(Nat.pow_right_injective hq).extend_apply]
    · simp [Function.extend_apply' _ _ _ hn]
  map_mul' F G := by
    ext n
    rw [ArithmeticFunction.mul_apply]
    change
      Function.extend (q ^ ·) ((F * G).coeff ·) 0 n =
        ∑ p ∈ n.divisorsAntidiagonal,
          Function.extend (q ^ ·) (F.coeff ·) 0 p.1 *
            Function.extend (q ^ ·) (G.coeff ·) 0 p.2
    by_cases hn : ∃ k, q ^ k = n
    · obtain ⟨k, rfl⟩ := hn
      rw [(Nat.pow_right_injective hq).extend_apply]
      have hs :
          (Finset.antidiagonal k).map
              (.prodMap
                ⟨fun j ↦ q ^ j, Nat.pow_right_injective hq⟩
                ⟨fun j ↦ q ^ j, Nat.pow_right_injective hq⟩) ⊆
            (q ^ k).divisorsAntidiagonal :=
        li_antidiagonal_map_subset_divisorsAntidiagonal_pow hq k
      rw [PowerSeries.coeff_mul k F G, ← Finset.sum_subset hs]
      · simp [(Nat.pow_right_injective hq).extend_apply]
      · intro p hp hnot
        rcases p with ⟨a, b⟩
        obtain ⟨hab, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
        by_cases ha : ∃ i, q ^ i = a
        · by_cases hb : ∃ j, q ^ j = b
          · obtain ⟨i, rfl⟩ := ha
            obtain ⟨j, rfl⟩ := hb
            have hij : i + j = k := by
              apply Nat.pow_right_injective hq
              simpa [pow_add] using hab
            exfalso
            apply hnot
            apply Finset.mem_map.mpr
            refine ⟨(i, j), ?_, ?_⟩
            · simpa [Finset.mem_antidiagonal] using hij
            · rfl
          · rw [Function.extend_apply' _ _ _ hb, Pi.zero_apply, mul_zero]
        · rw [Function.extend_apply' _ _ _ ha, Pi.zero_apply, zero_mul]
    · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply,
        Finset.sum_eq_zero]
      intro p hp
      rcases p with ⟨a, b⟩
      obtain ⟨hab, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      by_cases ha : ∃ i, q ^ i = a
      · by_cases hb : ∃ j, q ^ j = b
        · obtain ⟨i, rfl⟩ := ha
          obtain ⟨j, rfl⟩ := hb
          exfalso
          apply hn
          refine ⟨i + j, ?_⟩
          simpa [pow_add] using hab
        · rw [Function.extend_apply' _ _ _ hb, Pi.zero_apply, mul_zero]
      · rw [Function.extend_apply' _ _ _ ha, Pi.zero_apply, zero_mul]

private theorem liArithmeticOfPowerSeries_apply
    {q : ℕ} (hq : 1 < q) (F : PowerSeries ℂ) (n : ℕ) :
    liArithmeticOfPowerSeries hq F n =
      Function.extend (q ^ ·) (F.coeff ·) 0 n := by
  rfl

private theorem liArithmeticOfPowerSeries_apply_pow
    {q : ℕ} (hq : 1 < q) (F : PowerSeries ℂ) (k : ℕ) :
    liArithmeticOfPowerSeries hq F (q ^ k) = F.coeff k := by
  rw [liArithmeticOfPowerSeries_apply hq,
    (Nat.pow_right_injective hq).extend_apply]

/-! ## Transport the formal local factorization to Dirichlet convolution -/

/-- A single positive-site arithmetic atom is exactly the image of the
one-variable monomial `a*T` under the local formal power-series embedding. -/
theorem arithmeticSiteAtom_eq_liArithmeticOfPowerSeries_C_mul_X
    {q : ℕ} (hq : 1 < q) (a : ℂ) :
    arithmeticSiteAtom q a =
      liArithmeticOfPowerSeries hq
        (PowerSeries.C a * PowerSeries.X) := by
  ext n
  rw [liArithmeticOfPowerSeries_apply hq]
  by_cases hn : ∃ k : ℕ, q ^ k = n
  · obtain ⟨k, rfl⟩ := hn
    rw [(Nat.pow_right_injective hq).extend_apply]
    rw [arithmeticSiteAtom_apply_of_pos (by omega : 1 ≤ q)]
    have hcoeff :
        PowerSeries.coeff k
            (PowerSeries.C a * PowerSeries.X : PowerSeries ℂ) =
          if k = 1 then a else 0 := by
      simpa using (PowerSeries.coeff_C_mul_X_pow a 1 k)
    rw [hcoeff]
    by_cases hk : k = 1
    · subst k
      simp
    · have hpow : q ^ k ≠ q := by
        intro h
        have : k = 1 := by
          apply Nat.pow_right_injective hq
          simpa using h
        exact hk this
      simp [hk, hpow]
  · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply]
    rw [arithmeticSiteAtom_apply_of_pos (by omega : 1 ≤ q)]
    have hnq : n ≠ q := by
      intro hnq
      apply hn
      exact ⟨1, by simp [hnq]⟩
    simp [hnq]

/-- Arithmetic-function image of the exact quadratic hard-core/Poisson
correction factor at one genuine site. -/
def arithmeticHardCorePoissonCorrectionFactor
    (a : ℂ) {q : ℕ} (hq : 1 < q) : ArithmeticFunction ℂ :=
  liArithmeticOfPowerSeries hq
    (hardCorePoissonCorrectionSeries a)

/-- Arithmetic-function image of the one-site Poisson exponential. -/
def arithmeticPoissonLocalFactor
    (a : ℂ) {q : ℕ} (hq : 1 < q) : ArithmeticFunction ℂ :=
  liArithmeticOfPowerSeries hq
    (poissonExponentialSeries a)

/-- **Exact one-site Dirichlet factorization.**
For every genuine multiplicative site `q > 1`, the hard-core coefficient
factor is exactly the Dirichlet convolution of the quadratic correction factor
and the Poisson factor. -/
theorem arithmeticHardCoreLocalFactor_eq_correction_mul_poisson
    {q : ℕ} (hq : 1 < q) (a : ℂ) :
    arithmeticHardCoreLocalFactor a q =
      arithmeticHardCorePoissonCorrectionFactor a hq *
        arithmeticPoissonLocalFactor a hq := by
  unfold arithmeticHardCorePoissonCorrectionFactor
    arithmeticPoissonLocalFactor
  rw [← map_mul,
    hardCorePoissonCorrectionSeries_mul_poissonExponentialSeries]
  unfold arithmeticHardCoreLocalFactor
  rw [map_sub, map_one]
  congr 1
  exact
    arithmeticSiteAtom_eq_liArithmeticOfPowerSeries_C_mul_X hq a

/-- At a pure power of its site, the arithmetic correction factor is exactly
the corresponding formal correction coefficient. -/
theorem arithmeticHardCorePoissonCorrectionFactor_apply_pow
    {q : ℕ} (hq : 1 < q) (a : ℂ) (m : ℕ) :
    arithmeticHardCorePoissonCorrectionFactor a hq (q ^ m) =
      hardCorePoissonCorrectionCoeff a m := by
  unfold arithmeticHardCorePoissonCorrectionFactor
  rw [liArithmeticOfPowerSeries_apply_pow hq,
    coeff_hardCorePoissonCorrectionSeries]

/-- Away from the powers of its site, the arithmetic correction factor
vanishes identically. -/
theorem arithmeticHardCorePoissonCorrectionFactor_apply_eq_zero_of_not_pow
    {q n : ℕ} (hq : 1 < q) (a : ℂ)
    (hn : ¬ ∃ m : ℕ, q ^ m = n) :
    arithmeticHardCorePoissonCorrectionFactor a hq n = 0 := by
  unfold arithmeticHardCorePoissonCorrectionFactor
  rw [liArithmeticOfPowerSeries_apply hq,
    Function.extend_apply' _ _ _ hn, Pi.zero_apply]

/-- Critical weighted total variation of a correction kernel up to X. -/
def criticalWeightedVariation
    (h : ℕ → ℂ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X,
    ‖h n‖ / Real.sqrt (n : ℝ)


/-- Exponents whose site powers are visible below a finite endpoint. -/
private def liCorrectionExponentSet (q X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun m => q ^ m ≤ X)

private theorem li_exponent_le_endpoint_of_pow_le
    {q m X : ℕ} (hq : 1 < q) (hmX : q ^ m ≤ X) :
    m ≤ X := by
  have hq1 : 1 ≤ q := by omega
  have hmq : m ≤ q ^ m := by
    calc
      m = 1 * m := by simp
      _ ≤ q * m := Nat.mul_le_mul_right m hq1
      _ ≤ q ^ m := Nat.mul_le_pow (by omega : q ≠ 1) m
  exact hmq.trans hmX

/-- **Sparse-support reindexing of one correction factor.**
Its critical arithmetic variation is exactly the finite sum of the formal
correction coefficients over the powers visible at the endpoint. -/
theorem criticalWeightedVariation_hardCorePoissonCorrectionFactor_eq
    {q : ℕ} (hq : 1 < q) (a : ℂ) (X : ℕ) :
    criticalWeightedVariation
        (fun n => arithmeticHardCorePoissonCorrectionFactor a hq n) X =
      ∑ m ∈ liCorrectionExponentSet q X,
        ‖hardCorePoissonCorrectionCoeff a m‖ /
          Real.sqrt ((q ^ m : ℕ) : ℝ) := by
  unfold criticalWeightedVariation
  let E := liCorrectionExponentSet q X
  have hinj : Function.Injective (fun m : ℕ => q ^ m) :=
    Nat.pow_right_injective hq
  have hsub :
      E.image (fun m : ℕ => q ^ m) ⊆ Finset.Icc 1 X := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨m, hmE, rfl⟩
    have hmdata := Finset.mem_filter.mp hmE
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_pow m q (by omega), hmdata.2⟩
  calc
    (∑ n ∈ Finset.Icc 1 X,
        ‖arithmeticHardCorePoissonCorrectionFactor a hq n‖ /
          Real.sqrt (n : ℝ))
        = ∑ n ∈ E.image (fun m : ℕ => q ^ m),
            ‖arithmeticHardCorePoissonCorrectionFactor a hq n‖ /
              Real.sqrt (n : ℝ) := by
          symm
          apply Finset.sum_subset hsub
          intro n hnI hnNot
          have hnNotPow : ¬ ∃ m : ℕ, q ^ m = n := by
            rintro ⟨m, hm⟩
            have hnX := (Finset.mem_Icc.mp hnI).2
            have hmX : q ^ m ≤ X := hm.trans_le hnX
            have hmle : m ≤ X :=
              li_exponent_le_endpoint_of_pow_le hq hmX
            have hmE : m ∈ E := by
              dsimp [E, liCorrectionExponentSet]
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hmle), hmX⟩
            apply hnNot
            exact Finset.mem_image.mpr ⟨m, hmE, hm⟩
          rw [
            arithmeticHardCorePoissonCorrectionFactor_apply_eq_zero_of_not_pow
              hq a hnNotPow,
            norm_zero, zero_div]
    _ = ∑ m ∈ E,
          ‖hardCorePoissonCorrectionCoeff a m‖ /
            Real.sqrt ((q ^ m : ℕ) : ℝ) := by
          rw [Finset.sum_image]
          · apply Finset.sum_congr rfl
            intro m hm
            rw [arithmeticHardCorePoissonCorrectionFactor_apply_pow]
          · intro m _hm n _hn hmn
            exact hinj hmn
    _ = _ := by rfl

/-- Nonnegative absolute coefficient majorant for one complete local
hard-core/Poisson correction series. -/
private def hardCorePoissonCorrectionVariationTerm
    (z : ℂ) : ℕ → ℝ
  | 0 => 1
  | Nat.succ 0 => 0
  | Nat.succ (Nat.succ m) =>
      hardCorePoissonCorrectionTailTerm ‖z‖ m

private theorem norm_hardCorePoissonCorrectionCoeff_eq_variationTerm
    (z : ℂ) (m : ℕ) :
    ‖hardCorePoissonCorrectionCoeff z m‖ =
      hardCorePoissonCorrectionVariationTerm z m := by
  cases m with
  | zero =>
      simp [hardCorePoissonCorrectionVariationTerm]
  | succ m =>
      cases m with
      | zero =>
          simp [hardCorePoissonCorrectionVariationTerm]
      | succ m =>
          simpa [hardCorePoissonCorrectionVariationTerm,
            hardCorePoissonCorrectionTailTerm,
            Nat.succ_eq_add_one, Nat.add_assoc] using
            norm_hardCorePoissonCorrectionCoeff_add_two z m

private theorem hardCorePoissonCorrectionVariationTerm_nonneg
    (z : ℂ) (m : ℕ) :
    0 ≤ hardCorePoissonCorrectionVariationTerm z m := by
  cases m with
  | zero =>
      simp [hardCorePoissonCorrectionVariationTerm]
  | succ m =>
      cases m with
      | zero =>
          simp [hardCorePoissonCorrectionVariationTerm]
      | succ m =>
          simpa [hardCorePoissonCorrectionVariationTerm,
            Nat.succ_eq_add_one, Nat.add_assoc] using
            hardCorePoissonCorrectionTailTerm_nonneg
              (a := ‖z‖) (norm_nonneg z) m

private theorem hardCorePoissonCorrectionVariationTerm_summable
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable (hardCorePoissonCorrectionVariationTerm z) := by
  rw [← summable_nat_add_iff 2 (G := ℝ)]
  simpa [hardCorePoissonCorrectionVariationTerm,
    Nat.add_assoc] using
    hardCorePoissonCorrectionTailTerm_summable
      (a := ‖z‖) (norm_nonneg z) hz

private theorem tsum_hardCorePoissonCorrectionVariationTerm_eq
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∑' m : ℕ, hardCorePoissonCorrectionVariationTerm z m) =
      1 + ∑' m : ℕ,
        hardCorePoissonCorrectionTailTerm ‖z‖ m := by
  have hs :=
    hardCorePoissonCorrectionVariationTerm_summable z hz
  have hsplit := hs.sum_add_tsum_nat_add 2
  have hhead :
      (∑ m ∈ Finset.range 2,
        hardCorePoissonCorrectionVariationTerm z m) = 1 := by
    norm_num [Finset.sum_range_succ,
      hardCorePoissonCorrectionVariationTerm]
  have htail :
      (∑' m : ℕ,
        hardCorePoissonCorrectionVariationTerm z (m + 2)) =
      ∑' m : ℕ,
        hardCorePoissonCorrectionTailTerm ‖z‖ m := by
    apply tsum_congr
    intro m
    simp [hardCorePoissonCorrectionVariationTerm]
  calc
    (∑' m : ℕ, hardCorePoissonCorrectionVariationTerm z m) =
        (∑ m ∈ Finset.range 2,
            hardCorePoissonCorrectionVariationTerm z m) +
          ∑' m : ℕ,
            hardCorePoissonCorrectionVariationTerm z (m + 2) :=
      hsplit.symm
    _ = 1 + ∑' m : ℕ,
          hardCorePoissonCorrectionTailTerm ‖z‖ m := by
      rw [hhead, htail]

/-- **One complete Li correction factor has uniformly bounded critical
variation.**  This is the local estimate needed by the hyperbola-product
induction; the denominator n^(1/2) only improves the coefficient variation. -/
theorem criticalWeightedVariation_hardCorePoissonCorrectionFactor_le_local
    {q : ℕ} (hq : 2 ≤ q) (X : ℕ) :
    criticalWeightedVariation
        (fun n =>
          arithmeticHardCorePoissonCorrectionFactor
            (criticalLiFrequencyWeight q) (q := q) (by omega) n) X ≤
      criticalLiLocalCorrectionVariation q := by
  have hqgt : 1 < q := by omega
  have hz : ‖criticalLiFrequencyWeight q‖ ≤ 1 :=
    norm_criticalLiFrequencyWeight_le_one_of_two_le hq
  rw [criticalWeightedVariation_hardCorePoissonCorrectionFactor_eq
    hqgt (criticalLiFrequencyWeight q) X]
  have hs :=
    hardCorePoissonCorrectionVariationTerm_summable
      (criticalLiFrequencyWeight q) hz
  calc
    (∑ m ∈ liCorrectionExponentSet q X,
        ‖hardCorePoissonCorrectionCoeff
            (criticalLiFrequencyWeight q) m‖ /
          Real.sqrt ((q ^ m : ℕ) : ℝ))
        ≤ ∑ m ∈ liCorrectionExponentSet q X,
            hardCorePoissonCorrectionVariationTerm
              (criticalLiFrequencyWeight q) m := by
          apply Finset.sum_le_sum
          intro m hm
          have hpowNat : 1 ≤ q ^ m :=
            Nat.one_le_pow m q (by omega)
          have hpowReal : (1 : ℝ) ≤ ((q ^ m : ℕ) : ℝ) := by
            exact_mod_cast hpowNat
          have hsqrt :
              (1 : ℝ) ≤ Real.sqrt ((q ^ m : ℕ) : ℝ) :=
            (Real.one_le_sqrt).2 hpowReal
          have hsqrtpos :
              0 < Real.sqrt ((q ^ m : ℕ) : ℝ) :=
            lt_of_lt_of_le zero_lt_one hsqrt
          have hn0 :
              0 ≤ ‖hardCorePoissonCorrectionCoeff
                (criticalLiFrequencyWeight q) m‖ :=
            norm_nonneg _
          have hmul :
              0 ≤ ‖hardCorePoissonCorrectionCoeff
                    (criticalLiFrequencyWeight q) m‖ *
                  (Real.sqrt ((q ^ m : ℕ) : ℝ) - 1) :=
            mul_nonneg hn0 (sub_nonneg.mpr hsqrt)
          have hdiv :
              ‖hardCorePoissonCorrectionCoeff
                    (criticalLiFrequencyWeight q) m‖ /
                  Real.sqrt ((q ^ m : ℕ) : ℝ) ≤
                ‖hardCorePoissonCorrectionCoeff
                    (criticalLiFrequencyWeight q) m‖ := by
            apply (div_le_iff₀ hsqrtpos).2
            nlinarith
          calc
            ‖hardCorePoissonCorrectionCoeff
                  (criticalLiFrequencyWeight q) m‖ /
                Real.sqrt ((q ^ m : ℕ) : ℝ)
                ≤ ‖hardCorePoissonCorrectionCoeff
                    (criticalLiFrequencyWeight q) m‖ := hdiv
            _ = hardCorePoissonCorrectionVariationTerm
                  (criticalLiFrequencyWeight q) m :=
              norm_hardCorePoissonCorrectionCoeff_eq_variationTerm _ _
    _ ≤ ∑' m : ℕ,
          hardCorePoissonCorrectionVariationTerm
            (criticalLiFrequencyWeight q) m := by
          exact hs.sum_le_tsum
            (liCorrectionExponentSet q X)
            (fun m hm =>
              hardCorePoissonCorrectionVariationTerm_nonneg
                (criticalLiFrequencyWeight q) m)
    _ = criticalLiLocalCorrectionVariation q := by
          rw [tsum_hardCorePoissonCorrectionVariationTerm_eq
            (criticalLiFrequencyWeight q) hz]
          rfl

/-- Exact norm of the critical square-root weight away from zero. -/
theorem norm_criticalSqrtWeight_eq_inv_sqrt
    {q : ℕ} (hq : 1 ≤ q) :
    ‖criticalSqrtWeight q‖ = 1 / Real.sqrt (q : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hsqrtpos : 0 < Real.sqrt (q : ℝ) :=
    Real.sqrt_pos.2 hqpos
  unfold criticalSqrtWeight
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsqrtpos]
  simp [one_div]

/-- The exact critical weight respects natural powers. -/
theorem criticalSqrtWeight_pow (q m : ℕ) :
    criticalSqrtWeight (q ^ m) =
      criticalSqrtWeight q ^ m := by
  induction m with
  | zero =>
      simp [criticalSqrtWeight]
  | succ m ih =>
      rw [pow_succ, criticalSqrtWeight_mul, ih, pow_succ]

/-- Scaling the local owner mass scales its degree-m correction coefficient by
the m-th power of the same scalar. -/
theorem hardCorePoissonCorrectionCoeff_mul_scale
    (a r : ℂ) (m : ℕ) :
    hardCorePoissonCorrectionCoeff (a * r) m =
      hardCorePoissonCorrectionCoeff a m * r ^ m := by
  unfold hardCorePoissonCorrectionCoeff
  rw [mul_pow]
  ring

/-- The arithmetic critical weight q^(-m/2) converts the raw Li correction
coefficient at q^m exactly into the correction coefficient of the transformed
owner z_q = w_q / sqrt(q). -/
theorem norm_hardCorePoissonCorrectionCoeff_div_sqrt_pow_eq
    {q : ℕ} (hq : 1 ≤ q) (a : ℂ) (m : ℕ) :
    ‖hardCorePoissonCorrectionCoeff a m‖ /
        Real.sqrt ((q ^ m : ℕ) : ℝ) =
      ‖hardCorePoissonCorrectionCoeff
          (a * criticalSqrtWeight q) m‖ := by
  have hqpow : 1 ≤ q ^ m :=
    Nat.one_le_pow m q hq
  have hweight :
      (Real.sqrt ((q ^ m : ℕ) : ℝ))⁻¹ =
        ‖criticalSqrtWeight q‖ ^ m := by
    calc
      (Real.sqrt ((q ^ m : ℕ) : ℝ))⁻¹ =
          ‖criticalSqrtWeight (q ^ m)‖ := by
            symm
            simpa [one_div] using
              (norm_criticalSqrtWeight_eq_inv_sqrt (q := q ^ m) hqpow)
      _ = ‖criticalSqrtWeight q ^ m‖ := by
            rw [criticalSqrtWeight_pow]
      _ = ‖criticalSqrtWeight q‖ ^ m := by
            rw [norm_pow]
  rw [div_eq_mul_inv, hweight]
  calc
    ‖hardCorePoissonCorrectionCoeff a m‖ *
          ‖criticalSqrtWeight q‖ ^ m =
        ‖hardCorePoissonCorrectionCoeff a m *
          criticalSqrtWeight q ^ m‖ := by
            rw [norm_mul, norm_pow]
    _ = ‖hardCorePoissonCorrectionCoeff
          (a * criticalSqrtWeight q) m‖ := by
            rw [hardCorePoissonCorrectionCoeff_mul_scale]

/-- On the unit ball, the complete absolute coefficient sequence of the local
hard-core/Poisson correction is summable. -/
theorem norm_hardCorePoissonCorrectionCoeff_summable_of_norm_le_one
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun m : ℕ => ‖hardCorePoissonCorrectionCoeff z m‖) := by
  have htail :=
    hardCorePoissonCorrectionTailTerm_summable
      (norm_nonneg z) hz
  have hshift :
      Summable
        (fun m : ℕ =>
          ‖hardCorePoissonCorrectionCoeff z (m + 2)‖) := by
    simpa only [hardCorePoissonCorrectionTailTerm,
      norm_hardCorePoissonCorrectionCoeff_add_two] using htail
  exact (summable_nat_add_iff 2).mp hshift

/-- The total absolute coefficient variation is exactly the already-defined
local correction variation. -/
theorem tsum_norm_hardCorePoissonCorrectionCoeff_eq_localVariation
    {q : ℕ} (hq : 4 ≤ q) :
    (∑' m : ℕ,
      ‖hardCorePoissonCorrectionCoeff
        (criticalLiFrequencyWeight q) m‖) =
      criticalLiLocalCorrectionVariation q := by
  let z := criticalLiFrequencyWeight q
  have hz : ‖z‖ ≤ 1 := by
    dsimp [z]
    exact norm_criticalLiFrequencyWeight_le_one hq
  have hs :
      Summable (fun m : ℕ =>
        ‖hardCorePoissonCorrectionCoeff z m‖) :=
    norm_hardCorePoissonCorrectionCoeff_summable_of_norm_le_one hz
  have hhead :
      (∑ m ∈ Finset.range 2,
        ‖hardCorePoissonCorrectionCoeff z m‖) = 1 := by
    norm_num [Finset.sum_range_succ,
      hardCorePoissonCorrectionCoeff]
  have htail :
      (∑' m : ℕ,
        ‖hardCorePoissonCorrectionCoeff z (m + 2)‖) =
      ∑' m : ℕ,
        hardCorePoissonCorrectionTailTerm ‖z‖ m := by
    apply tsum_congr
    intro m
    simpa [hardCorePoissonCorrectionTailTerm] using
      (norm_hardCorePoissonCorrectionCoeff_add_two z m)
  calc
    (∑' m : ℕ, ‖hardCorePoissonCorrectionCoeff z m‖) =
        (∑ m ∈ Finset.range 2,
          ‖hardCorePoissonCorrectionCoeff z m‖) +
          ∑' m : ℕ,
            ‖hardCorePoissonCorrectionCoeff z (m + 2)‖ :=
      (hs.sum_add_tsum_nat_add 2).symm
    _ = 1 + ∑' m : ℕ,
          hardCorePoissonCorrectionTailTerm ‖z‖ m := by
          rw [hhead, htail]
    _ = criticalLiLocalCorrectionVariation q := by
          rfl

/-- **Arithmetic local correction variation bound.**
After the exact sparse-power reindexing, the n^(-1/2)-weighted arithmetic
variation of one Li hard-core/Poisson correction factor is bounded by the
same local coefficient variation already controlled quadratically above. -/
theorem criticalWeightedVariation_liCorrectionFactor_le_localVariation
    {q : ℕ} (hq : 4 ≤ q) (X : ℕ) :
    criticalWeightedVariation
        (fun n =>
          arithmeticHardCorePoissonCorrectionFactor
            (primeSievePNTDensity q) (by omega : 1 < q) n) X ≤
      criticalLiLocalCorrectionVariation q := by
  have hq1 : 1 ≤ q := by omega
  have hz :
      ‖criticalLiFrequencyWeight q‖ ≤ 1 :=
    norm_criticalLiFrequencyWeight_le_one hq
  have hs :
      Summable (fun m : ℕ =>
        ‖hardCorePoissonCorrectionCoeff
          (criticalLiFrequencyWeight q) m‖) :=
    norm_hardCorePoissonCorrectionCoeff_summable_of_norm_le_one hz
  rw [criticalWeightedVariation_hardCorePoissonCorrectionFactor_eq
    (q := q) (by omega : 1 < q)]
  calc
    (∑ m ∈ liCorrectionExponentSet q X,
        ‖hardCorePoissonCorrectionCoeff
            (primeSievePNTDensity q) m‖ /
          Real.sqrt ((q ^ m : ℕ) : ℝ))
        =
      ∑ m ∈ liCorrectionExponentSet q X,
        ‖hardCorePoissonCorrectionCoeff
          (criticalLiFrequencyWeight q) m‖ := by
          apply Finset.sum_congr rfl
          intro m hm
          simpa [criticalLiFrequencyWeight] using
            (norm_hardCorePoissonCorrectionCoeff_div_sqrt_pow_eq
              (q := q) hq1 (primeSievePNTDensity q) m)
    _ ≤ ∑' m : ℕ,
        ‖hardCorePoissonCorrectionCoeff
          (criticalLiFrequencyWeight q) m‖ :=
      hs.sum_le_tsum (liCorrectionExponentSet q X)
        (fun m hm => norm_nonneg _)
    _ = criticalLiLocalCorrectionVariation q :=
      tsum_norm_hardCorePoissonCorrectionCoeff_eq_localVariation hq

/-- **Arithmetic local correction variation at every Li site.**
The q=2 exact cancellation and q=3 unit-ball bound remove the last exceptional
range from the raw Li correction estimate.  The critical denominator in
`V_X` is transferred exactly to the coefficient before the quadratic
majorant is applied. -/
theorem criticalWeightedVariation_liCorrectionFactor_le_localVariation_of_two_le
    {q : ℕ} (hq : 2 ≤ q) (X : ℕ) :
    criticalWeightedVariation
        (fun n =>
          arithmeticHardCorePoissonCorrectionFactor
            (primeSievePNTDensity q) (by omega : 1 < q) n) X ≤
      criticalLiLocalCorrectionVariation q := by
  have hq1 : 1 ≤ q := by omega
  have hz :
      ‖criticalLiFrequencyWeight q‖ ≤ 1 :=
    norm_criticalLiFrequencyWeight_le_one_of_two_le hq
  have hs :=
    hardCorePoissonCorrectionVariationTerm_summable
      (criticalLiFrequencyWeight q) hz
  rw [criticalWeightedVariation_hardCorePoissonCorrectionFactor_eq
    (q := q) (by omega : 1 < q)]
  calc
    (∑ m ∈ liCorrectionExponentSet q X,
        ‖hardCorePoissonCorrectionCoeff
            (primeSievePNTDensity q) m‖ /
          Real.sqrt ((q ^ m : ℕ) : ℝ))
        =
      ∑ m ∈ liCorrectionExponentSet q X,
        hardCorePoissonCorrectionVariationTerm
          (criticalLiFrequencyWeight q) m := by
          apply Finset.sum_congr rfl
          intro m hm
          calc
            ‖hardCorePoissonCorrectionCoeff
                (primeSievePNTDensity q) m‖ /
              Real.sqrt ((q ^ m : ℕ) : ℝ)
                =
              ‖hardCorePoissonCorrectionCoeff
                (criticalLiFrequencyWeight q) m‖ := by
                  simpa [criticalLiFrequencyWeight] using
                    (norm_hardCorePoissonCorrectionCoeff_div_sqrt_pow_eq
                      (q := q) hq1 (primeSievePNTDensity q) m)
            _ = hardCorePoissonCorrectionVariationTerm
                  (criticalLiFrequencyWeight q) m :=
              norm_hardCorePoissonCorrectionCoeff_eq_variationTerm _ _
    _ ≤ ∑' m : ℕ,
          hardCorePoissonCorrectionVariationTerm
            (criticalLiFrequencyWeight q) m := by
          exact hs.sum_le_tsum
            (liCorrectionExponentSet q X)
            (fun m hm =>
              hardCorePoissonCorrectionVariationTerm_nonneg
                (criticalLiFrequencyWeight q) m)
    _ = criticalLiLocalCorrectionVariation q := by
          rw [tsum_hardCorePoissonCorrectionVariationTerm_eq
            (criticalLiFrequencyWeight q) hz]
          rfl

/-- Finite product of the quadratic correction factors over sites
`2,...,k+1`, ordered exactly like `arithmeticHardCoreProduct`. -/
def arithmeticHardCorePoissonCorrectionProduct
    (w : ℕ → ℂ) : ℕ → ArithmeticFunction ℂ
  | 0 => 1
  | k + 1 =>
      arithmeticHardCorePoissonCorrectionFactor
          (w (k + 2)) (q := k + 2) (by omega) *
        arithmeticHardCorePoissonCorrectionProduct w k

/-- Finite product of the corresponding Poisson factors. -/
def arithmeticPoissonProduct
    (w : ℕ → ℂ) : ℕ → ArithmeticFunction ℂ
  | 0 => 1
  | k + 1 =>
      arithmeticPoissonLocalFactor
          (w (k + 2)) (q := k + 2) (by omega) *
        arithmeticPoissonProduct w k

/-- **Exact finite global hard-core/Poisson factorization.**
The complete finite hard-core Euler coefficient product is literally the
quadratic correction product convolved with the Poisson product. -/
theorem arithmeticHardCoreProduct_eq_correctionProduct_mul_poissonProduct
    (w : ℕ → ℂ) (k : ℕ) :
    arithmeticHardCoreProduct w k =
      arithmeticHardCorePoissonCorrectionProduct w k *
        arithmeticPoissonProduct w k := by
  induction k with
  | zero =>
      simp [arithmeticHardCoreProduct,
        arithmeticHardCorePoissonCorrectionProduct,
        arithmeticPoissonProduct]
  | succ k ih =>
      rw [arithmeticHardCoreProduct,
        arithmeticHardCorePoissonCorrectionProduct,
        arithmeticPoissonProduct,
        arithmeticHardCoreLocalFactor_eq_correction_mul_poisson
          (q := k + 2) (by omega : 1 < k + 2),
        ih]
      ac_rfl


/-! ## Stabilized hard-core/Poisson kernels -/

/-- At a pure power of its site, the arithmetic Poisson factor is the
corresponding exponential coefficient. -/
theorem arithmeticPoissonLocalFactor_apply_pow
    {q : ℕ} (hq : 1 < q) (a : ℂ) (m : ℕ) :
    arithmeticPoissonLocalFactor a hq (q ^ m) =
      (-a) ^ m / (Nat.factorial m : ℂ) := by
  unfold arithmeticPoissonLocalFactor poissonExponentialSeries
  rw [liArithmeticOfPowerSeries_apply_pow hq,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [div_eq_mul_inv]

/-- Away from powers of its site, one arithmetic Poisson factor vanishes. -/
theorem arithmeticPoissonLocalFactor_apply_eq_zero_of_not_pow
    {q n : ℕ} (hq : 1 < q) (a : ℂ)
    (hn : ¬ ∃ m : ℕ, q ^ m = n) :
    arithmeticPoissonLocalFactor a hq n = 0 := by
  unfold arithmeticPoissonLocalFactor
  rw [liArithmeticOfPowerSeries_apply hq,
    Function.extend_apply' _ _ _ hn, Pi.zero_apply]

/-- Pointwise critical rescaling of an arithmetic coefficient sequence. -/
def criticalScaleArithmetic (f : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ :=
  ⟨fun n => criticalSqrtWeight n * f n, by
    simp [criticalSqrtWeight]⟩

/-- Complete multiplicativity of the critical weight makes pointwise critical
rescaling a homomorphism for Dirichlet convolution. -/
theorem criticalScaleArithmetic_mul
    (f g : ArithmeticFunction ℂ) :
    criticalScaleArithmetic (f * g) =
      criticalScaleArithmetic f * criticalScaleArithmetic g := by
  ext n
  change criticalSqrtWeight n * (f * g) n =
    (criticalScaleArithmetic f * criticalScaleArithmetic g) n
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  change criticalSqrtWeight n *
      (∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2) =
    ∑ p ∈ n.divisorsAntidiagonal,
      (criticalSqrtWeight p.1 * f p.1) *
        (criticalSqrtWeight p.2 * g p.2)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.mem_divisorsAntidiagonal] at hp
  rcases hp with ⟨hprod, _⟩
  rw [← hprod, criticalSqrtWeight_mul]
  ring

/-- Critical rescaling of one local Poisson factor simply rescales its owner
mass by q^(-1/2). -/
theorem criticalScaleArithmetic_poissonLocalFactor
    {q : ℕ} (hq : 1 < q) (a : ℂ) :
    criticalScaleArithmetic (arithmeticPoissonLocalFactor a hq) =
      arithmeticPoissonLocalFactor
        (a * criticalSqrtWeight q) hq := by
  ext n
  by_cases hp : ∃ m : ℕ, q ^ m = n
  · rcases hp with ⟨m, rfl⟩
    change criticalSqrtWeight (q ^ m) *
        arithmeticPoissonLocalFactor a hq (q ^ m) =
      arithmeticPoissonLocalFactor
        (a * criticalSqrtWeight q) hq (q ^ m)
    rw [arithmeticPoissonLocalFactor_apply_pow,
      arithmeticPoissonLocalFactor_apply_pow,
      criticalSqrtWeight_pow]
    rw [show -(a * criticalSqrtWeight q) =
      (-a) * criticalSqrtWeight q by ring, mul_pow]
    ring
  · change criticalSqrtWeight n *
        arithmeticPoissonLocalFactor a hq n =
      arithmeticPoissonLocalFactor
        (a * criticalSqrtWeight q) hq n
    rw [arithmeticPoissonLocalFactor_apply_eq_zero_of_not_pow hq a hp,
      arithmeticPoissonLocalFactor_apply_eq_zero_of_not_pow
        hq (a * criticalSqrtWeight q) hp]
    ring

/-- Critical rescaling passes through the complete finite Poisson product and
replaces each owner w_q by the transformed owner w_q/sqrt(q). -/
theorem criticalScaleArithmetic_poissonProduct
    (w : ℕ → ℂ) (k : ℕ) :
    criticalScaleArithmetic (arithmeticPoissonProduct w k) =
      arithmeticPoissonProduct
        (fun q => w q * criticalSqrtWeight q) k := by
  induction k with
  | zero =>
      ext n
      by_cases hn : n = 1
      · subst n
        simp [criticalScaleArithmetic, arithmeticPoissonProduct,
          criticalSqrtWeight]
      · simp [criticalScaleArithmetic, arithmeticPoissonProduct,
          criticalSqrtWeight, hn]
  | succ k ih =>
      rw [arithmeticPoissonProduct, criticalScaleArithmetic_mul,
        criticalScaleArithmetic_poissonLocalFactor, ih]
      rfl

private theorem pow_site_not_eq_of_pos_lt
    {q n : ℕ} (hq : 1 < q) (hnq : n < q)
    (hn1 : n ≠ 1) :
    ¬ ∃ m : ℕ, q ^ m = n := by
  rintro ⟨m, hm⟩
  cases m with
  | zero =>
      simp only [pow_zero] at hm
      exact hn1 hm.symm
  | succ m =>
      have hqle : q ≤ q ^ (m + 1) := by
        calc
          q = q * 1 := by simp
          _ ≤ q * q ^ m := by
            exact Nat.mul_le_mul_left q
              (Nat.one_le_pow m q (by omega))
          _ = q ^ (m + 1) := by
            simp [pow_succ, Nat.mul_comm]
      rw [hm] at hqle
      omega

private theorem arithmeticHardCorePoissonCorrectionFactor_apply_of_pos_lt
    {q n : ℕ} (hq : 1 < q) (hn : 1 ≤ n) (hnq : n < q)
    (a : ℂ) :
    arithmeticHardCorePoissonCorrectionFactor a hq n =
      if n = 1 then 1 else 0 := by
  by_cases hn1 : n = 1
  · subst n
    simpa using
      (arithmeticHardCorePoissonCorrectionFactor_apply_pow hq a 0)
  · have hnot := pow_site_not_eq_of_pos_lt hq hnq hn1
    rw [arithmeticHardCorePoissonCorrectionFactor_apply_eq_zero_of_not_pow
      hq a hnot]
    simp [hn1]

private theorem arithmeticPoissonLocalFactor_apply_of_pos_lt
    {q n : ℕ} (hq : 1 < q) (hn : 1 ≤ n) (hnq : n < q)
    (a : ℂ) :
    arithmeticPoissonLocalFactor a hq n =
      if n = 1 then 1 else 0 := by
  by_cases hn1 : n = 1
  · subst n
    simpa using (arithmeticPoissonLocalFactor_apply_pow hq a 0)
  · have hnot := pow_site_not_eq_of_pos_lt hq hnq hn1
    rw [arithmeticPoissonLocalFactor_apply_eq_zero_of_not_pow hq a hnot]
    simp [hn1]

private theorem arithmeticCoefficientCumulative_correctionFactor_mul_of_lt
    {q Y : ℕ} (hq : 1 < q) (hY : 1 ≤ Y) (hYq : Y < q)
    (a : ℂ) (f : ArithmeticFunction ℂ) :
    arithmeticCoefficientCumulative
        (arithmeticHardCorePoissonCorrectionFactor a hq * f) Y =
      arithmeticCoefficientCumulative f Y := by
  rw [arithmeticCoefficientCumulative_mul]
  rw [Finset.sum_eq_single 1]
  · have hone :=
      arithmeticHardCorePoissonCorrectionFactor_apply_of_pos_lt
        hq (by omega : (1 : ℕ) ≤ 1) (by omega : (1 : ℕ) < q) a
    simp at hone
    rw [hone]
    simp
  · intro n hn hn1
    rcases Finset.mem_Icc.mp hn with ⟨hnpos, hnY⟩
    have hnq : n < q := hnY.trans_lt hYq
    rw [arithmeticHardCorePoissonCorrectionFactor_apply_of_pos_lt
      hq hnpos hnq a]
    simp [hn1]
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨le_rfl, hY⟩)).elim

private theorem arithmeticCoefficientCumulative_poissonFactor_mul_of_lt
    {q Y : ℕ} (hq : 1 < q) (hY : 1 ≤ Y) (hYq : Y < q)
    (a : ℂ) (f : ArithmeticFunction ℂ) :
    arithmeticCoefficientCumulative
        (arithmeticPoissonLocalFactor a hq * f) Y =
      arithmeticCoefficientCumulative f Y := by
  rw [arithmeticCoefficientCumulative_mul]
  rw [Finset.sum_eq_single 1]
  · have hone :=
      arithmeticPoissonLocalFactor_apply_of_pos_lt
        hq (by omega : (1 : ℕ) ≤ 1) (by omega : (1 : ℕ) < q) a
    simp at hone
    rw [hone]
    simp
  · intro n hn hn1
    rcases Finset.mem_Icc.mp hn with ⟨hnpos, hnY⟩
    have hnq : n < q := hnY.trans_lt hYq
    rw [arithmeticPoissonLocalFactor_apply_of_pos_lt hq hnpos hnq a]
    simp [hn1]
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨le_rfl, hY⟩)).elim

private theorem
    arithmeticHardCorePoissonCorrectionProduct_cumulative_natAdd_stable
    (w : ℕ → ℂ) (Y g : ℕ) (hY : 1 ≤ Y) :
    arithmeticCoefficientCumulative
        (arithmeticHardCorePoissonCorrectionProduct w ((Y - 1) + g)) Y =
      arithmeticCoefficientCumulative
        (arithmeticHardCorePoissonCorrectionProduct w (Y - 1)) Y := by
  induction g with
  | zero =>
      simp
  | succ g ih =>
      have hq : 1 < (Y - 1) + g + 2 := by omega
      have hYq : Y < (Y - 1) + g + 2 := by omega
      rw [show (Y - 1) + (g + 1) = ((Y - 1) + g) + 1 by omega,
        arithmeticHardCorePoissonCorrectionProduct,
        arithmeticCoefficientCumulative_correctionFactor_mul_of_lt
          hq hY hYq]
      exact ih

private theorem arithmeticPoissonProduct_cumulative_natAdd_stable
    (w : ℕ → ℂ) (Y g : ℕ) (hY : 1 ≤ Y) :
    arithmeticCoefficientCumulative
        (arithmeticPoissonProduct w ((Y - 1) + g)) Y =
      arithmeticCoefficientCumulative
        (arithmeticPoissonProduct w (Y - 1)) Y := by
  induction g with
  | zero =>
      simp
  | succ g ih =>
      have hq : 1 < (Y - 1) + g + 2 := by omega
      have hYq : Y < (Y - 1) + g + 2 := by omega
      rw [show (Y - 1) + (g + 1) = ((Y - 1) + g) + 1 by omega,
        arithmeticPoissonProduct,
        arithmeticCoefficientCumulative_poissonFactor_mul_of_lt
          hq hY hYq]
      exact ih

private theorem
    arithmeticHardCorePoissonCorrectionProduct_cumulative_stable
    (w : ℕ → ℂ) {Y X : ℕ} (hY : 1 ≤ Y) (hYX : Y ≤ X) :
    arithmeticCoefficientCumulative
        (arithmeticHardCorePoissonCorrectionProduct w (X - 1)) Y =
      arithmeticCoefficientCumulative
        (arithmeticHardCorePoissonCorrectionProduct w (Y - 1)) Y := by
  have hidx : X - 1 = (Y - 1) + (X - Y) := by omega
  rw [hidx]
  exact
    arithmeticHardCorePoissonCorrectionProduct_cumulative_natAdd_stable
      w Y (X - Y) hY

private theorem arithmeticPoissonProduct_cumulative_stable
    (w : ℕ → ℂ) {Y X : ℕ} (hY : 1 ≤ Y) (hYX : Y ≤ X) :
    arithmeticCoefficientCumulative
        (arithmeticPoissonProduct w (X - 1)) Y =
      arithmeticCoefficientCumulative
        (arithmeticPoissonProduct w (Y - 1)) Y := by
  have hidx : X - 1 = (Y - 1) + (X - Y) := by omega
  rw [hidx]
  exact arithmeticPoissonProduct_cumulative_natAdd_stable
    w Y (X - Y) hY

private theorem arithmeticFunction_apply_eq_cumulative_sub
    (f : ArithmeticFunction ℂ) {n : ℕ} (hn : 1 ≤ n) :
    f n =
      arithmeticCoefficientCumulative f n -
        arithmeticCoefficientCumulative f (n - 1) := by
  have hsum :
      arithmeticCoefficientCumulative f n =
        arithmeticCoefficientCumulative f (n - 1) + f n := by
    unfold arithmeticCoefficientCumulative
    have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
    calc
      (∑ i ∈ Finset.Icc 1 n, f i) =
          ∑ i ∈ Finset.Icc 1 (n - 1 + 1), f i := by
            rw [hpred]
      _ = (∑ i ∈ Finset.Icc 1 (n - 1), f i) + f (n - 1 + 1) := by
            rw [Finset.sum_Icc_succ_top (by omega)]
      _ = (∑ i ∈ Finset.Icc 1 (n - 1), f i) + f n := by
            rw [hpred]
  rw [hsum]
  ring

private theorem
    arithmeticHardCorePoissonCorrectionProduct_apply_stable
    (w : ℕ → ℂ) {n X : ℕ} (hn : 1 ≤ n) (hnX : n ≤ X) :
    arithmeticHardCorePoissonCorrectionProduct w (X - 1) n =
      arithmeticHardCorePoissonCorrectionProduct w (n - 1) n := by
  by_cases hn1 : n = 1
  · subst n
    have hcum :=
      arithmeticHardCorePoissonCorrectionProduct_cumulative_stable
        w (Y := 1) (X := X) (by omega) hnX
    simpa [arithmeticCoefficientCumulative] using hcum
  · have hnm1 : 1 ≤ n - 1 := by omega
    rw [arithmeticFunction_apply_eq_cumulative_sub _ hn,
      arithmeticFunction_apply_eq_cumulative_sub _ hn]
    rw [arithmeticHardCorePoissonCorrectionProduct_cumulative_stable
      w hn hnX]
    rw [arithmeticHardCorePoissonCorrectionProduct_cumulative_stable
      w hnm1 (by omega : n - 1 ≤ X)]
    rw [arithmeticHardCorePoissonCorrectionProduct_cumulative_stable
      w hnm1 (by omega : n - 1 ≤ n)]


private theorem arithmeticPoissonProduct_apply_stable
    (w : ℕ → ℂ) {n X : ℕ} (hn : 1 ≤ n) (hnX : n ≤ X) :
    arithmeticPoissonProduct w (X - 1) n =
      arithmeticPoissonProduct w (n - 1) n := by
  by_cases hn1 : n = 1
  · subst n
    have hcum :=
      arithmeticPoissonProduct_cumulative_stable
        w (Y := 1) (X := X) (by omega) hnX
    simpa [arithmeticCoefficientCumulative] using hcum
  · have hnm1 : 1 ≤ n - 1 := by omega
    rw [arithmeticFunction_apply_eq_cumulative_sub _ hn,
      arithmeticFunction_apply_eq_cumulative_sub _ hn]
    rw [arithmeticPoissonProduct_cumulative_stable w hn hnX]
    rw [arithmeticPoissonProduct_cumulative_stable
      w hnm1 (by omega : n - 1 ≤ X)]
    rw [arithmeticPoissonProduct_cumulative_stable
      w hnm1 (by omega : n - 1 ≤ n)]



/-- Absolute coefficient of the genuinely quadratic-and-higher part of one
Poisson exponential, indexed from degree two. -/
def poissonQuadraticTailTerm (a : ℝ) (m : ℕ) : ℝ :=
  a ^ (m + 2) / (Nat.factorial (m + 2) : ℝ)

theorem poissonQuadraticTailTerm_nonneg
    {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    0 ≤ poissonQuadraticTailTerm a m := by
  unfold poissonQuadraticTailTerm
  positivity

/-- The pure Poisson degree-two tail is pointwise dominated by the already
certified hard-core/Poisson correction tail. -/
theorem poissonQuadraticTailTerm_le_hardCorePoissonCorrectionTailTerm
    {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    poissonQuadraticTailTerm a m ≤
      hardCorePoissonCorrectionTailTerm a m := by
  unfold poissonQuadraticTailTerm hardCorePoissonCorrectionTailTerm
  have hbase :
      0 ≤ a ^ (m + 2) / (Nat.factorial (m + 2) : ℝ) := by
    positivity
  have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ m + 1 by omega)
  calc
    a ^ (m + 2) / (Nat.factorial (m + 2) : ℝ) =
        1 * (a ^ (m + 2) / (Nat.factorial (m + 2) : ℝ)) := by ring
    _ ≤ ((m + 1 : ℕ) : ℝ) *
        (a ^ (m + 2) / (Nat.factorial (m + 2) : ℝ)) :=
      mul_le_mul_of_nonneg_right hm hbase
    _ = ((m + 1 : ℕ) : ℝ) * a ^ (m + 2) /
        (Nat.factorial (m + 2) : ℝ) := by ring

theorem poissonQuadraticTailTerm_summable
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Summable (poissonQuadraticTailTerm a) := by
  exact Summable.of_nonneg_of_le
    (fun m => poissonQuadraticTailTerm_nonneg ha0 m)
    (fun m => poissonQuadraticTailTerm_le_hardCorePoissonCorrectionTailTerm
      ha0 m)
    (hardCorePoissonCorrectionTailTerm_summable ha0 ha1)

/-- The complete absolute Poisson tail beyond degrees zero and one is
quadratic in the local owner mass.  The constant is deliberately inherited
from the already-green correction-tail estimate. -/
theorem tsum_poissonQuadraticTailTerm_le_three_sq
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑' m : ℕ, poissonQuadraticTailTerm a m) ≤ 3 * a ^ 2 := by
  have hs := poissonQuadraticTailTerm_summable ha0 ha1
  have hc := hardCorePoissonCorrectionTailTerm_summable ha0 ha1
  calc
    (∑' m : ℕ, poissonQuadraticTailTerm a m)
        ≤ ∑' m : ℕ, hardCorePoissonCorrectionTailTerm a m := by
          exact Summable.tsum_le_tsum
            (fun m =>
              poissonQuadraticTailTerm_le_hardCorePoissonCorrectionTailTerm
                ha0 m)
            hs hc
    _ ≤ 3 * a ^ 2 :=
      tsum_hardCorePoissonCorrectionTailTerm_le_three_sq ha0 ha1

/-- Complex norm form of one Poisson coefficient in degree m+2. -/
theorem norm_poissonCoeff_add_two_eq_quadraticTail
    (z : ℂ) (m : ℕ) :
    ‖(-z) ^ (m + 2) / (Nat.factorial (m + 2) : ℂ)‖ =
      poissonQuadraticTailTerm ‖z‖ m := by
  unfold poissonQuadraticTailTerm
  rw [norm_div, norm_pow, norm_neg, Complex.norm_natCast]

/-- On the unit ball, the full complex Poisson tail from degree two onward
has absolute mass at most three times the squared owner norm. -/
theorem tsum_norm_poissonCoeff_add_two_le_three_sq
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∑' m : ℕ,
        ‖(-z) ^ (m + 2) / (Nat.factorial (m + 2) : ℂ)‖) ≤
      3 * ‖z‖ ^ 2 := by
  have h0 : 0 ≤ ‖z‖ := norm_nonneg z
  calc
    (∑' m : ℕ,
        ‖(-z) ^ (m + 2) / (Nat.factorial (m + 2) : ℂ)‖) =
      ∑' m : ℕ, poissonQuadraticTailTerm ‖z‖ m := by
        apply tsum_congr
        intro m
        exact norm_poissonCoeff_add_two_eq_quadraticTail z m
    _ ≤ 3 * ‖z‖ ^ 2 :=
      tsum_poissonQuadraticTailTerm_le_three_sq h0 hz

/-- After the critical square-root rescaling at site q, the complete
quadratic Poisson tail is paid by exactly the local collision currency
‖w_q‖²/q, up to the universal factor three. -/
theorem tsum_norm_poissonCoeff_critical_add_two_le_collision
    {q : ℕ} (hq : 1 ≤ q) (a : ℂ)
    (hz : ‖a * criticalSqrtWeight q‖ ≤ 1) :
    (∑' m : ℕ,
        ‖(-a) ^ (m + 2) / (Nat.factorial (m + 2) : ℂ)‖ /
          Real.sqrt ((q ^ (m + 2) : ℕ) : ℝ)) ≤
      3 * (‖a‖ ^ 2 / (q : ℝ)) := by
  have hterm :
      ∀ m : ℕ,
        ‖(-a) ^ (m + 2) / (Nat.factorial (m + 2) : ℂ)‖ /
            Real.sqrt ((q ^ (m + 2) : ℕ) : ℝ) =
          ‖(-(a * criticalSqrtWeight q)) ^ (m + 2) /
            (Nat.factorial (m + 2) : ℂ)‖ := by
    intro m
    have hqpow : 1 ≤ q ^ (m + 2) :=
      Nat.one_le_pow (m + 2) q hq
    have hweight :
        (Real.sqrt ((q ^ (m + 2) : ℕ) : ℝ))⁻¹ =
          ‖criticalSqrtWeight q‖ ^ (m + 2) := by
      calc
        (Real.sqrt ((q ^ (m + 2) : ℕ) : ℝ))⁻¹ =
            ‖criticalSqrtWeight (q ^ (m + 2))‖ := by
              symm
              simpa [one_div] using
                (norm_criticalSqrtWeight_eq_inv_sqrt
                  (q := q ^ (m + 2)) hqpow)
        _ = ‖criticalSqrtWeight q ^ (m + 2)‖ := by
              rw [criticalSqrtWeight_pow]
        _ = ‖criticalSqrtWeight q‖ ^ (m + 2) := by
              rw [norm_pow]
    rw [div_eq_mul_inv, hweight, norm_div, norm_pow, norm_neg,
      Complex.norm_natCast]
    rw [norm_div, norm_pow, norm_neg, norm_mul, Complex.norm_natCast]
    ring
  calc
    (∑' m : ℕ,
        ‖(-a) ^ (m + 2) / (Nat.factorial (m + 2) : ℂ)‖ /
          Real.sqrt ((q ^ (m + 2) : ℕ) : ℝ)) =
      ∑' m : ℕ,
        ‖(-(a * criticalSqrtWeight q)) ^ (m + 2) /
          (Nat.factorial (m + 2) : ℂ)‖ := by
        apply tsum_congr
        exact hterm
    _ ≤ 3 * ‖a * criticalSqrtWeight q‖ ^ 2 :=
      tsum_norm_poissonCoeff_add_two_le_three_sq hz
    _ = 3 * (‖a‖ ^ 2 / (q : ℝ)) := by
      rw [norm_mul, mul_pow, norm_criticalSqrtWeight_sq]
      ring

/-- For the exact Li site weight, the local quadratic Poisson tail is paid by
the already summable transformed collision owner. -/
theorem tsum_norm_exactLiPoissonCoeff_critical_add_two_le_collision
    {q : ℕ} (hq : 2 ≤ q) :
    (∑' m : ℕ,
        ‖(-primeSievePNTDensity q) ^ (m + 2) /
            (Nat.factorial (m + 2) : ℂ)‖ /
          Real.sqrt ((q ^ (m + 2) : ℕ) : ℝ)) ≤
      3 * ‖criticalLiFrequencyWeight q‖ ^ 2 := by
  have hz : ‖criticalLiFrequencyWeight q‖ ≤ 1 := by
    rcases Nat.eq_or_lt_of_le hq with rfl | hqgt
    · rw [criticalLiFrequencyWeight_two_eq_zero]
      simp
    · have hq3 : 3 ≤ q := by omega
      by_cases h3 : q = 3
      · subst q
        exact norm_criticalLiFrequencyWeight_three_le_one
      · exact norm_criticalLiFrequencyWeight_le_one (by omega)
  have h :=
    tsum_norm_poissonCoeff_critical_add_two_le_collision
      (q := q) (by omega : 1 ≤ q) (primeSievePNTDensity q) hz
  simpa [norm_criticalLiFrequencyWeight_sq] using h

/-- **Exact one-site Poisson cumulative recurrence.**
Multiplying a coefficient sequence by the Poisson exponential at site `q`
produces the finite signed power expansion over exactly those powers `q^m`
visible below the endpoint. -/
theorem arithmeticCoefficientCumulative_poissonLocalFactor_mul_eq
    {q : ℕ} (hq : 1 < q) (a : ℂ)
    (f : ArithmeticFunction ℂ) (X : ℕ) :
    arithmeticCoefficientCumulative
        (arithmeticPoissonLocalFactor a hq * f) X =
      ∑ m ∈ liCorrectionExponentSet q X,
        ((-a) ^ m / (Nat.factorial m : ℂ)) *
          arithmeticCoefficientCumulative f (X / q ^ m) := by
  rw [arithmeticCoefficientCumulative_mul]
  let E := liCorrectionExponentSet q X
  have hinj : Function.Injective (fun m : ℕ => q ^ m) :=
    Nat.pow_right_injective hq
  have hsub :
      E.image (fun m : ℕ => q ^ m) ⊆ Finset.Icc 1 X := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨m, hmE, rfl⟩
    have hmdata := Finset.mem_filter.mp hmE
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_pow m q (by omega), hmdata.2⟩
  calc
    (∑ n ∈ Finset.Icc 1 X,
        arithmeticPoissonLocalFactor a hq n *
          arithmeticCoefficientCumulative f (X / n))
        =
      ∑ n ∈ E.image (fun m : ℕ => q ^ m),
        arithmeticPoissonLocalFactor a hq n *
          arithmeticCoefficientCumulative f (X / n) := by
          symm
          apply Finset.sum_subset hsub
          intro n hnI hnNot
          have hnNotPow : ¬ ∃ m : ℕ, q ^ m = n := by
            rintro ⟨m, hm⟩
            have hnX := (Finset.mem_Icc.mp hnI).2
            have hmX : q ^ m ≤ X := hm.trans_le hnX
            have hmle : m ≤ X :=
              li_exponent_le_endpoint_of_pow_le hq hmX
            have hmE : m ∈ E := by
              dsimp [E, liCorrectionExponentSet]
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hmle), hmX⟩
            apply hnNot
            exact Finset.mem_image.mpr ⟨m, hmE, hm⟩
          rw [arithmeticPoissonLocalFactor_apply_eq_zero_of_not_pow
            hq a hnNotPow, zero_mul]
    _ = ∑ m ∈ E,
        ((-a) ^ m / (Nat.factorial m : ℂ)) *
          arithmeticCoefficientCumulative f (X / q ^ m) := by
          rw [Finset.sum_image]
          · apply Finset.sum_congr rfl
            intro m hm
            rw [arithmeticPoissonLocalFactor_apply_pow]
          · intro m _hm n _hn hmn
            exact hinj hmn
    _ = _ := by rfl

/-- Successor-cutoff form of the exact Poisson recurrence.  The new site is
`q = k+2`; the old state is the cumulative of the cutoff-`k` product. -/
theorem arithmeticPoissonProduct_cumulative_succ_eq
    (w : ℕ → ℂ) (k X : ℕ) :
    arithmeticCoefficientCumulative
        (arithmeticPoissonProduct w (k + 1)) X =
      ∑ m ∈ liCorrectionExponentSet (k + 2) X,
        ((-w (k + 2)) ^ m / (Nat.factorial m : ℂ)) *
          arithmeticCoefficientCumulative
            (arithmeticPoissonProduct w k) (X / (k + 2) ^ m) := by
  rw [arithmeticPoissonProduct]
  exact arithmeticCoefficientCumulative_poissonLocalFactor_mul_eq
    (q := k + 2) (by omega) (w (k + 2))
      (arithmeticPoissonProduct w k) X

/-- Exponents at least two that remain visible in one finite Poisson site. -/
private def liPoissonQuadraticExponentSet (q X : ℕ) : Finset ℕ :=
  (liCorrectionExponentSet q X).filter (fun m => 2 ≤ m)

/-- **Linear/quadratic split of one Poisson site.**
Once the new site q=k+2 is visible below X, the exact finite Poisson update is
its degree-zero state, minus the linear fresh-owner child, plus only the
degree-two-and-higher collision tail. -/
theorem arithmeticPoissonProduct_cumulative_succ_eq_linear_add_tail
    (w : ℕ → ℂ) (k X : ℕ) (hqX : k + 2 ≤ X) :
    arithmeticCoefficientCumulative
        (arithmeticPoissonProduct w (k + 1)) X =
      arithmeticCoefficientCumulative (arithmeticPoissonProduct w k) X -
        w (k + 2) *
          arithmeticCoefficientCumulative
            (arithmeticPoissonProduct w k) (X / (k + 2)) +
        ∑ m ∈ liPoissonQuadraticExponentSet (k + 2) X,
          ((-w (k + 2)) ^ m / (Nat.factorial m : ℂ)) *
            arithmeticCoefficientCumulative
              (arithmeticPoissonProduct w k) (X / (k + 2) ^ m) := by
  rw [arithmeticPoissonProduct_cumulative_succ_eq]
  let E := liCorrectionExponentSet (k + 2) X
  let H := liPoissonQuadraticExponentSet (k + 2) X
  have hX1 : 1 ≤ X := by omega
  have h0E : 0 ∈ E := by
    dsimp [E, liCorrectionExponentSet]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), by simpa using hX1⟩
  have h1E : 1 ∈ E := by
    dsimp [E, liCorrectionExponentSet]
    simp [hqX]
  have hsplit : E = insert 0 (insert 1 H) := by
    ext m
    constructor
    · intro hm
      by_cases hm0 : m = 0
      · subst m
        simp
      by_cases hm1 : m = 1
      · subst m
        simp
      have hm2 : 2 ≤ m := by omega
      have hmH : m ∈ H := by
        dsimp [H, liPoissonQuadraticExponentSet]
        exact Finset.mem_filter.mpr ⟨hm, hm2⟩
      simp [hmH, hm0, hm1]
    · intro hm
      simp only [Finset.mem_insert] at hm
      rcases hm with rfl | rfl | hmH
      · exact h0E
      · exact h1E
      · exact (Finset.mem_filter.mp hmH).1
  have h0not : 0 ∉ insert 1 H := by
    simp [H, liPoissonQuadraticExponentSet]
  have h1not : 1 ∉ H := by
    simp [H, liPoissonQuadraticExponentSet]
  change
    (∑ m ∈ E,
        ((-w (k + 2)) ^ m / (Nat.factorial m : ℂ)) *
          arithmeticCoefficientCumulative
            (arithmeticPoissonProduct w k) (X / (k + 2) ^ m)) = _
  rw [hsplit, Finset.sum_insert h0not, Finset.sum_insert h1not]
  simp
  ring

/-- The fixed correction kernel obtained by freezing each coefficient at the
first cutoff at which it can be visible. -/
def exactLiCorrectionKernel (n : ℕ) : ℂ :=
  if 1 ≤ n then
    arithmeticHardCorePoissonCorrectionProduct
      primeSievePNTDensity (n - 1) n
  else 0

/-- Stabilized coefficient of the exact Poissonized Li product. -/
def exactLiPoissonCoefficient (n : ℕ) : ℂ :=
  if 1 ≤ n then
    arithmeticPoissonProduct primeSievePNTDensity (n - 1) n
  else 0

/-- A stabilized Poisson coefficient can be read at any larger visible
cutoff. -/
theorem exactLiPoissonCoefficient_eq_cutoff
    {n X : ℕ} (hn : 1 ≤ n) (hnX : n ≤ X) :
    exactLiPoissonCoefficient n =
      arithmeticPoissonProduct primeSievePNTDensity (X - 1) n := by
  simp only [exactLiPoissonCoefficient, if_pos hn]
  exact
    (arithmeticPoissonProduct_apply_stable
      primeSievePNTDensity hn hnX).symm

/-- The integer cumulative reference of the exact Poissonized Li product. -/
def exactLiPoissonIntegerReference (X : ℕ) : ℂ :=
  if 1 ≤ X then
    arithmeticCoefficientCumulative
      (arithmeticPoissonProduct primeSievePNTDensity (X - 1)) X
  else 1

@[simp] theorem exactLiPoissonIntegerReference_zero :
    exactLiPoissonIntegerReference 0 = 1 := by
  simp [exactLiPoissonIntegerReference]


@[simp] theorem exactLiPoissonIntegerReference_one :
    exactLiPoissonIntegerReference 1 = 1 := by
  simp [exactLiPoissonIntegerReference, arithmeticCoefficientCumulative,
    arithmeticPoissonProduct]

/-- The stabilized coefficient sequence cumulatively reconstructs the exact
Poisson integer reference. -/
theorem exactLiPoissonIntegerReference_eq_coefficientCumulative
    {X : ℕ} (hX : 1 ≤ X) :
    exactLiPoissonIntegerReference X =
      ∑ n ∈ Finset.Icc 1 X, exactLiPoissonCoefficient n := by
  simp only [exactLiPoissonIntegerReference, if_pos hX]
  unfold arithmeticCoefficientCumulative
  apply Finset.sum_congr rfl
  intro n hnmem
  rcases Finset.mem_Icc.mp hnmem with ⟨hn1, hnX⟩
  rw [exactLiPoissonCoefficient_eq_cutoff hn1 hnX]

/-- Critical rescaling of a stabilized Poisson coefficient is exactly the
coefficient of the Poisson product with transformed Li owners. -/
theorem criticalScale_exactLiPoissonCoefficient
    {n : ℕ} (hn : 1 ≤ n) :
    criticalSqrtWeight n * exactLiPoissonCoefficient n =
      arithmeticPoissonProduct criticalLiFrequencyWeight (n - 1) n := by
  have h :=
    congrArg (fun f : ArithmeticFunction ℂ => f n)
      (criticalScaleArithmetic_poissonProduct
        primeSievePNTDensity (n - 1))
  change criticalSqrtWeight n *
      arithmeticPoissonProduct primeSievePNTDensity (n - 1) n =
    arithmeticPoissonProduct
      (fun q => primeSievePNTDensity q * criticalSqrtWeight q)
      (n - 1) n at h
  simpa [exactLiPoissonCoefficient, if_pos hn,
    criticalLiFrequencyWeight] using h

/-- At any larger visible cutoff, the critically rescaled stabilized
coefficient is read from the transformed-owner Poisson product. -/
theorem exactLiPoissonCoefficient_div_sqrt_eq_critical_cutoff
    {n X : ℕ} (hn : 1 ≤ n) (hnX : n ≤ X) :
    exactLiPoissonCoefficient n / (Real.sqrt (n : ℝ) : ℂ) =
      arithmeticPoissonProduct criticalLiFrequencyWeight (X - 1) n := by
  have hscale := criticalScale_exactLiPoissonCoefficient hn
  have hstable :=
    arithmeticPoissonProduct_apply_stable
      criticalLiFrequencyWeight hn hnX
  rw [hstable]
  simpa [criticalSqrtWeight, div_eq_mul_inv, mul_comm] using hscale

/-- The cumulative Poisson reference after the exact critical n^(-1/2)
coefficient transform. -/
def exactLiCriticalPoissonIntegerReference (X : ℕ) : ℂ :=
  if 1 ≤ X then
    arithmeticCoefficientCumulative
      (arithmeticPoissonProduct criticalLiFrequencyWeight (X - 1)) X
  else 1

@[simp] theorem exactLiCriticalPoissonIntegerReference_zero :
    exactLiCriticalPoissonIntegerReference 0 = 1 := by
  simp [exactLiCriticalPoissonIntegerReference]

/-- Raising the Li cutoff above a visible coefficient does not change that
coefficient. -/
theorem exactLiCorrectionKernel_eq_cutoff
    {n X : ℕ} (hn : 1 ≤ n) (hnX : n ≤ X) :
    exactLiCorrectionKernel n =
      arithmeticHardCorePoissonCorrectionProduct
        primeSievePNTDensity (X - 1) n := by
  simp only [exactLiCorrectionKernel, if_pos hn]
  exact
    (arithmeticHardCorePoissonCorrectionProduct_apply_stable
      primeSievePNTDensity hn hnX).symm

/-- Raising the Poisson cutoff above a positive child endpoint leaves its
cumulative reference unchanged. -/
theorem exactLiPoissonIntegerReference_eq_child
    {Y X : ℕ} (hY : 1 ≤ Y) (hYX : Y ≤ X) :
    exactLiPoissonIntegerReference Y =
      arithmeticCoefficientCumulative
        (arithmeticPoissonProduct primeSievePNTDensity (X - 1)) Y := by
  simp only [exactLiPoissonIntegerReference, if_pos hY]
  exact
    (arithmeticPoissonProduct_cumulative_stable
      primeSievePNTDensity hY hYX).symm


/-- Above the artificial zero endpoint, one Poisson-reference increment is
exactly the stabilized Poisson coefficient. -/
theorem exactLiPoissonIntegerReference_sub_pred_eq_coefficient
    {n : ℕ} (hn : 2 ≤ n) :
    exactLiPoissonIntegerReference n -
        exactLiPoissonIntegerReference (n - 1) =
      exactLiPoissonCoefficient n := by
  have hn1 : 1 ≤ n := by omega
  have hnm1 : 1 ≤ n - 1 := by omega
  rw [exactLiPoissonIntegerReference, if_pos hn1]
  rw [exactLiPoissonIntegerReference_eq_child hnm1
    (by omega : n - 1 ≤ n)]
  symm
  simpa [exactLiPoissonCoefficient, if_pos hn1] using
    (arithmeticFunction_apply_eq_cumulative_sub
      (arithmeticPoissonProduct primeSievePNTDensity (n - 1)) hn1)

/-- The first sampled Poisson-reference increment vanishes because both the
zero endpoint and the unit endpoint carry the same unit atom. -/
@[simp] theorem exactLiPoissonIntegerReference_one_sub_zero :
    exactLiPoissonIntegerReference 1 -
        exactLiPoissonIntegerReference 0 = 0 := by
  simp [exactLiPoissonIntegerReference, arithmeticCoefficientCumulative,
    arithmeticPoissonProduct]


/-! ## Generic critical convolution transfer -/

/-- Finite multiplicative convolution at an integer endpoint. -/
def finiteMultiplicativeConvolution
    (h M : ℕ → ℂ) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, h n * M (X / n)

/-- The cumulative Dirichlet-convolution identity in the generic finite
multiplicative-convolution notation consumed by the pure-Li closure. -/
theorem arithmeticCoefficientCumulative_mul_eq_finiteMultiplicativeConvolution
    (f g : ArithmeticFunction ℂ) (X : ℕ) :
    arithmeticCoefficientCumulative (f * g) X =
      finiteMultiplicativeConvolution
        (fun n => f n) (arithmeticCoefficientCumulative g) X := by
  rw [arithmeticCoefficientCumulative_mul]
  rfl

private theorem sum_Icc_divisorsAntidiagonal_eq_sum_div_real
    (F : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2) =
      ∑ a ∈ Finset.Icc 1 N,
        ∑ b ∈ Finset.Icc 1 (N / a), F a b := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N,
        ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2) =
        ∑ z ∈ (Finset.Icc 1 N).sigma
            (fun n => n.divisorsAntidiagonal),
          F z.2.1 z.2.2 :=
      Finset.sum_sigma' (Finset.Icc 1 N)
        (fun n => n.divisorsAntidiagonal)
        (fun _ p => F p.1 p.2)
    _ = ∑ w ∈ (Finset.Icc 1 N).sigma
            (fun a => Finset.Icc 1 (N / a)),
          F w.1 w.2 := by
      refine Finset.sum_nbij'
        (i := fun z => ⟨z.2.1, z.2.2⟩)
        (j := fun w => ⟨w.1 * w.2, (w.1, w.2)⟩)
        ?_ ?_ ?_ ?_ ?_
      · rintro ⟨n, a, b⟩ hz
        rw [Finset.mem_sigma] at hz ⊢
        obtain ⟨hn, hp⟩ := hz
        rw [Finset.mem_Icc] at hn
        rw [Nat.mem_divisorsAntidiagonal] at hp
        obtain ⟨hab, hn0⟩ := hp
        have ha0 : 0 < a := by
          rcases Nat.eq_zero_or_pos a with h | h
          · exfalso
            apply hn0
            rw [← hab, h, Nat.zero_mul]
          · exact h
        have hb0 : 0 < b := by
          rcases Nat.eq_zero_or_pos b with h | h
          · exfalso
            apply hn0
            rw [← hab, h, Nat.mul_zero]
          · exact h
        have habN : a * b ≤ N := by
          rw [hab]
          exact hn.2
        constructor
        · rw [Finset.mem_Icc]
          refine ⟨ha0, ?_⟩
          exact le_trans (Nat.le_mul_of_pos_right a hb0) habN
        · rw [Finset.mem_Icc]
          refine ⟨hb0, ?_⟩
          rw [Nat.le_div_iff_mul_le ha0]
          rw [Nat.mul_comm]
          exact habN
      · rintro ⟨a, b⟩ hw
        rw [Finset.mem_sigma] at hw ⊢
        obtain ⟨ha, hb⟩ := hw
        rw [Finset.mem_Icc] at ha hb
        have habN : a * b ≤ N := by
          have h := (Nat.le_div_iff_mul_le ha.1).1 hb.2
          rw [Nat.mul_comm] at h
          exact h
        have hab0 : 0 < a * b := Nat.mul_pos ha.1 hb.1
        constructor
        · rw [Finset.mem_Icc]
          exact ⟨hab0, habN⟩
        · rw [Nat.mem_divisorsAntidiagonal]
          exact ⟨rfl, hab0.ne'⟩
      · rintro ⟨n, a, b⟩ hz
        rw [Finset.mem_sigma] at hz
        obtain ⟨-, hp⟩ := hz
        rw [Nat.mem_divisorsAntidiagonal] at hp
        obtain ⟨hab, -⟩ := hp
        have hab' : a * b = n := hab
        subst hab'
        rfl
      · rintro ⟨a, b⟩ _
        rfl
      · rintro ⟨n, a, b⟩ _
        rfl
    _ = ∑ a ∈ Finset.Icc 1 N,
          ∑ b ∈ Finset.Icc 1 (N / a), F a b :=
      (Finset.sum_sigma' (Finset.Icc 1 N)
        (fun a => Finset.Icc 1 (N / a))
        (fun a b => F a b)).symm

/-- **Critical weighted variation is submultiplicative for Dirichlet
convolution.**  The weight `n^(-1/2)` is exactly multiplicative, so after
the divisor-pair Fubini swap all multiplicative collisions are harmless. -/
theorem criticalWeightedVariation_arithmetic_mul_le
    (f g : ArithmeticFunction ℂ) (X : ℕ) :
    criticalWeightedVariation (fun n => (f * g) n) X ≤
      criticalWeightedVariation (fun n => f n) X *
        criticalWeightedVariation (fun n => g n) X := by
  unfold criticalWeightedVariation
  calc
    (∑ n ∈ Finset.Icc 1 X,
        ‖(f * g) n‖ / Real.sqrt (n : ℝ))
        ≤ ∑ n ∈ Finset.Icc 1 X,
            ∑ p ∈ n.divisorsAntidiagonal,
              (‖f p.1‖ / Real.sqrt (p.1 : ℝ)) *
                (‖g p.2‖ / Real.sqrt (p.2 : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [ArithmeticFunction.mul_apply]
          calc
            ‖∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2‖ /
                  Real.sqrt (n : ℝ)
                ≤ (∑ p ∈ n.divisorsAntidiagonal,
                    ‖f p.1 * g p.2‖) / Real.sqrt (n : ℝ) := by
                  exact div_le_div_of_nonneg_right
                    (norm_sum_le _ _) (Real.sqrt_nonneg _)
            _ = ∑ p ∈ n.divisorsAntidiagonal,
                  (‖f p.1‖ / Real.sqrt (p.1 : ℝ)) *
                    (‖g p.2‖ / Real.sqrt (p.2 : ℝ)) := by
                  rw [Finset.sum_div]
                  apply Finset.sum_congr rfl
                  intro p hp
                  have hab := (Nat.mem_divisorsAntidiagonal.mp hp).1
                  have habR :
                      (n : ℝ) = (p.1 : ℝ) * (p.2 : ℝ) := by
                    exact_mod_cast hab.symm
                  rw [norm_mul, habR,
                    Real.sqrt_mul' _ (by positivity : 0 ≤ (p.2 : ℝ))]
                  ring
    _ = ∑ a ∈ Finset.Icc 1 X,
          ∑ b ∈ Finset.Icc 1 (X / a),
            (‖f a‖ / Real.sqrt (a : ℝ)) *
              (‖g b‖ / Real.sqrt (b : ℝ)) :=
        sum_Icc_divisorsAntidiagonal_eq_sum_div_real
          (fun a b =>
            (‖f a‖ / Real.sqrt (a : ℝ)) *
              (‖g b‖ / Real.sqrt (b : ℝ))) X
    _ ≤ ∑ a ∈ Finset.Icc 1 X,
          (‖f a‖ / Real.sqrt (a : ℝ)) *
            (∑ b ∈ Finset.Icc 1 X,
              ‖g b‖ / Real.sqrt (b : ℝ)) := by
          apply Finset.sum_le_sum
          intro a ha
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro b hb
              rcases Finset.mem_Icc.mp hb with ⟨hb1, hbXa⟩
              exact Finset.mem_Icc.mpr
                ⟨hb1, hbXa.trans (Nat.div_le_self X a)⟩
            · intro b hb hnot
              positivity
          · positivity
    _ = (∑ a ∈ Finset.Icc 1 X,
            ‖f a‖ / Real.sqrt (a : ℝ)) *
          (∑ b ∈ Finset.Icc 1 X,
            ‖g b‖ / Real.sqrt (b : ℝ)) := by
          rw [Finset.sum_mul]

/-- Critical weighted variation is nonnegative. -/
theorem criticalWeightedVariation_nonneg
    (h : ℕ → ℂ) (X : ℕ) :
    0 ≤ criticalWeightedVariation h X := by
  unfold criticalWeightedVariation
  exact Finset.sum_nonneg fun n hn =>
    div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

private theorem criticalWeightedVariation_arithmetic_one_le_one
    (X : ℕ) :
    criticalWeightedVariation
        (fun n => (1 : ArithmeticFunction ℂ) n) X ≤ 1 := by
  unfold criticalWeightedVariation
  by_cases hX : 1 ≤ X
  · have hmem : 1 ∈ Finset.Icc 1 X :=
      Finset.mem_Icc.mpr ⟨le_rfl, hX⟩
    rw [Finset.sum_eq_single 1]
    · simp [ArithmeticFunction.one_apply]
    · intro n hn hn1
      simp [hn1]
    · intro hnot
      exact (hnot hmem).elim
  · have hX0 : X = 0 := by omega
    subst X
    simp [ArithmeticFunction.one_apply]

/-- **The raw Li correction product has the required critical variation.**
This is the product that occurs in the exact factorization of the original
Li hard-core state, before any critical transform is inserted into the owner
weights.  Repeated hyperbola submultiplicativity introduces no collision loss. -/
theorem criticalWeightedVariation_liCorrectionProduct_le_localProduct
    (k X : ℕ) :
    criticalWeightedVariation
        (fun n =>
          arithmeticHardCorePoissonCorrectionProduct
            primeSievePNTDensity k n) X ≤
      ∏ q ∈ Finset.Icc 2 (k + 1),
        criticalLiLocalCorrectionVariation q := by
  induction k with
  | zero =>
      simpa [arithmeticHardCorePoissonCorrectionProduct] using
        criticalWeightedVariation_arithmetic_one_le_one X
  | succ k ih =>
      let F : ArithmeticFunction ℂ :=
        arithmeticHardCorePoissonCorrectionFactor
          (primeSievePNTDensity (k + 2))
          (q := k + 2) (by omega)
      let P : ArithmeticFunction ℂ :=
        arithmeticHardCorePoissonCorrectionProduct
          primeSievePNTDensity k
      have hrec :
          arithmeticHardCorePoissonCorrectionProduct
              primeSievePNTDensity (Nat.succ k) = F * P := by
        rfl
      have htop : Nat.succ k + 1 = k + 2 := by omega
      rw [hrec, htop,
        Finset.prod_Icc_succ_top (by omega : 2 ≤ k + 2)]
      have hmul :
          criticalWeightedVariation (fun n => (F * P) n) X ≤
            criticalWeightedVariation (fun n => F n) X *
              criticalWeightedVariation (fun n => P n) X :=
        criticalWeightedVariation_arithmetic_mul_le F P X
      have hF :
          criticalWeightedVariation (fun n => F n) X ≤
            criticalLiLocalCorrectionVariation (k + 2) := by
        dsimp [F]
        exact
          criticalWeightedVariation_liCorrectionFactor_le_localVariation_of_two_le
            (q := k + 2) (by omega) X
      have hP :
          criticalWeightedVariation (fun n => P n) X ≤
            ∏ q ∈ Finset.Icc 2 (k + 1),
              criticalLiLocalCorrectionVariation q := by
        simpa [P] using ih
      have hP0 :
          0 ≤ criticalWeightedVariation (fun n => P n) X :=
        criticalWeightedVariation_nonneg _ X
      have hlocal0 :
          0 ≤ criticalLiLocalCorrectionVariation (k + 2) :=
        criticalLiLocalCorrectionVariation_nonneg (k + 2)
      calc
        criticalWeightedVariation (fun n => (F * P) n) X
            ≤ criticalWeightedVariation (fun n => F n) X *
                criticalWeightedVariation (fun n => P n) X := hmul
        _ ≤ criticalLiLocalCorrectionVariation (k + 2) *
              (∏ q ∈ Finset.Icc 2 (k + 1),
                criticalLiLocalCorrectionVariation q) :=
          mul_le_mul hF hP hP0 hlocal0
        _ = (∏ q ∈ Finset.Icc 2 (k + 1),
                criticalLiLocalCorrectionVariation q) *
              criticalLiLocalCorrectionVariation (k + 2) := by
          exact mul_comm _ _

/-- **Uniform weighted variation of the complete raw quadratic correction
product.**  The bound is independent of both the Li Euler cutoff and the
arithmetic endpoint, and is therefore the exact correction estimate consumed
by the original-state convolution closure. -/
theorem criticalWeightedVariation_liCorrectionProduct_le_exp_collisionBudget
    (k X : ℕ) :
    criticalWeightedVariation
        (fun n =>
          arithmeticHardCorePoissonCorrectionProduct
            primeSievePNTDensity k n) X ≤
      Real.exp (3 * criticalLiCollisionBudget) := by
  calc
    criticalWeightedVariation
        (fun n =>
          arithmeticHardCorePoissonCorrectionProduct
            primeSievePNTDensity k n) X
        ≤ ∏ q ∈ Finset.Icc 2 (k + 1),
            criticalLiLocalCorrectionVariation q :=
      criticalWeightedVariation_liCorrectionProduct_le_localProduct k X
    _ ≤ Real.exp (3 * criticalLiCollisionBudget) := by
      exact
        prod_criticalLiLocalCorrectionVariation_le_exp_collisionBudget_of_two_le
          (Finset.Icc 2 (k + 1))
          (by
            intro q hq
            exact (Finset.mem_Icc.mp hq).1)

/-- **Critical convolution transfer.**
If the reference cumulative state is uniformly bounded by B and the correction
kernel has uniformly bounded n^(-1/2)-weighted total variation H, then their
multiplicative convolution is O(sqrt X). -/
theorem norm_finiteMultiplicativeConvolution_le_sqrt
    (h M : ℕ → ℂ) (B H : ℝ)
    (hB : 0 ≤ B)
    (hM : ∀ m : ℕ, ‖M m‖ ≤ B)
    (hvar : ∀ X : ℕ, criticalWeightedVariation h X ≤ H)
    (X : ℕ) :
    ‖finiteMultiplicativeConvolution h M X‖ ≤
      B * Real.sqrt (X : ℝ) * H := by
  unfold finiteMultiplicativeConvolution
  calc
    ‖∑ n ∈ Finset.Icc 1 X, h n * M (X / n)‖
        ≤ ∑ n ∈ Finset.Icc 1 X, ‖h n * M (X / n)‖ :=
          norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 X, ‖h n‖ * ‖M (X / n)‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [norm_mul]
    _ ≤ ∑ n ∈ Finset.Icc 1 X,
          (B * Real.sqrt (X : ℝ)) *
            (‖h n‖ / Real.sqrt (n : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          rcases Finset.mem_Icc.mp hn with ⟨hn1, hnX⟩
          have hnpos : (0 : ℝ) < (n : ℝ) := by
            exact_mod_cast (show 0 < n by omega)
          have hsqrtnpos : 0 < Real.sqrt (n : ℝ) :=
            Real.sqrt_pos.2 hnpos
          have hsqrtnne : Real.sqrt (n : ℝ) ≠ 0 :=
            ne_of_gt hsqrtnpos
          have hsqrtle :
              Real.sqrt (n : ℝ) ≤ Real.sqrt (X : ℝ) := by
            apply Real.sqrt_le_sqrt
            exact_mod_cast hnX
          have hquot : 0 ≤ ‖h n‖ / Real.sqrt (n : ℝ) := by
            positivity
          calc
            ‖h n‖ * ‖M (X / n)‖ ≤ ‖h n‖ * B :=
              mul_le_mul_of_nonneg_left (hM (X / n)) (norm_nonneg _)
            _ = B * (Real.sqrt (n : ℝ) *
                  (‖h n‖ / Real.sqrt (n : ℝ))) := by
                field_simp [hsqrtnne]
            _ ≤ B * (Real.sqrt (X : ℝ) *
                  (‖h n‖ / Real.sqrt (n : ℝ))) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hsqrtle hquot) hB
            _ = (B * Real.sqrt (X : ℝ)) *
                  (‖h n‖ / Real.sqrt (n : ℝ)) := by ring
    _ = (B * Real.sqrt (X : ℝ)) *
          criticalWeightedVariation h X := by
          unfold criticalWeightedVariation
          rw [Finset.mul_sum]
    _ ≤ (B * Real.sqrt (X : ℝ)) * H := by
          exact mul_le_mul_of_nonneg_left (hvar X)
            (mul_nonneg hB (Real.sqrt_nonneg _))
    _ = B * Real.sqrt (X : ℝ) * H := by ring

/-- Square-endpoint form of the critical convolution transfer. -/
theorem norm_finiteMultiplicativeConvolution_squareRootEndpoint_le
    (h M : ℕ → ℂ) (B H : ℝ)
    (hB : 0 ≤ B)
    (hM : ∀ m : ℕ, ‖M m‖ ≤ B)
    (hvar : ∀ X : ℕ, criticalWeightedVariation h X ≤ H)
    (R : ℕ) :
    ‖finiteMultiplicativeConvolution h M (squareRootEndpoint R)‖ ≤
      B * H * (R : ℝ) := by
  by_cases hR : R = 0
  · subst R
    simp [finiteMultiplicativeConvolution, squareRootEndpoint]
  · have hRpos : (0 : ℝ) ≤ R := by positivity
    have hH : 0 ≤ H := by
      have h0 := hvar 0
      simpa [criticalWeightedVariation] using h0
    have hXle :
        (squareRootEndpoint R : ℝ) ≤ (R : ℝ) ^ 2 := by
      exact_mod_cast (Nat.sub_le (R ^ 2) 1)
    have hsqrt :
        Real.sqrt (squareRootEndpoint R : ℝ) ≤ (R : ℝ) := by
      calc
        Real.sqrt (squareRootEndpoint R : ℝ) ≤
            Real.sqrt ((R : ℝ) ^ 2) := Real.sqrt_le_sqrt hXle
        _ = (R : ℝ) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hRpos]
    have hbase :=
      norm_finiteMultiplicativeConvolution_le_sqrt
        h M B H hB hM hvar (squareRootEndpoint R)
    calc
      ‖finiteMultiplicativeConvolution h M (squareRootEndpoint R)‖
          ≤ B * Real.sqrt (squareRootEndpoint R : ℝ) * H := hbase
      _ ≤ B * (R : ℝ) * H := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsqrt hB) hH
      _ = B * H * (R : ℝ) := by ring




/-- A reference cumulative model is bounded at the exact square-root scale. -/
def SquareRootReferenceBounded (M : ℕ → ℂ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧
    ∀ X : ℕ, 1 ≤ X → ‖M X‖ ≤ B * Real.sqrt (X : ℝ)

/-- **Critical convolution transfer with a square-root reference.**
The floor child loses exactly one square-root divisor weight, so the same
critical variation controls a square-root-sized reference. -/
theorem norm_finiteMultiplicativeConvolution_le_sqrt_of_sqrtRef
    (h M : ℕ → ℂ) (B H : ℝ)
    (hB : 0 ≤ B)
    (hM : ∀ m : ℕ, 1 ≤ m → ‖M m‖ ≤ B * Real.sqrt (m : ℝ))
    (hvar : ∀ X : ℕ, criticalWeightedVariation h X ≤ H)
    (X : ℕ) (hX : 1 ≤ X) :
    ‖finiteMultiplicativeConvolution h M X‖ ≤
      B * Real.sqrt (X : ℝ) * H := by
  have hH : 0 ≤ H := by
    have h0 := hvar 0
    simpa [criticalWeightedVariation] using h0
  unfold finiteMultiplicativeConvolution
  calc
    ‖∑ n ∈ Finset.Icc 1 X, h n * M (X / n)‖
        ≤ ∑ n ∈ Finset.Icc 1 X, ‖h n * M (X / n)‖ :=
          norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 X, ‖h n‖ * ‖M (X / n)‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [norm_mul]
    _ ≤ ∑ n ∈ Finset.Icc 1 X,
          (B * Real.sqrt (X : ℝ)) *
            (‖h n‖ / Real.sqrt (n : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          rcases Finset.mem_Icc.mp hn with ⟨hn1, hnX⟩
          have hnposNat : 0 < n := by omega
          have hchild1 : 1 ≤ X / n :=
            (Nat.one_le_div_iff hnposNat).2 hnX
          have hnpos : (0 : ℝ) < (n : ℝ) := by
            exact_mod_cast hnposNat
          have hsqrtnpos : 0 < Real.sqrt (n : ℝ) :=
            Real.sqrt_pos.2 hnpos
          have hsqrtnne : Real.sqrt (n : ℝ) ≠ 0 :=
            ne_of_gt hsqrtnpos
          have hcast :
              ((X / n : ℕ) : ℝ) ≤ (X : ℝ) / (n : ℝ) :=
            Nat.cast_div_le
          have hsqrt := Real.sqrt_le_sqrt hcast
          have hsqrtDiv :
              Real.sqrt ((X : ℝ) / (n : ℝ)) =
                Real.sqrt (X : ℝ) / Real.sqrt (n : ℝ) := by
            exact Real.sqrt_div
              (show 0 ≤ (X : ℝ) by positivity) (n : ℝ)
          have hchild :
              Real.sqrt ((X / n : ℕ) : ℝ) ≤
                Real.sqrt (X : ℝ) / Real.sqrt (n : ℝ) := by
            rw [← hsqrtDiv]
            exact hsqrt
          calc
            ‖h n‖ * ‖M (X / n)‖
                ≤ ‖h n‖ *
                    (B * Real.sqrt ((X / n : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (hM (X / n) hchild1) (norm_nonneg _)
            _ ≤ ‖h n‖ *
                    (B * (Real.sqrt (X : ℝ) / Real.sqrt (n : ℝ))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hchild hB) (norm_nonneg _)
            _ = (B * Real.sqrt (X : ℝ)) *
                  (‖h n‖ / Real.sqrt (n : ℝ)) := by
              field_simp [hsqrtnne]
    _ = (B * Real.sqrt (X : ℝ)) *
          criticalWeightedVariation h X := by
          unfold criticalWeightedVariation
          rw [Finset.mul_sum]
    _ ≤ (B * Real.sqrt (X : ℝ)) * H := by
          exact mul_le_mul_of_nonneg_left (hvar X)
            (mul_nonneg hB (Real.sqrt_nonneg _))
    _ = B * Real.sqrt (X : ℝ) * H := by ring

/-- Square-endpoint form of the critical convolution transfer for a
square-root-bounded reference. -/
theorem norm_finiteMultiplicativeConvolution_squareRootEndpoint_of_sqrtRef
    (h M : ℕ → ℂ) (B H : ℝ)
    (hB : 0 ≤ B)
    (hM : ∀ m : ℕ, 1 ≤ m → ‖M m‖ ≤ B * Real.sqrt (m : ℝ))
    (hvar : ∀ X : ℕ, criticalWeightedVariation h X ≤ H)
    (R : ℕ) :
    ‖finiteMultiplicativeConvolution h M (squareRootEndpoint R)‖ ≤
      B * H * (R : ℝ) := by
  have hH : 0 ≤ H := by
    have h0 := hvar 0
    simpa [criticalWeightedVariation] using h0
  by_cases hX0 : squareRootEndpoint R = 0
  · have hnonneg : 0 ≤ B * H * (R : ℝ) := by positivity
    simpa [hX0, finiteMultiplicativeConvolution] using hnonneg
  have hX1 : 1 ≤ squareRootEndpoint R := by omega
  have hRpos : (0 : ℝ) ≤ R := by positivity
  have hXle :
      (squareRootEndpoint R : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast (Nat.sub_le (R ^ 2) 1)
  have hsqrt :
      Real.sqrt (squareRootEndpoint R : ℝ) ≤ (R : ℝ) := by
    calc
      Real.sqrt (squareRootEndpoint R : ℝ) ≤
          Real.sqrt ((R : ℝ) ^ 2) := Real.sqrt_le_sqrt hXle
      _ = (R : ℝ) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hRpos]
  have hbase :=
    norm_finiteMultiplicativeConvolution_le_sqrt_of_sqrtRef
      h M B H hB hM hvar (squareRootEndpoint R) hX1
  calc
    ‖finiteMultiplicativeConvolution h M (squareRootEndpoint R)‖
        ≤ B * Real.sqrt (squareRootEndpoint R : ℝ) * H := hbase
    _ ≤ B * (R : ℝ) * H := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsqrt hB) hH
    _ = B * H * (R : ℝ) := by ring



/-! ## Convolution-reference closure of the pure Li model -/

/-- The formal Dickman construction supplies the concrete uniformly bounded
integer reference required by the convolution closure. -/
theorem exactLiDickmanIntegerReference_isUniformlyBounded :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : ℕ, ‖exactLiDickmanIntegerReference x‖ ≤ B :=
  exactLiDickmanIntegerReference_uniformly_bounded

/-- A correction kernel has uniformly bounded critical weighted variation. -/
def UniformCriticalWeightedVariation (h : ℕ → ℂ) : Prop :=
  ∃ H : ℝ, 0 ≤ H ∧
    ∀ X : ℕ, criticalWeightedVariation h X ≤ H

/-- Exact diagonal factorization of every all-scale Li state through a fixed
reference cumulative model and a multiplicative correction kernel. -/
def AllScaleLiDiagonalConvolutionFactorization
    (h M : ℕ → ℂ) : Prop :=
  ∀ (L : ℕ → ℕ → ℂ) (X : ℕ),
    1 ≤ X →
    IsAllScaleLiState L →
    L X X = finiteMultiplicativeConvolution h M X

/-- Every all-scale exact-Li diagonal factors through the stabilized
quadratic correction kernel and stabilized Poisson cumulative reference. -/
theorem allScaleLiState_diagonal_eq_poissonConvolution
    {L : ℕ → ℕ → ℂ} {X : ℕ} (hX : 1 ≤ X)
    (hL : IsAllScaleLiState L) :
    L X X =
      finiteMultiplicativeConvolution
        exactLiCorrectionKernel exactLiPoissonIntegerReference X := by
  rw [allScaleLiState_diagonal_eq_hardCoreProductCumulative X hX hL,
    arithmeticHardCoreProduct_eq_correctionProduct_mul_poissonProduct,
    arithmeticCoefficientCumulative_mul_eq_finiteMultiplicativeConvolution]
  unfold finiteMultiplicativeConvolution
  apply Finset.sum_congr rfl
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hn1, hnX⟩
  have hnpos : 0 < n := by omega
  have hchild1 : 1 ≤ X / n :=
    (Nat.one_le_div_iff hnpos).2 hnX
  have hchildX : X / n ≤ X := Nat.div_le_self X n
  change
    arithmeticHardCorePoissonCorrectionProduct
        primeSievePNTDensity (X - 1) n *
      arithmeticCoefficientCumulative
        (arithmeticPoissonProduct primeSievePNTDensity (X - 1)) (X / n) =
      exactLiCorrectionKernel n * exactLiPoissonIntegerReference (X / n)
  rw [← exactLiCorrectionKernel_eq_cutoff hn1 hnX,
    ← exactLiPoissonIntegerReference_eq_child hchild1 hchildX]

/-- The stabilized exact-Li correction kernel has the same uniform critical
variation budget as every sufficiently large finite cutoff. -/
theorem exactLiCorrectionKernel_uniformVariation :
    UniformCriticalWeightedVariation exactLiCorrectionKernel := by
  refine ⟨Real.exp (3 * criticalLiCollisionBudget), (Real.exp_pos _).le, ?_⟩
  intro X
  by_cases hX0 : X = 0
  · subst X
    simpa [criticalWeightedVariation] using
      (Real.exp_pos (3 * criticalLiCollisionBudget)).le
  · have hX : 1 ≤ X := by omega
    calc
      criticalWeightedVariation exactLiCorrectionKernel X =
          criticalWeightedVariation
            (fun n =>
              arithmeticHardCorePoissonCorrectionProduct
                primeSievePNTDensity (X - 1) n) X := by
            unfold criticalWeightedVariation
            apply Finset.sum_congr rfl
            intro n hn
            rcases Finset.mem_Icc.mp hn with ⟨hn1, hnX⟩
            rw [exactLiCorrectionKernel_eq_cutoff hn1 hnX]
      _ ≤ Real.exp (3 * criticalLiCollisionBudget) :=
        criticalWeightedVariation_liCorrectionProduct_le_exp_collisionBudget
          (X - 1) X

/-- **Square-root-reference correction-kernel closure.**
A square-root-bounded reference, uniformly bounded critical correction
variation, and exact diagonal convolution factorization close the intrinsic
all-scale exact-Li square-root theorem. -/
theorem allScaleLiSquareRootBounded_of_sqrtReference_convolution
    (h M : ℕ → ℂ)
    (hM : SquareRootReferenceBounded M)
    (hh : UniformCriticalWeightedVariation h)
    (hfac : AllScaleLiDiagonalConvolutionFactorization h M) :
    AllScaleLiSquareRootBoundedStatement := by
  rcases hM with ⟨B, hB, hMb⟩
  rcases hh with ⟨H, hH, hvar⟩
  refine ⟨(B * H) ^ 2, sq_nonneg _, ?_⟩
  intro L R hL _hsat hR
  have hX1 : 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hR2 : 4 ≤ R ^ 2 := by nlinarith
    omega
  have hconv :=
    norm_finiteMultiplicativeConvolution_squareRootEndpoint_of_sqrtRef
      h M B H hB hMb hvar R
  rw [← hfac L (squareRootEndpoint R) hX1 hL] at hconv
  have hBH : 0 ≤ B * H := mul_nonneg hB hH
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  have hright : 0 ≤ (B * H) * (R : ℝ) :=
    mul_nonneg hBH hR0
  have hsquare :=
    mul_self_le_mul_self
      (norm_nonneg (L (squareRootEndpoint R) (squareRootEndpoint R)))
      hconv
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsquare

/-- **Correction-kernel pure-model closure.**
A uniformly bounded reference, a correction kernel with uniformly bounded
critical variation, and the exact diagonal convolution factorization imply the
intrinsic all-scale Li square-root theorem. -/
theorem allScaleLiSquareRootBounded_of_convolutionReference
    (h M : ℕ → ℂ)
    (hM : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℕ, ‖M x‖ ≤ B)
    (hh : UniformCriticalWeightedVariation h)
    (hfac : AllScaleLiDiagonalConvolutionFactorization h M) :
    AllScaleLiSquareRootBoundedStatement := by
  rcases hM with ⟨B, hB, hMb⟩
  rcases hh with ⟨H, hH, hvar⟩
  refine ⟨(B * H) ^ 2, sq_nonneg _, ?_⟩
  intro L R hL hsat hR
  have hX1 : 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hR2 : 4 ≤ R ^ 2 := by nlinarith
    omega
  have hconv :=
    norm_finiteMultiplicativeConvolution_squareRootEndpoint_le
      h M B H hB hMb hvar R
  rw [← hfac L (squareRootEndpoint R) hX1 hL] at hconv
  have hBH : 0 ≤ B * H := mul_nonneg hB hH
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  have hright : 0 ≤ (B * H) * (R : ℝ) :=
    mul_nonneg hBH hR0
  have hsquare :=
    mul_self_le_mul_self
      (norm_nonneg (L (squareRootEndpoint R) (squareRootEndpoint R)))
      hconv
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsquare

/-- Critical transform of an all-scale Li state. -/
def allScaleLiCriticalState
    (L : ℕ → ℕ → ℂ) (x y : ℕ) : ℂ :=
  1 + weightedForwardDifferencePrefix criticalSqrtWeight
    (fun n => L n y) x

/-- The critical transform is itself an exact largest-site frequency state,
with Li singleton weights divided by sqrt(q). -/
theorem allScaleLiCriticalState_isPrimeFrequencyState
    {L : ℕ → ℕ → ℂ} (hL : IsAllScaleLiState L) :
    IsPrimeFrequencyState criticalLiFrequencyWeight
      (allScaleLiCriticalState L) := by
  intro x y
  unfold allScaleLiCriticalState primeFrequencyStep criticalLiFrequencyWeight
  have hzero : ∀ q : ℕ, L 0 (q - 1) = 1 := by
    intro q
    rw [hL 0 (q - 1)]
    simp [primeFrequencyStep]
  have hrec :=
    weightedForwardDifferencePrefix_primeFrequencyState
      hL criticalSqrtWeight_mul x y
  rw [hrec]
  apply congrArg (fun z : ℂ => 1 - z)
  apply Finset.sum_congr rfl
  intro q hq
  rw [hzero q]


/-! ## Exact reciprocal/Dickman coordinate -/

/-- Multiplicative reciprocal weight n^(-1). -/
def reciprocalWeight (n : ℕ) : ℂ :=
  ((n : ℂ))⁻¹

/-- The reciprocal weight is exactly multiplicative. -/
theorem reciprocalWeight_mul (a b : ℕ) :
    reciprocalWeight (a * b) =
      reciprocalWeight a * reciprocalWeight b := by
  simp [reciprocalWeight, Nat.cast_mul, mul_inv_rev, mul_comm]

/-- Li owner weight after the exact reciprocal transform. -/
def reciprocalLiFrequencyWeight (q : ℕ) : ℂ :=
  primeSievePNTDensity q * reciprocalWeight q



private theorem exactLi_loglog_intervalIntegrable
    {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := (le_min ha hb).trans ht.1
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith))
  have hc0 : ContinuousAt (fun s : ℝ => s * Real.log s) t :=
    continuousAt_id.mul (Real.continuousAt_log ht0)
  exact (continuousAt_const.div hc0 (mul_ne_zero ht0 hl0)).continuousWithinAt

private theorem exactLi_loglog_primitive
    {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (∫ t in a..b, 1 / (t * Real.log t)) =
      Real.log (Real.log b) - Real.log (Real.log a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => Real.log (Real.log t)) _
    (exactLi_loglog_intervalIntegrable ha hb)
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := (le_min ha hb).trans ht.1
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith))
  convert (Real.hasDerivAt_log ht0).log hl0 using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- One exact singleton Li mass, after reciprocal weighting, is bounded by the
corresponding log-log increment. -/
theorem exactLi_norm_pntDensity_div_le_loglog_step
    {q : ℕ} (hq : 3 ≤ q) :
    ‖primeSievePNTDensity q‖ / (q : ℝ) ≤
      Real.log (Real.log (q : ℝ)) -
        Real.log (Real.log ((q - 1 : ℕ) : ℝ)) := by
  have ha : (2 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ q - 1 by omega)
  have hb : (2 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (show 2 ≤ q by omega)
  have hab : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.sub_le q 1
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (exactLi_invLog_intervalIntegrable (a := 2) (by norm_num) ha)
    (exactLi_invLog_intervalIntegrable ha hb)
  have hdiff :
      logarithmicIntegralFromTwo (q : ℝ) -
          logarithmicIntegralFromTwo ((q - 1 : ℕ) : ℝ) =
        ∫ t in ((q - 1 : ℕ) : ℝ)..(q : ℝ), (Real.log t)⁻¹ := by
    unfold logarithmicIntegralFromTwo
    linarith [hadd]
  have hnonneg :
      0 ≤ logarithmicIntegralFromTwo (q : ℝ) -
        logarithmicIntegralFromTwo ((q - 1 : ℕ) : ℝ) := by
    rw [hdiff]
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    apply inv_nonneg.mpr
    apply Real.log_nonneg
    linarith [ht.1]
  rw [primeSievePNTDensity, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hnonneg, hdiff, ← intervalIntegral.integral_div]
  calc
    (∫ t in ((q - 1 : ℕ) : ℝ)..(q : ℝ),
        (Real.log t)⁻¹ / (q : ℝ))
        ≤ ∫ t in ((q - 1 : ℕ) : ℝ)..(q : ℝ),
            1 / (t * Real.log t) := by
      apply intervalIntegral.integral_mono_on hab
        ((exactLi_invLog_intervalIntegrable ha hb).div_const (q : ℝ))
        (exactLi_loglog_intervalIntegrable ha hb)
      intro t ht
      have ht2 : (2 : ℝ) ≤ t := ha.trans ht.1
      have hl : 0 ≤ (Real.log t)⁻¹ :=
        inv_nonneg.mpr (Real.log_nonneg (by linarith))
      calc
        (Real.log t)⁻¹ / (q : ℝ) ≤
            (Real.log t)⁻¹ / t :=
          div_le_div_of_nonneg_left hl (by linarith) ht.2
        _ = 1 / (t * Real.log t) := by
          simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    _ = _ := exactLi_loglog_primitive ha hb

private theorem exactLi_sum_backward_difference
    (g : ℕ → ℝ) {y x : ℕ} (hyx : y ≤ x) :
    (∑ q ∈ Finset.Ioc y x, (g q - g (q - 1))) =
      g x - g y := by
  induction x with
  | zero =>
      have hy : y = 0 := by omega
      subst y
      simp
  | succ x ih =>
      by_cases h : y ≤ x
      · rw [Finset.sum_Ioc_succ_top h, ih h]
        simp only [Nat.add_sub_cancel]
        ring
      · have heq : y = x + 1 := by omega
        subst y
        simp

/-- The reciprocal mass of exact singleton Li weights telescopes to a log-log
endpoint increment, without importing any external research module. -/
theorem exactLi_reciprocal_mass_le
    {y x : ℕ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    (∑ q ∈ Finset.Ioc y x,
        ‖primeSievePNTDensity q‖ / (q : ℝ)) ≤
      Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (y : ℝ)) := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioc y x,
        (Real.log (Real.log (q : ℝ)) -
          Real.log (Real.log ((q - 1 : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro q hq
      exact exactLi_norm_pntDensity_div_le_loglog_step
        (by
          have := (Finset.mem_Ioc.mp hq).1
          omega)
    _ = _ :=
      exactLi_sum_backward_difference
        (fun q => Real.log (Real.log (q : ℝ))) hyx

/-- On every root-to-square interval the total reciprocal Li owner mass is
strictly contractive: at most log 2.  This is the exact discrete analogue of
the unit-length Dickman delay mass after logarithmic rescaling. -/
theorem reciprocalLiFrequencyWeight_norm_sum_rootSquare_le_log_two
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    (∑ q ∈ Finset.Ioc y x, ‖reciprocalLiFrequencyWeight q‖) ≤
      Real.log 2 := by
  by_cases hyx : y ≤ x
  · have hypos : (0 : ℝ) < y := by
      exact_mod_cast (show 0 < y by omega)
    have hxpos : (0 : ℝ) < x := by
      exact_mod_cast (show 0 < x by omega)
    have hly : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hlx : 0 < Real.log (x : ℝ) :=
      hly.trans_le (Real.log_le_log hypos (by exact_mod_cast hyx))
    have hxlog : Real.log (x : ℝ) ≤ 2 * Real.log (y : ℝ) := by
      calc
        Real.log (x : ℝ) ≤ Real.log ((y : ℝ) ^ 2) :=
          Real.log_le_log hxpos (by exact_mod_cast hxy)
        _ = 2 * Real.log (y : ℝ) := by
          rw [Real.log_pow]
          norm_num
    have hll := Real.log_le_log hlx hxlog
    rw [Real.log_mul (by norm_num) (ne_of_gt hly)] at hll
    have hmass := exactLi_reciprocal_mass_le hy hyx
    have hm :
        (∑ q ∈ Finset.Ioc y x,
          ‖primeSievePNTDensity q‖ / (q : ℝ)) ≤ Real.log 2 := by
      linarith
    calc
      (∑ q ∈ Finset.Ioc y x, ‖reciprocalLiFrequencyWeight q‖)
          = ∑ q ∈ Finset.Ioc y x,
              ‖primeSievePNTDensity q‖ / (q : ℝ) := by
            apply Finset.sum_congr rfl
            intro q hq
            unfold reciprocalLiFrequencyWeight reciprocalWeight
            rw [norm_mul, norm_inv]
            simp [div_eq_mul_inv]
      _ ≤ Real.log 2 := hm
  · rw [Finset.Ioc_eq_empty_of_le (Nat.le_of_not_ge hyx)]
    simp only [Finset.sum_empty]
    exact Real.log_nonneg (by norm_num)

/-- Reciprocal transform of an all-scale Li state.  This is the discrete
counterpart of A(x)=∫ u^(-1) dν(u) in the continuous Dickman derivation. -/
def allScaleLiReciprocalState
    (L : ℕ → ℕ → ℂ) (x y : ℕ) : ℂ :=
  1 + weightedForwardDifferencePrefix reciprocalWeight
    (fun n => L n y) x

/-- The reciprocal transform is itself an exact largest-site frequency state,
with singleton Li owner weight w_q/q. -/
theorem allScaleLiReciprocalState_isPrimeFrequencyState
    {L : ℕ → ℕ → ℂ} (hL : IsAllScaleLiState L) :
    IsPrimeFrequencyState reciprocalLiFrequencyWeight
      (allScaleLiReciprocalState L) := by
  intro x y
  unfold allScaleLiReciprocalState primeFrequencyStep
    reciprocalLiFrequencyWeight
  have hzero : ∀ q : ℕ, L 0 (q - 1) = 1 := by
    intro q
    rw [hL 0 (q - 1)]
    simp [primeFrequencyStep]
  have hrec :=
    weightedForwardDifferencePrefix_primeFrequencyState
      hL reciprocalWeight_mul x y
  rw [hrec]
  apply congrArg (fun z : ℂ => 1 - z)
  apply Finset.sum_congr rfl
  intro q hq
  rw [hzero q]

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


/-! ## First-order critical bin transport budget -/

/-- Critical cost of moving the Li mass in the unit bin (n,n+1] from the
left critical weight n^(-1/2) to the discrete endpoint (n+1)^(-1/2). -/
def criticalLiEndpointBinGap (n : ℕ) : ℝ :=
  ‖primeSievePNTDensity (n + 1)‖ *
    ((Real.sqrt (n : ℝ))⁻¹ -
      (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)

/-- The critical endpoint shift in one Li bin is nonnegative. -/
theorem criticalLiEndpointBinGap_nonneg
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ criticalLiEndpointBinGap n := by
  unfold criticalLiEndpointBinGap
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n + 1 by omega)
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsqrtnp : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.2 hnp
  have hsqrtle :
      Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    norm_num
  have hinv :
      (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ ≤
        (Real.sqrt (n : ℝ))⁻¹ :=
    (inv_le_inv₀ hsqrtnp hsqrtn).2 hsqrtle
  exact mul_nonneg (norm_nonneg _) (sub_nonneg.mpr hinv)

/-- **Uniform first-order discrete/continuous critical transport budget.**
The Li mass in every unit bin is the same on both sides; only its location
moves.  At critical weight n^(-1/2), these endpoint moves telescope, so their
total cost is uniformly finite. -/
theorem criticalLiEndpointBinGap_sum_le
    {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Ico 2 N, criticalLiEndpointBinGap n) ≤
      (Real.log 2)⁻¹ * (Real.sqrt 2)⁻¹ := by
  let C : ℝ := (Real.log 2)⁻¹
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hterm :
      ∀ n ∈ Finset.Ico 2 N,
        criticalLiEndpointBinGap n ≤
          C * ((Real.sqrt (n : ℝ))⁻¹ -
            (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) := by
    intro n hnmem
    have hn2 : 2 ≤ n := (Finset.mem_Ico.mp hnmem).1
    have hweight :
        ‖primeSievePNTDensity (n + 1)‖ ≤ C := by
      dsimp [C]
      exact exactLi_norm_pntDensity_le_inv_log
        (y := 2) (q := n + 1) (by norm_num) (by omega)
    have hgap :
        0 ≤ (Real.sqrt (n : ℝ))⁻¹ -
          (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := by
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hnp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < n + 1 by omega)
      have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
      have hsqrtnp : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
        Real.sqrt_pos.2 hnp
      have hsqrtle :
          Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
        apply Real.sqrt_le_sqrt
        norm_num
      exact sub_nonneg.mpr ((inv_le_inv₀ hsqrtnp hsqrtn).2 hsqrtle)
    unfold criticalLiEndpointBinGap
    exact mul_le_mul_of_nonneg_right hweight hgap
  calc
    (∑ n ∈ Finset.Ico 2 N, criticalLiEndpointBinGap n)
        ≤ ∑ n ∈ Finset.Ico 2 N,
            C * ((Real.sqrt (n : ℝ))⁻¹ -
              (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) := by
          exact Finset.sum_le_sum hterm
    _ = C * (∑ n ∈ Finset.Ico 2 N,
          ((Real.sqrt (n : ℝ))⁻¹ -
            (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)) := by
          rw [Finset.mul_sum]
    _ = C * ((Real.sqrt 2)⁻¹ - (Real.sqrt (N : ℝ))⁻¹) := by
          have hforward := sum_Ico_forwardDiff_real
            (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) hN
          have hback :
              (∑ n ∈ Finset.Ico 2 N,
                ((Real.sqrt (n : ℝ))⁻¹ -
                  (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)) =
                (Real.sqrt 2)⁻¹ - (Real.sqrt (N : ℝ))⁻¹ := by
            calc
              _ = -(∑ n ∈ Finset.Ico 2 N,
                    ((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ -
                      (Real.sqrt (n : ℝ))⁻¹)) := by
                    rw [← Finset.sum_neg_distrib]
                    apply Finset.sum_congr rfl
                    intro n hn
                    ring
              _ = _ := by rw [hforward]; ring
          rw [hback]
    _ ≤ C * (Real.sqrt 2)⁻¹ := by
          have hNinv : 0 ≤ (Real.sqrt (N : ℝ))⁻¹ := by positivity
          nlinarith
    _ = (Real.log 2)⁻¹ * (Real.sqrt 2)⁻¹ := by
          rfl


/-! ## Exact continuous-vs-discrete degree-one Li bin sandwich -/

/-- Continuous critical Li mass in the unit bin `(n,n+1]`.
This keeps the Li density and the critical `t^(-1/2)` weight at their
continuous locations. -/
def exactLiContinuousCriticalBinMass (n : ℕ) : ℝ :=
  ∫ t in (n : ℝ)..((n + 1 : ℕ) : ℝ),
    (Real.log t)⁻¹ / Real.sqrt t

/-- Discrete critical Li mass after moving the entire unit-bin Li mass to the
right integer endpoint. -/
def exactLiDiscreteCriticalBinMass (n : ℕ) : ℝ :=
  densityTightLiWeight (n + 1) /
    Real.sqrt ((n + 1 : ℕ) : ℝ)

/-- Conservative left-endpoint envelope for the same unit-bin Li mass. -/
def exactLiLeftCriticalBinEnvelope (n : ℕ) : ℝ :=
  densityTightLiWeight (n + 1) / Real.sqrt (n : ℝ)

private theorem exactLi_criticalBinDensity_intervalIntegrable
    {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => (Real.log t)⁻¹ / Real.sqrt t)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := (le_min ha hb).trans ht.1
  have ht0 : t ≠ 0 := by linarith
  have hlog0 : Real.log t ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith))
  have hsqrt0 : Real.sqrt t ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hnum : ContinuousAt (fun s : ℝ => (Real.log s)⁻¹) t :=
    (Real.continuousAt_log ht0).inv₀ hlog0
  have hden : ContinuousAt (fun s : ℝ => Real.sqrt s) t :=
    Real.continuous_sqrt.continuousAt
  exact (hnum.div hden hsqrt0).continuousWithinAt

/-- The complex singleton Li weight has norm equal to its underlying positive
real unit-bin mass. -/
theorem norm_primeSievePNTDensity_eq_densityTightLiWeight
    {q : ℕ} (hq : 3 ≤ q) :
    ‖primeSievePNTDensity q‖ = densityTightLiWeight q := by
  unfold primeSievePNTDensity
  rw [Complex.norm_real, Real.norm_eq_abs]
  change |densityTightLiWeight q| = densityTightLiWeight q
  exact abs_of_nonneg (densityTightLiWeight_nonneg hq)

/-- **Right-endpoint discretization is degree-one optimistic.**
For every Li unit bin from `n >= 2`, placing the entire mass at the right
integer endpoint can only decrease its critical degree-one mass. -/
theorem exactLiDiscreteCriticalBinMass_le_continuous
    {n : ℕ} (hn : 2 ≤ n) :
    exactLiDiscreteCriticalBinMass n ≤
      exactLiContinuousCriticalBinMass n := by
  have hq : 3 ≤ n + 1 := by omega
  have ha : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ n + 1 by omega)
  have hab : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
  unfold exactLiDiscreteCriticalBinMass exactLiContinuousCriticalBinMass
  rw [densityTightLiWeight_eq_integral hq,
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_mono_on hab
    ((exactLi_invLog_intervalIntegrable ha hb).div_const
      (Real.sqrt ((n + 1 : ℕ) : ℝ)))
    (exactLi_criticalBinDensity_intervalIntegrable ha hb)
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := ha.trans ht.1
  have hlog :
      0 ≤ (Real.log t)⁻¹ :=
    inv_nonneg.mpr (Real.log_nonneg (by linarith))
  have hsqrtt : 0 < Real.sqrt t :=
    Real.sqrt_pos.2 (by linarith)
  have hsqrtle :
      Real.sqrt t ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt ht.2
  exact div_le_div_of_nonneg_left hlog hsqrtt hsqrtle

/-- The continuous critical Li mass is itself bounded by placing the same mass
at the left endpoint of its unit bin. -/
theorem exactLiContinuousCriticalBinMass_le_leftEnvelope
    {n : ℕ} (hn : 2 ≤ n) :
    exactLiContinuousCriticalBinMass n ≤
      exactLiLeftCriticalBinEnvelope n := by
  have hq : 3 ≤ n + 1 := by omega
  have ha : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ n + 1 by omega)
  have hab : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
  unfold exactLiContinuousCriticalBinMass exactLiLeftCriticalBinEnvelope
  rw [densityTightLiWeight_eq_integral hq,
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_mono_on hab
    (exactLi_criticalBinDensity_intervalIntegrable ha hb)
    ((exactLi_invLog_intervalIntegrable ha hb).div_const
      (Real.sqrt (n : ℝ)))
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := ha.trans ht.1
  have hlog :
      0 ≤ (Real.log t)⁻¹ :=
    inv_nonneg.mpr (Real.log_nonneg (by linarith))
  have hsqrtn : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
  have hsqrtle : Real.sqrt (n : ℝ) ≤ Real.sqrt t :=
    Real.sqrt_le_sqrt ht.1
  exact div_le_div_of_nonneg_left hlog hsqrtn hsqrtle

/-- The full left-minus-right endpoint width is exactly the already-certified
critical Li bin gap. -/
theorem exactLiLeftEnvelope_sub_discrete_eq_endpointBinGap
    {n : ℕ} (hn : 2 ≤ n) :
    exactLiLeftCriticalBinEnvelope n -
        exactLiDiscreteCriticalBinMass n =
      criticalLiEndpointBinGap n := by
  unfold exactLiLeftCriticalBinEnvelope exactLiDiscreteCriticalBinMass
    criticalLiEndpointBinGap
  rw [norm_primeSievePNTDensity_eq_densityTightLiWeight
    (q := n + 1) (by omega : 3 ≤ n + 1)]
  simp only [div_eq_mul_inv]
  ring

/-- Exact continuous-minus-discrete first-order transport error in one Li bin. -/
def exactLiCriticalBinTransportError (n : ℕ) : ℝ :=
  exactLiContinuousCriticalBinMass n -
    exactLiDiscreteCriticalBinMass n

/-- The continuous placement is conservative: the degree-one transport error
is nonnegative. -/
theorem exactLiCriticalBinTransportError_nonneg
    {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ exactLiCriticalBinTransportError n := by
  unfold exactLiCriticalBinTransportError
  exact sub_nonneg.mpr (exactLiDiscreteCriticalBinMass_le_continuous hn)

/-- The continuous-vs-discrete degree-one error is no larger than the
left-to-right endpoint gap already used by the critical transport budget. -/
theorem exactLiCriticalBinTransportError_le_endpointBinGap
    {n : ℕ} (hn : 2 ≤ n) :
    exactLiCriticalBinTransportError n ≤ criticalLiEndpointBinGap n := by
  unfold exactLiCriticalBinTransportError
  calc
    exactLiContinuousCriticalBinMass n -
          exactLiDiscreteCriticalBinMass n
        ≤ exactLiLeftCriticalBinEnvelope n -
          exactLiDiscreteCriticalBinMass n :=
      sub_le_sub_right
        (exactLiContinuousCriticalBinMass_le_leftEnvelope hn) _
    _ = criticalLiEndpointBinGap n :=
      exactLiLeftEnvelope_sub_discrete_eq_endpointBinGap hn

/-- **Uniform degree-one continuous-to-discrete Li transfer.**
The complete first-order critical error through any finite endpoint is bounded
by the same absolute telescoping constant. -/
theorem sum_exactLiCriticalBinTransportError_le
    {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Ico 2 N, exactLiCriticalBinTransportError n) ≤
      (Real.log 2)⁻¹ * (Real.sqrt 2)⁻¹ := by
  calc
    (∑ n ∈ Finset.Ico 2 N, exactLiCriticalBinTransportError n)
        ≤ ∑ n ∈ Finset.Ico 2 N, criticalLiEndpointBinGap n := by
          apply Finset.sum_le_sum
          intro n hn
          exact exactLiCriticalBinTransportError_le_endpointBinGap
            (Finset.mem_Ico.mp hn).1
    _ ≤ (Real.log 2)⁻¹ * (Real.sqrt 2)⁻¹ :=
      criticalLiEndpointBinGap_sum_le hN


/-- Exact finite Abel identity at square-root weight.
The boundary formula is valid from the first nonzero index onward. -/
theorem sum_sqrtAbelIncrement_eq
    (A : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, sqrtAbelIncrement A n) =
      (Real.sqrt (N : ℝ) : ℂ) * A N - A 0 -
        ∑ n ∈ Finset.Ico 1 N,
          A n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) -
            Real.sqrt (n : ℝ) : ℝ) : ℂ) := by
  cases N with
  | zero =>
      omega
  | succ N =>
      induction N with
      | zero =>
          norm_num [sqrtAbelIncrement]
      | succ N ih =>
          have hN1 : 1 ≤ N + 1 := by omega
          rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 2),
            Finset.sum_Ico_succ_top hN1, ih hN1]
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
  rw [sum_sqrtAbelIncrement_eq A N hN]
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hsqrtN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hA0 : ‖A 0‖ ≤ B := hA 0 (Nat.zero_le N)
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
          exact mul_le_mul (hA n hnle) le_rfl hstep hB
      _ = B * (∑ n ∈ Finset.Ico 1 N,
            (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))) := by
          rw [Finset.mul_sum]
      _ = B * (Real.sqrt (N : ℝ) - 1) := by
          rw [sum_Ico_sqrt_step hN]
      _ = (Real.sqrt (N : ℝ) - 1) * B := by ring
  calc
    ‖(Real.sqrt (N : ℝ) : ℂ) * A N - A 0 -
        ∑ n ∈ Finset.Ico 1 N,
          A n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) -
            Real.sqrt (n : ℝ) : ℝ) : ℂ)‖
        ≤ ‖(Real.sqrt (N : ℝ) : ℂ) * A N‖ + ‖A 0‖ +
          ‖∑ n ∈ Finset.Ico 1 N,
            A n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) -
              Real.sqrt (n : ℝ) : ℝ) : ℂ)‖ := by
          calc
            _ ≤ ‖(Real.sqrt (N : ℝ) : ℂ) * A N - A 0‖ +
                ‖∑ n ∈ Finset.Ico 1 N,
                  A n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) -
                    Real.sqrt (n : ℝ) : ℝ) : ℂ)‖ := norm_sub_le _ _
            _ ≤ (‖(Real.sqrt (N : ℝ) : ℂ) * A N‖ + ‖A 0‖) +
                ‖∑ n ∈ Finset.Ico 1 N,
                  A n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) -
                    Real.sqrt (n : ℝ) : ℝ) : ℂ)‖ := by
                  gcongr
                  exact norm_sub_le _ _
    _ ≤ Real.sqrt (N : ℝ) * B + B +
        (Real.sqrt (N : ℝ) - 1) * B := by
          gcongr
    _ = 2 * Real.sqrt (N : ℝ) * B := by ring



/-! ## Saturation and fixed-cutoff critical coordinate -/

/-- Saturation is automatic for every prime-frequency state because the
recursion depends on the cutoff only through `min x y`. -/
theorem primeFrequencyState_saturated
    {w : ℕ → ℂ} {S : ℕ → ℕ → ℂ}
    (hS : IsPrimeFrequencyState w S) :
    PrimeFrequencySaturated S := by
  intro x y hxy
  rw [hS x y, hS x x]
  unfold primeFrequencyStep
  rw [min_eq_left hxy, min_self]


/-! ## Reciprocal square-root contraction -/

/-- Exact square-root split for the reciprocal/Dickman transform. -/
theorem allScaleLiReciprocalState_squareRoot_split
    {L : ℕ → ℕ → ℂ}
    (R : ℕ) (hR : 2 ≤ R) (hL : IsAllScaleLiState L) :
    allScaleLiReciprocalState L (squareRootEndpoint R) (squareRootEndpoint R) =
      allScaleLiReciprocalState L (squareRootEndpoint R) R -
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          reciprocalLiFrequencyWeight q *
            allScaleLiReciprocalState L
              (squareRootEndpoint R / q) (squareRootEndpoint R / q) := by
  have hT :=
    allScaleLiReciprocalState_isPrimeFrequencyState hL
  exact primeFrequencyState_squareRoot_split R hR hT
    (primeFrequencyState_saturated hT)

/-- **Strict reciprocal high-owner contraction.**
On the square endpoint, the entire owner packet above the root costs at most
`log 2` times a bound for the smaller diagonal children. -/
theorem norm_allScaleLiReciprocalState_squareRoot_highTail_le
    {L : ℕ → ℕ → ℂ}
    (R : ℕ) (B : ℝ)
    (hR : 2 ≤ R) (hL : IsAllScaleLiState L) (hB : 0 ≤ B)
    (hdiag : ∀ d : ℕ, d < R →
      ‖allScaleLiReciprocalState L d d‖ ≤ B) :
    ‖allScaleLiReciprocalState L (squareRootEndpoint R) R -
        allScaleLiReciprocalState L
          (squareRootEndpoint R) (squareRootEndpoint R)‖ ≤
      Real.log 2 * B := by
  have hsplit :=
    allScaleLiReciprocalState_squareRoot_split R hR hL
  have hdiff :
      allScaleLiReciprocalState L (squareRootEndpoint R) R -
          allScaleLiReciprocalState L
            (squareRootEndpoint R) (squareRootEndpoint R) =
        ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          reciprocalLiFrequencyWeight q *
            allScaleLiReciprocalState L
              (squareRootEndpoint R / q) (squareRootEndpoint R / q) := by
    rw [hsplit]
    ring
  rw [hdiff]
  calc
    ‖∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
        reciprocalLiFrequencyWeight q *
          allScaleLiReciprocalState L
            (squareRootEndpoint R / q) (squareRootEndpoint R / q)‖
        ≤ ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
            ‖reciprocalLiFrequencyWeight q *
              allScaleLiReciprocalState L
                (squareRootEndpoint R / q) (squareRootEndpoint R / q)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          ‖reciprocalLiFrequencyWeight q‖ * B := by
      apply Finset.sum_le_sum
      intro q hq
      rcases Finset.mem_Ioc.mp hq with ⟨hRq, hqX⟩
      have hqpos : 0 < q := by omega
      have hXltRsq : squareRootEndpoint R < R ^ 2 := by
        unfold squareRootEndpoint
        have hpos : 0 < R ^ 2 := by positivity
        omega
      have hRsqLt : R ^ 2 < R * q := by
        nlinarith
      have hchild : squareRootEndpoint R / q < R := by
        apply (Nat.div_lt_iff_lt_mul hqpos).2
        exact hXltRsq.trans hRsqLt
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (hdiag (squareRootEndpoint R / q) hchild)
        (norm_nonneg _)
    _ = (∑ q ∈ Finset.Ioc R (squareRootEndpoint R),
          ‖reciprocalLiFrequencyWeight q‖) * B := by
      rw [Finset.sum_mul]
    _ ≤ Real.log 2 * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact reciprocalLiFrequencyWeight_norm_sum_rootSquare_le_log_two
        hR (Nat.sub_le (R ^ 2) 1)

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


/-- The diagonal critical prefix is exactly the fixed-cutoff weighted
first-coordinate prefix. -/
theorem allScaleLiCriticalPrefix_eq_fixedCutoffWeighted
    {L : ℕ → ℕ → ℂ} (N : ℕ)
    (hsat : PrimeFrequencySaturated L) :
    allScaleLiCriticalPrefix L N =
      weightedForwardDifferencePrefix criticalSqrtWeight
        (fun n => L n N) N := by
  unfold allScaleLiCriticalPrefix weightedForwardDifferencePrefix
    allScaleLiDiagonalIncrement criticalSqrtWeight
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  have hpredN : n - 1 ≤ N := (Nat.sub_le n 1).trans hnN
  change (L n n - L (n - 1) (n - 1)) /
      (Real.sqrt (n : ℝ) : ℂ) =
    (Real.sqrt (n : ℝ) : ℂ)⁻¹ * (L n N - L (n - 1) N)
  rw [hsat n N hnN, hsat (n - 1) N hpredN]
  rw [div_eq_mul_inv]
  ring

/-- State-only form of the same identification; no separate saturation
hypothesis is needed. -/
theorem allScaleLiCriticalPrefix_eq_fixedCutoffWeighted_of_state
    {L : ℕ → ℕ → ℂ} (N : ℕ) (hL : IsAllScaleLiState L) :
    allScaleLiCriticalPrefix L N =
      weightedForwardDifferencePrefix criticalSqrtWeight
        (fun n => L n N) N := by
  exact allScaleLiCriticalPrefix_eq_fixedCutoffWeighted N
    (primeFrequencyState_saturated hL)



/-- Reciprocal-weighted prefix of the diagonal increments. -/
def allScaleLiReciprocalPrefix
    (L : ℕ → ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    allScaleLiDiagonalIncrement L n / (n : ℂ)

/-- The diagonal reciprocal prefix is exactly the fixed-cutoff reciprocal
first-coordinate prefix. -/
theorem allScaleLiReciprocalPrefix_eq_fixedCutoffWeighted
    {L : ℕ → ℕ → ℂ} (N : ℕ)
    (hsat : PrimeFrequencySaturated L) :
    allScaleLiReciprocalPrefix L N =
      weightedForwardDifferencePrefix reciprocalWeight
        (fun n => L n N) N := by
  unfold allScaleLiReciprocalPrefix weightedForwardDifferencePrefix
    allScaleLiDiagonalIncrement reciprocalWeight
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  have hpredN : n - 1 ≤ N := (Nat.sub_le n 1).trans hnN
  change (L n n - L (n - 1) (n - 1)) / (n : ℂ) =
    ((n : ℂ))⁻¹ * (L n N - L (n - 1) N)
  rw [hsat n N hnN, hsat (n - 1) N hpredN, div_eq_mul_inv]
  ring

/-- State-only form of the reciprocal-prefix identification. -/
theorem allScaleLiReciprocalPrefix_eq_fixedCutoffWeighted_of_state
    {L : ℕ → ℕ → ℂ} (N : ℕ) (hL : IsAllScaleLiState L) :
    allScaleLiReciprocalPrefix L N =
      weightedForwardDifferencePrefix reciprocalWeight
        (fun n => L n N) N := by
  exact allScaleLiReciprocalPrefix_eq_fixedCutoffWeighted N
    (primeFrequencyState_saturated hL)

/-- On the diagonal, the reciprocal/Dickman state is exactly one plus the
reciprocal-weighted diagonal prefix. -/
theorem allScaleLiReciprocalState_diagonal_eq
    {L : ℕ → ℕ → ℂ} (N : ℕ) (hL : IsAllScaleLiState L) :
    allScaleLiReciprocalState L N N =
      1 + allScaleLiReciprocalPrefix L N := by
  unfold allScaleLiReciprocalState
  rw [allScaleLiReciprocalPrefix_eq_fixedCutoffWeighted_of_state N hL]

/-- On the diagonal, the transformed state is exactly one plus the critical
half-weighted prefix. -/
theorem allScaleLiCriticalState_diagonal_eq
    {L : ℕ → ℕ → ℂ} (N : ℕ) (hL : IsAllScaleLiState L) :
    allScaleLiCriticalState L N N =
      1 + allScaleLiCriticalPrefix L N := by
  unfold allScaleLiCriticalState
  rw [allScaleLiCriticalPrefix_eq_fixedCutoffWeighted_of_state N hL]

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

/-- A zero-target degree-two transfer certificate.
At each square-root endpoint, the discrete/reference error is decomposed into
at most the endpoint number of local errors, and their total degree-two energy
about zero is uniformly bounded.  This is deliberately not centered at a
mean. -/
def AllScaleLiZeroTargetDegreeTwoTransfer (M : ℕ → ℂ) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧
    ∀ (L : ℕ → ℕ → ℂ) (R : ℕ),
      IsAllScaleLiState L →
      PrimeFrequencySaturated L →
      2 ≤ R →
      ∃ (s : Finset ℕ) (e : ℕ → ℂ),
        L (squareRootEndpoint R) (squareRootEndpoint R) -
            M (squareRootEndpoint R) =
          ∑ i ∈ s, e i ∧
        (s.card : ℝ) ≤ (squareRootEndpoint R : ℝ) ∧
        zeroTargetComplexDegreeTwoEnergy s e ≤ E

/-- **Zero-target partial-moment closure.**
A bounded reference plus a uniformly bounded degree-two error-energy
certificate about target zero proves the intrinsic all-scale Li square-root
theorem.  The proof works directly at squared scale; no mean, variance
decomposition, or square-root extraction is used. -/
theorem allScaleLiSquareRootBounded_of_uniformReference_zeroTargetDegreeTwoTransfer
    (M : ℕ → ℂ)
    (hM : UniformReferenceDiagonalBounded M)
    (hT : AllScaleLiZeroTargetDegreeTwoTransfer M) :
    AllScaleLiSquareRootBoundedStatement := by
  rcases hM with ⟨B, hB, hMb⟩
  rcases hT with ⟨E, hE, hT⟩
  refine ⟨2 * E + 2 * B ^ 2, by positivity, ?_⟩
  intro L R hL hsat hR
  rcases hT L R hL hsat hR with ⟨s, e, hdecomp, hcard, henergy⟩
  have henergy0 : 0 ≤ zeroTargetComplexDegreeTwoEnergy s e :=
    zeroTargetComplexDegreeTwoEnergy_nonneg s e
  have hX0 : 0 ≤ (squareRootEndpoint R : ℝ) := by positivity
  have hXleR2 :
      (squareRootEndpoint R : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast (Nat.sub_le (R ^ 2) 1)
  have hdiffSq :
      ‖L (squareRootEndpoint R) (squareRootEndpoint R) -
          M (squareRootEndpoint R)‖ ^ 2 ≤
        E * (R : ℝ) ^ 2 := by
    rw [hdecomp]
    calc
      ‖∑ i ∈ s, e i‖ ^ 2
          ≤ (s.card : ℝ) * zeroTargetComplexDegreeTwoEnergy s e :=
            norm_finset_sum_sq_le_card_mul_zeroTargetComplexDegreeTwoEnergy s e
      _ ≤ (squareRootEndpoint R : ℝ) * E := by
            exact mul_le_mul hcard henergy henergy0 hX0
      _ ≤ (R : ℝ) ^ 2 * E :=
            mul_le_mul_of_nonneg_right hXleR2 hE
      _ = E * (R : ℝ) ^ 2 := by ring
  have hM_sq :
      ‖M (squareRootEndpoint R)‖ ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hMb (squareRootEndpoint R)) 2
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  have hR2 : (1 : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
  have hBscale : B ^ 2 ≤ B ^ 2 * (R : ℝ) ^ 2 := by
    calc
      B ^ 2 = B ^ 2 * 1 := by ring
      _ ≤ B ^ 2 * (R : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hR2 (sq_nonneg B)
  have hM_sq_scale :
      ‖M (squareRootEndpoint R)‖ ^ 2 ≤
        B ^ 2 * (R : ℝ) ^ 2 :=
    hM_sq.trans hBscale
  have htri :
      ‖L (squareRootEndpoint R) (squareRootEndpoint R)‖ ≤
        ‖L (squareRootEndpoint R) (squareRootEndpoint R) -
            M (squareRootEndpoint R)‖ +
          ‖M (squareRootEndpoint R)‖ := by
    calc
      ‖L (squareRootEndpoint R) (squareRootEndpoint R)‖ =
          ‖(L (squareRootEndpoint R) (squareRootEndpoint R) -
              M (squareRootEndpoint R)) +
            M (squareRootEndpoint R)‖ := by
              congr 1
              ring
      _ ≤ _ := norm_add_le _ _
  have htriSq :=
    pow_le_pow_left₀
      (norm_nonneg (L (squareRootEndpoint R) (squareRootEndpoint R)))
      htri 2
  have hab :
      (‖L (squareRootEndpoint R) (squareRootEndpoint R) -
            M (squareRootEndpoint R)‖ +
          ‖M (squareRootEndpoint R)‖) ^ 2 ≤
        2 * ‖L (squareRootEndpoint R) (squareRootEndpoint R) -
              M (squareRootEndpoint R)‖ ^ 2 +
          2 * ‖M (squareRootEndpoint R)‖ ^ 2 := by
    nlinarith [sq_nonneg
      (‖L (squareRootEndpoint R) (squareRootEndpoint R) -
          M (squareRootEndpoint R)‖ -
        ‖M (squareRootEndpoint R)‖)]
  calc
    ‖L (squareRootEndpoint R) (squareRootEndpoint R)‖ ^ 2
        ≤ (‖L (squareRootEndpoint R) (squareRootEndpoint R) -
              M (squareRootEndpoint R)‖ +
            ‖M (squareRootEndpoint R)‖) ^ 2 := htriSq
    _ ≤ 2 * ‖L (squareRootEndpoint R) (squareRootEndpoint R) -
              M (squareRootEndpoint R)‖ ^ 2 +
          2 * ‖M (squareRootEndpoint R)‖ ^ 2 := hab
    _ ≤ 2 * (E * (R : ℝ) ^ 2) +
          2 * (B ^ 2 * (R : ℝ) ^ 2) := by
            nlinarith
    _ = (2 * E + 2 * B ^ 2) * (R : ℝ) ^ 2 := by ring

/-- The concrete bounded Dickman reference reduces the remaining pure-Li
problem to one zero-target degree-two transfer certificate. -/
theorem allScaleLiSquareRootBounded_of_exactLiDickman_zeroTargetDegreeTwoTransfer
    (hT :
      AllScaleLiZeroTargetDegreeTwoTransfer
        exactLiDickmanIntegerReference) :
    AllScaleLiSquareRootBoundedStatement :=
  allScaleLiSquareRootBounded_of_uniformReference_zeroTargetDegreeTwoTransfer
    exactLiDickmanIntegerReference
    exactLiDickmanIntegerReference_isUniformlyBounded hT

/-! ## Correct critical-weighted reference transfer -/

/-- Half-weighted forward-difference prefix of an arbitrary sampled reference.
This is the same critical coordinate used by the all-scale Li state. -/
def sampledCriticalPrefix (M : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (M n - M (n - 1)) / (Real.sqrt (n : ℝ) : ℂ)

/-- The sampled critical prefix of the Poisson reference is exactly the
critical cumulative of the stabilized Poisson coefficients, with the unit
atom omitted because the artificial zero endpoint already contains that atom. -/
theorem sampledCriticalPrefix_exactLiPoissonIntegerReference_eq
    (N : ℕ) :
    sampledCriticalPrefix exactLiPoissonIntegerReference N =
      ∑ n ∈ Finset.Icc 2 N,
        exactLiPoissonCoefficient n /
          (Real.sqrt (n : ℝ) : ℂ) := by
  by_cases hN : N = 0
  · subst N
    have hleft :
        sampledCriticalPrefix exactLiPoissonIntegerReference 0 = 0 := by
      unfold sampledCriticalPrefix
      rw [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1)]
      rfl
    have hright :
        (∑ n ∈ Finset.Icc 2 0,
          exactLiPoissonCoefficient n /
            (Real.sqrt (n : ℝ) : ℂ)) = 0 := by
      rw [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 2)]
      rfl
    rw [hleft, hright]
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  have hIcc :
      Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : 1 ∉ Finset.Icc 2 N := by
    intro hmem
    have htwo : 2 ≤ (1 : ℕ) := (Finset.mem_Icc.mp hmem).1
    omega
  have hfirst :
      (exactLiPoissonIntegerReference 1 -
          exactLiPoissonIntegerReference (1 - 1)) /
          (Real.sqrt ((1 : ℕ) : ℝ) : ℂ) = 0 := by
    simp
  unfold sampledCriticalPrefix
  rw [hIcc, Finset.sum_insert hnot, hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [exactLiPoissonIntegerReference_sub_pred_eq_coefficient hn2]

/-- **Exact critical Poisson reduction.**
The native sampled critical prefix of the original Poisson reference is
literally the cumulative transformed-owner Poisson product minus its unit atom.
No inequality or endpoint approximation occurs here. -/
theorem sampledCriticalPrefix_exactLiPoissonIntegerReference_eq_critical
    (N : ℕ) :
    sampledCriticalPrefix exactLiPoissonIntegerReference N =
      exactLiCriticalPoissonIntegerReference N - 1 := by
  by_cases hN0 : N = 0
  · subst N
    have hleft :
        sampledCriticalPrefix exactLiPoissonIntegerReference 0 = 0 := by
      unfold sampledCriticalPrefix
      rw [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1)]
      rfl
    rw [hleft, exactLiCriticalPoissonIntegerReference_zero]
    ring
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  rw [sampledCriticalPrefix_exactLiPoissonIntegerReference_eq]
  have hterms :
      (∑ n ∈ Finset.Icc 2 N,
          exactLiPoissonCoefficient n /
            (Real.sqrt (n : ℝ) : ℂ)) =
        ∑ n ∈ Finset.Icc 2 N,
          arithmeticPoissonProduct criticalLiFrequencyWeight (N - 1) n := by
    apply Finset.sum_congr rfl
    intro n hnmem
    rcases Finset.mem_Icc.mp hnmem with ⟨hn2, hnN⟩
    exact exactLiPoissonCoefficient_div_sqrt_eq_critical_cutoff
      (by omega) hnN
  rw [hterms]
  unfold exactLiCriticalPoissonIntegerReference
  rw [if_pos hN]
  unfold arithmeticCoefficientCumulative
  have hset :
      Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : 1 ∉ Finset.Icc 2 N := by
    intro hmem
    have : 2 ≤ (1 : ℕ) := (Finset.mem_Icc.mp hmem).1
    omega
  have hone :
      arithmeticPoissonProduct criticalLiFrequencyWeight (N - 1) 1 = 1 := by
    have hs :=
      arithmeticPoissonProduct_apply_stable
        criticalLiFrequencyWeight (n := 1) (X := N) (by omega) hN
    simpa [arithmeticPoissonProduct] using hs
  rw [hset, Finset.sum_insert hnot, hone]
  ring

/-- One-step form of the sampled critical prefix. -/
theorem sampledCriticalPrefix_succ
    (M : ℕ → ℂ) (N : ℕ) :
    sampledCriticalPrefix M (N + 1) =
      sampledCriticalPrefix M N +
        (M (N + 1) - M N) /
          (Real.sqrt ((N + 1 : ℕ) : ℝ) : ℂ) := by
  unfold sampledCriticalPrefix
  rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1)]
  simp only [Nat.add_sub_cancel]

/-- The square-root Abel increment of a sampled critical prefix recovers the
original sampled increment exactly. -/
theorem sqrtAbelIncrement_sampledCriticalPrefix
    (M : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    sqrtAbelIncrement (sampledCriticalPrefix M) n =
      M n - M (n - 1) := by
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hs := sampledCriticalPrefix_succ M (n - 1)
  rw [hpred] at hs
  unfold sqrtAbelIncrement
  rw [hs]
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsqrtne : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hsqrtpos)
  field_simp [hsqrtne]
  ring

private theorem sum_Icc_sampledForwardDiff_complex
    (M : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (M n - M (n - 1))) =
      M N - M 0 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1), ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- Uniform boundedness of the native half-weighted sampled increment prefix. -/
def SampledCriticalPrefixBounded (M : ℕ → ℂ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧
    ∀ N : ℕ, ‖sampledCriticalPrefix M N‖ ≤ B

/-- A uniformly bounded sampled critical prefix returns an exact square-root
bound for the sampled reference.  This is the reverse Abel direction needed
for the Poisson close. -/
theorem squareRootReferenceBounded_of_sampledCriticalPrefixBounded
    (M : ℕ → ℂ)
    (hcrit : SampledCriticalPrefixBounded M) :
    SquareRootReferenceBounded M := by
  rcases hcrit with ⟨B, hB, hcrit⟩
  refine ⟨2 * B + ‖M 0‖, by positivity, ?_⟩
  intro N hN
  have hprefix :
      ∀ n : ℕ, n ≤ N → ‖sampledCriticalPrefix M n‖ ≤ B := by
    intro n hn
    exact hcrit n
  have habel :=
    norm_sum_sqrtAbelIncrement_le
      (sampledCriticalPrefix M) N B hN hB hprefix
  have hsum :
      (∑ n ∈ Finset.Icc 1 N,
          sqrtAbelIncrement (sampledCriticalPrefix M) n) =
        M N - M 0 := by
    calc
      (∑ n ∈ Finset.Icc 1 N,
          sqrtAbelIncrement (sampledCriticalPrefix M) n) =
          ∑ n ∈ Finset.Icc 1 N, (M n - M (n - 1)) := by
            apply Finset.sum_congr rfl
            intro n hnmem
            exact sqrtAbelIncrement_sampledCriticalPrefix M
              (Finset.mem_Icc.mp hnmem).1
      _ = M N - M 0 :=
        sum_Icc_sampledForwardDiff_complex M N
  rw [hsum] at habel
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hM0scale :
      ‖M 0‖ ≤ ‖M 0‖ * Real.sqrt (N : ℝ) := by
    calc
      ‖M 0‖ = ‖M 0‖ * 1 := by ring
      _ ≤ ‖M 0‖ * Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrt1 (norm_nonneg _)
  calc
    ‖M N‖ = ‖(M N - M 0) + M 0‖ := by
      congr 1
      ring
    _ ≤ ‖M N - M 0‖ + ‖M 0‖ := norm_add_le _ _
    _ ≤ 2 * Real.sqrt (N : ℝ) * B + ‖M 0‖ :=
      add_le_add habel le_rfl
    _ ≤ 2 * B * Real.sqrt (N : ℝ) +
          ‖M 0‖ * Real.sqrt (N : ℝ) := by
      have hreorder :
          2 * Real.sqrt (N : ℝ) * B =
            2 * B * Real.sqrt (N : ℝ) := by ring
      rw [hreorder]
      exact add_le_add le_rfl hM0scale
    _ = (2 * B + ‖M 0‖) * Real.sqrt (N : ℝ) := by ring

/-- Abel summation for the sampled critical prefix. -/
theorem sampledCriticalPrefix_eq_abel
    (M : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    sampledCriticalPrefix M N =
      M N / (Real.sqrt (N : ℝ) : ℂ) - M 0 +
        ∑ n ∈ Finset.Ico 1 N,
          M n * (((Real.sqrt (n : ℝ))⁻¹ -
            (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) := by
  cases N with
  | zero =>
      omega
  | succ N =>
      induction N with
      | zero =>
          norm_num [sampledCriticalPrefix]
      | succ N ih =>
          have hN1 : 1 ≤ N + 1 := by omega
          have hstep :
              sampledCriticalPrefix M (N + 2) =
                sampledCriticalPrefix M (N + 1) +
                  (M (N + 2) - M (N + 1)) /
                    (Real.sqrt ((N + 2 : ℕ) : ℝ) : ℂ) := by
            unfold sampledCriticalPrefix
            rw [Finset.sum_Icc_succ_top
              (by omega : (1 : ℕ) ≤ N + 2)]
            simp only [Nat.add_sub_cancel]
          rw [hstep, ih hN1, Finset.sum_Ico_succ_top hN1]
          simp only [div_eq_mul_inv]
          push_cast
          ring

/-- A uniformly bounded sampled reference has a uniformly bounded critical
prefix.  This is the correct Abel normalization: no unweighted increment
energy is required. -/
theorem norm_sampledCriticalPrefix_le_two_mul
    (M : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hM : ∀ n : ℕ, ‖M n‖ ≤ B)
    (N : ℕ) :
    ‖sampledCriticalPrefix M N‖ ≤ 2 * B := by
  by_cases hN0 : N = 0
  · subst N
    simp [sampledCriticalPrefix, hB]
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  rw [sampledCriticalPrefix_eq_abel M hN]
  have hsNpos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast (Nat.pos_of_ne_zero hN0))
  have hinvN : 0 ≤ (Real.sqrt (N : ℝ))⁻¹ := by positivity
  have hinvNle : (Real.sqrt (N : ℝ))⁻¹ ≤ 1 := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hsN1 : 1 ≤ Real.sqrt (N : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hNR
    exact inv_le_one_of_one_le₀ hsN1
  have hstep : ∀ n ∈ Finset.Ico 1 N,
      0 ≤ (Real.sqrt (n : ℝ))⁻¹ -
        (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have hsqrtnp : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
      Real.sqrt_pos.2 hnp
    exact sub_nonneg.mpr
      ((inv_le_inv₀ hsqrtnp hsqrtn).2
        (Real.sqrt_le_sqrt (by norm_num)))
  have htel :
      (∑ n ∈ Finset.Ico 1 N,
        ((Real.sqrt (n : ℝ))⁻¹ -
          (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)) =
        1 - (Real.sqrt (N : ℝ))⁻¹ := by
    have hf := sum_Ico_forwardDiff_real
      (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) hN
    calc
      _ = -(∑ n ∈ Finset.Ico 1 N,
          ((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ -
            (Real.sqrt (n : ℝ))⁻¹)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro n hn
            ring
      _ = _ := by rw [hf]; norm_num
  calc
    ‖M N / (Real.sqrt (N : ℝ) : ℂ) - M 0 +
        ∑ n ∈ Finset.Ico 1 N,
          M n * (((Real.sqrt (n : ℝ))⁻¹ -
            (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)‖
        ≤ ‖M N / (Real.sqrt (N : ℝ) : ℂ)‖ + ‖M 0‖ +
          ∑ n ∈ Finset.Ico 1 N,
            ‖M n * (((Real.sqrt (n : ℝ))⁻¹ -
              (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)‖ := by
          calc
            _ ≤ ‖M N / (Real.sqrt (N : ℝ) : ℂ) - M 0‖ +
                ‖∑ n ∈ Finset.Ico 1 N,
                  M n * (((Real.sqrt (n : ℝ))⁻¹ -
                    (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)‖ :=
              norm_add_le _ _
            _ ≤ (‖M N / (Real.sqrt (N : ℝ) : ℂ)‖ + ‖M 0‖) +
                ∑ n ∈ Finset.Ico 1 N,
                  ‖M n * (((Real.sqrt (n : ℝ))⁻¹ -
                    (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)‖ := by
              gcongr
              · exact norm_sub_le _ _
              · exact norm_sum_le _ _
    _ ≤ B * (Real.sqrt (N : ℝ))⁻¹ + B +
          B * (1 - (Real.sqrt (N : ℝ))⁻¹) := by
          have hhead :
              ‖M N / (Real.sqrt (N : ℝ) : ℂ)‖ ≤
                B * (Real.sqrt (N : ℝ))⁻¹ := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hsNpos, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (hM N) hinvN
          have htail :
              (∑ n ∈ Finset.Ico 1 N,
                ‖M n * (((Real.sqrt (n : ℝ))⁻¹ -
                  (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)‖) ≤
                B * (1 - (Real.sqrt (N : ℝ))⁻¹) := by
            calc
              _ ≤ ∑ n ∈ Finset.Ico 1 N,
                  B * ((Real.sqrt (n : ℝ))⁻¹ -
                    (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) := by
                apply Finset.sum_le_sum
                intro n hn
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (hstep n hn)]
                exact mul_le_mul_of_nonneg_right (hM n) (hstep n hn)
              _ = B * (1 - (Real.sqrt (N : ℝ))⁻¹) := by
                rw [← Finset.mul_sum, htel]
          exact add_le_add (add_le_add hhead (hM 0)) htail
    _ = 2 * B := by ring

/-- Correctly normalized discrete-to-reference transfer target: the difference
of critical half-weighted increment prefixes is uniformly bounded. -/
def AllScaleLiCriticalReferenceTransferBounded (M : ℕ → ℂ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ (L : ℕ → ℕ → ℂ) (N : ℕ),
      IsAllScaleLiState L →
      ‖allScaleLiCriticalPrefix L N - sampledCriticalPrefix M N‖ ≤ A

/-- A bounded sampled reference plus bounded critical transfer closes the
critical prefix, hence the pure Li square-root theorem. -/
theorem allScaleLiCriticalPrefixBounded_of_referenceTransfer
    (M : ℕ → ℂ)
    (hM : UniformReferenceDiagonalBounded M)
    (hT : AllScaleLiCriticalReferenceTransferBounded M) :
    AllScaleLiCriticalPrefixBoundedStatement := by
  rcases hM with ⟨B, hB, hMb⟩
  rcases hT with ⟨A, hA, hTb⟩
  refine ⟨A + 2 * B, by positivity, ?_⟩
  intro L N hL
  have hdiff := hTb L N hL
  have href := norm_sampledCriticalPrefix_le_two_mul M B hB hMb N
  calc
    ‖allScaleLiCriticalPrefix L N‖ =
        ‖(allScaleLiCriticalPrefix L N - sampledCriticalPrefix M N) +
          sampledCriticalPrefix M N‖ := by
            congr 1
            ring
    _ ≤ ‖allScaleLiCriticalPrefix L N - sampledCriticalPrefix M N‖ +
          ‖sampledCriticalPrefix M N‖ := norm_add_le _ _
    _ ≤ A + 2 * B := add_le_add hdiff href

/-- Concrete Dickman-reference critical transfer is the single correctly
normalized assembly statement that remains to close the pure Li model. -/
def ExactLiDickmanCriticalTransferBounded : Prop :=
  AllScaleLiCriticalReferenceTransferBounded
    exactLiDickmanIntegerReference

theorem allScaleLiSquareRootBounded_of_exactLiDickmanCriticalTransfer
    (hT : ExactLiDickmanCriticalTransferBounded) :
    AllScaleLiSquareRootBoundedStatement :=
  allScaleLiSquareRootBounded_of_criticalPrefixBounded
    (allScaleLiCriticalPrefixBounded_of_referenceTransfer
      exactLiDickmanIntegerReference
      exactLiDickmanIntegerReference_isUniformlyBounded hT)


/-! ## Canonical zero-target increment transfer -/

/-- One increment of the sampled continuous Dickman reference. -/
def exactLiDickmanIntegerReferenceIncrement (n : ℕ) : ℂ :=
  exactLiDickmanIntegerReference n -
    exactLiDickmanIntegerReference (n - 1)

/-- Canonical local discrete/continuous error at target zero: the difference
between one discrete all-scale Li diagonal increment and the corresponding
sampled Dickman-reference increment. -/
def allScaleLiDickmanIncrementError
    (L : ℕ → ℕ → ℂ) (n : ℕ) : ℂ :=
  allScaleLiDiagonalIncrement L n -
    exactLiDickmanIntegerReferenceIncrement n

@[simp] theorem exactLiDickmanIntegerReference_zero :
    exactLiDickmanIntegerReference 0 = 1 := by
  simp [exactLiDickmanIntegerReference]

/-- Finite forward differences telescope from 1 through N. -/
private theorem sum_Icc_forwardDiff_complex
    (F : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (F n - F (n - 1))) =
      F N - F 0 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1), ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- **Exact canonical error telescope.**
The sum of the zero-target local increment errors is exactly the endpoint
difference between the discrete all-scale Li state and the sampled continuous
Dickman reference. -/
theorem sum_allScaleLiDickmanIncrementError_eq
    {L : ℕ → ℕ → ℂ} (N : ℕ) (hL : IsAllScaleLiState L) :
    (∑ n ∈ Finset.Icc 1 N, allScaleLiDickmanIncrementError L n) =
      L N N - exactLiDickmanIntegerReference N := by
  unfold allScaleLiDickmanIncrementError
    exactLiDickmanIntegerReferenceIncrement
  rw [Finset.sum_sub_distrib,
    sum_allScaleLiDiagonalIncrement_eq L N,
    sum_Icc_forwardDiff_complex exactLiDickmanIntegerReference N,
    allScaleLiState_zero_zero hL,
    exactLiDickmanIntegerReference_zero]
  ring

/-- An intentionally strong *conditional* increment-error certificate.
This unweighted l2 statement is not used as the primary pure-Li target:
the critical closure below uses the native n^(-1/2) normalization.  It is kept
only as a valid sufficient interface when supplied independently. -/
def AllScaleLiDickmanIncrementErrorEnergyBounded : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧
    ∀ (L : ℕ → ℕ → ℂ) (N : ℕ),
      IsAllScaleLiState L →
      zeroTargetComplexDegreeTwoEnergy
        (Finset.Icc 1 N) (allScaleLiDickmanIncrementError L) ≤ E

/-- A uniform bound on the canonical zero-target increment energy produces the
exact degree-two transfer certificate consumed by the final Li closure. -/
theorem allScaleLiZeroTargetDegreeTwoTransfer_of_incrementErrorEnergyBounded
    (hE : AllScaleLiDickmanIncrementErrorEnergyBounded) :
    AllScaleLiZeroTargetDegreeTwoTransfer
      exactLiDickmanIntegerReference := by
  rcases hE with ⟨E, hE0, hbound⟩
  refine ⟨E, hE0, ?_⟩
  intro L R hL hsat hR
  let X : ℕ := squareRootEndpoint R
  have hX1 : 1 ≤ X := by
    dsimp [X, squareRootEndpoint]
    have hR2 : 4 ≤ R ^ 2 := by nlinarith
    omega
  refine ⟨Finset.Icc 1 X, allScaleLiDickmanIncrementError L, ?_, ?_, ?_⟩
  · simpa [X] using (sum_allScaleLiDickmanIncrementError_eq X hL).symm
  · rw [Nat.card_Icc]
    have hcard : X + 1 - 1 = X := by omega
    rw [hcard]
  · exact hbound L X hL

/-- **Over-strong conditional increment-energy endgame.**
The implication is valid, but its premise is deliberately not claimed
unconditionally; the native critical-weighted transfer below is the correct
model-side closure target. -/
theorem allScaleLiSquareRootBounded_of_incrementErrorEnergyBounded
    (hE : AllScaleLiDickmanIncrementErrorEnergyBounded) :
    AllScaleLiSquareRootBoundedStatement :=
  allScaleLiSquareRootBounded_of_exactLiDickman_zeroTargetDegreeTwoTransfer
    (allScaleLiZeroTargetDegreeTwoTransfer_of_incrementErrorEnergyBounded hE)

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
