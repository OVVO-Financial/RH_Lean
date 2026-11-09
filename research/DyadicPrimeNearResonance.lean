import Mathlib
import RHLean.Analysis.TwoABPrimeDilation

/-!
# Genuine shared-prime phases need not decorrelate

Formalizes 20261109-wheel-2/DG2, independently accepted in the Referee's
20261109-referee-1/DA E3. The full prime rectangles are retained, including
above-wall products; the two explicit witnesses also satisfy both walls.
This is a Hermitian phase-comparison obstruction, not an estimate for the
nonconjugated prime-discrepancy band or the complete centered wheel.
-/

noncomputable section

namespace RHLean.Analysis

/-- The full cross-root prime rectangle; no floor-half convention is used. -/
def dyadicPrimePair (R p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ R ≤ 2 * p ∧ p < R ∧ R ≤ q ∧ q < 2 * R

/-- Actual physical product admission at the original square-prefix wall. -/
def admittedDyadicPrimePair (R p q : ℕ) : Prop :=
  dyadicPrimePair R p q ∧ p * q ≤ squareRootEndpoint R

/-- Original normalized product phase, retaining the root occurrence label. -/
def dyadicPrimePhase (R p q : ℕ) : ℝ :=
  Real.log ((squareRootEndpoint R : ℝ) / ((p : ℝ) * q))

/-- The phase wave used only for the explicitly Hermitian comparison below. -/
def dyadicPrimePhaseWave (R p q : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((t * dyadicPrimePhase R p q : ℝ) : ℂ) * Complex.I)

private theorem endpoint_cast (R : ℕ) (hR : 1 ≤ R) :
    (squareRootEndpoint R : ℝ) = (R : ℝ) ^ 2 - 1 := by
  have hsq : 1 ≤ R ^ 2 := by nlinarith
  simp only [squareRootEndpoint, Nat.cast_sub hsq, Nat.cast_pow, Nat.cast_one]

/-- Exact shared-prime cancellation, with all denominators positive. -/
theorem dyadicPrimePhase_shared (R p q r : ℕ) (hR : 2 ≤ R)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    dyadicPrimePhase R p q - dyadicPrimePhase (2 * R) q r =
      Real.log ((((R : ℝ) ^ 2 - 1) * r) /
        ((4 * (R : ℝ) ^ 2 - 1) * p)) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hR' : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hX : 0 < (R : ℝ) ^ 2 - 1 := by nlinarith
  have hY : 0 < ((2 : ℝ) * R) ^ 2 - 1 := by nlinarith
  unfold dyadicPrimePhase
  rw [endpoint_cast R (by omega), endpoint_cast (2 * R) (by omega)]
  push_cast
  rw [← Real.log_div (ne_of_gt (div_pos hX (mul_pos hp' hq')))
    (ne_of_gt (div_pos hY (mul_pos hq' hr')))]
  congr 1
  field_simp
  <;> ring

private theorem abs_log_of_relative_error {R z : ℝ}
    (hR : 1 < R) (hz : 0 < z) (he : |z - 1| ≤ 1 / R) :
    |Real.log z| ≤ 1 / (R - 1) := by
  have hR0 : 0 < R := by linarith
  have hRm : 0 < R - 1 := by linarith
  have hsmall : 1 - z ≤ 1 / R := by linarith [(abs_le.mp he).1]
  have hsmallR := (le_div_iff₀ hR0).mp hsmall
  have hinv : z⁻¹ ≤ R / (R - 1) := by
    rw [← one_div]
    apply (div_le_div_iff₀ hz hRm).mpr
    nlinarith
  have hfrac : R / (R - 1) - 1 = 1 / (R - 1) := by
    field_simp
    <;> ring
  have hupper : 1 / R ≤ 1 / (R - 1) := by
    apply (div_le_div_iff₀ hR0 hRm).mpr
    linarith
  apply abs_le.mpr
  constructor
  · linarith [Real.one_sub_inv_le_log_of_pos hz]
  · exact (Real.log_le_sub_one_of_pos hz).trans
      ((abs_le.mp he).2.trans hupper)

/-- The quantitative estimate is real-variable and needs no prime hypothesis. -/
theorem sharedPrime_ratio_bounds (R p r : ℝ) (hR : 8 ≤ R)
    (hp : R ≤ 2 * p) (hpR : p ≤ R)
    (hstep : r = 4 * p - 1 ∨ r = 4 * p + 1) :
    Real.log (((R ^ 2 - 1) * r) / ((4 * R ^ 2 - 1) * p)) ≠ 0 ∧
      |Real.log (((R ^ 2 - 1) * r) / ((4 * R ^ 2 - 1) * p))| ≤
        1 / (R - 1) := by
  have hR0 : 0 < R := by linarith
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by rcases hstep with h | h <;> linarith
  have hX : 0 < R ^ 2 - 1 := by nlinarith
  have hY : 0 < 4 * R ^ 2 - 1 := by nlinarith
  have hD : 0 < (4 * R ^ 2 - 1) * p := mul_pos hY hp0
  have hz : 0 < ((R ^ 2 - 1) * r) / ((4 * R ^ 2 - 1) * p) :=
    div_pos (mul_pos hX hr0) hD
  have hnum : |(R ^ 2 - 1) * r - (4 * R ^ 2 - 1) * p| ≤
      R ^ 2 - 1 + 3 * p := by
    rcases hstep with h | h <;> rw [h, abs_le] <;> constructor <;> nlinarith
  have hfactor : 0 ≤ 4 * R ^ 2 - 3 * R - 1 := by nlinarith
  have hprod := mul_nonneg (show 0 ≤ 2 * p - R by linarith) hfactor
  have hbase : 0 ≤ R * (2 * R - 1) * (R - 1) :=
    mul_nonneg (mul_nonneg hR0.le (by linarith)) (by linarith)
  have hden : R * (R ^ 2 - 1 + 3 * p) ≤ (4 * R ^ 2 - 1) * p := by
    nlinarith
  have he : |((R ^ 2 - 1) * r) / ((4 * R ^ 2 - 1) * p) - 1| ≤
      1 / R := by
    rw [show ((R ^ 2 - 1) * r) / ((4 * R ^ 2 - 1) * p) - 1 =
        ((R ^ 2 - 1) * r - (4 * R ^ 2 - 1) * p) /
          ((4 * R ^ 2 - 1) * p) by field_simp; ring]
    rw [abs_div, abs_of_pos hD]
    apply (div_le_div_iff₀ hD hR0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hnum hR0.le]
  constructor
  · apply Real.log_ne_zero_of_pos_of_ne_one hz
    intro h
    have heq := (div_eq_one_iff_eq hD.ne').mp h
    have hthree : 3 * p < R ^ 2 - 1 := by nlinarith [sq_nonneg (R - 4)]
    rcases hstep with h | h <;> rw [h] at heq <;> nlinarith
  · exact abs_log_of_relative_error (by linarith) hz he

private theorem cosine_bound_of_phase {R d t : ℝ} (hR : 8 ≤ R)
    (hd : |d| ≤ 1 / (R - 1)) (ht : t ^ 2 ≤ 4 * R) :
    1 - 2 * R / (R - 1) ^ 2 ≤ Real.cos (t * d) ∧
      (33 : ℝ) / 49 ≤ Real.cos (t * d) := by
  have hRm : 0 < R - 1 := by linarith
  have hd2 : d ^ 2 ≤ (1 / (R - 1)) ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hd)
      (add_nonneg (show 0 ≤ 1 / (R - 1) by positivity) (abs_nonneg d))
    nlinarith [sq_abs d]
  have htd : (t * d) ^ 2 ≤ 4 * R / (R - 1) ^ 2 := by
    have h := mul_le_mul ht hd2 (sq_nonneg d) (show 0 ≤ 4 * R by linarith)
    simpa only [mul_pow, div_pow, one_pow, mul_one_div] using h
  have hc := Real.one_sub_sq_div_two_le_cos (x := t * d)
  have hfirst : 1 - 2 * R / (R - 1) ^ 2 ≤ Real.cos (t * d) := by
    nlinarith
  have hratio : 2 * R / (R - 1) ^ 2 ≤ (16 : ℝ) / 49 := by
    apply (div_le_iff₀ (sq_pos_of_pos hRm)).mpr
    nlinarith [mul_nonneg (show 0 ≤ R - 8 by linarith)
      (show 0 ≤ 8 * R - 1 by linarith)]
  exact ⟨hfirst, by linarith⟩

/-- Uniform distinct-phase obstruction on the full genuine prime rectangles. -/
theorem dyadicPrimePhase_near_resonance (R p q r : ℕ) (hR : 8 ≤ R)
    (hpq : dyadicPrimePair R p q) (hqr : dyadicPrimePair (2 * R) q r)
    (hstep : r + 1 = 4 * p ∨ r = 4 * p + 1) :
    dyadicPrimePhase R p q ≠ dyadicPrimePhase (2 * R) q r ∧
      ∀ t : ℝ, t ^ 2 ≤ 4 * R →
        (1 - 2 * R / ((R : ℝ) - 1) ^ 2 ≤
          Real.cos (t * (dyadicPrimePhase R p q - dyadicPrimePhase (2 * R) q r)) ∧
        (33 : ℝ) / 49 ≤
          Real.cos (t * (dyadicPrimePhase R p q - dyadicPrimePhase (2 * R) q r))) := by
  have hR' : (8 : ℝ) ≤ R := by exact_mod_cast hR
  have hp' : (R : ℝ) ≤ 2 * p := by exact_mod_cast hpq.2.2.1
  have hpR : (p : ℝ) ≤ R := by exact_mod_cast hpq.2.2.2.1.le
  have hs : (r : ℝ) = 4 * p - 1 ∨ (r : ℝ) = 4 * p + 1 := by
    rcases hstep with h | h
    · have h' : (r : ℝ) + 1 = 4 * p := by exact_mod_cast h
      exact Or.inl (by linarith)
    · exact Or.inr (by exact_mod_cast h)
  have hb := sharedPrime_ratio_bounds (R : ℝ) (p : ℝ) (r : ℝ) hR' hp' hpR hs
  have heq := dyadicPrimePhase_shared R p q r (by omega)
    hpq.1.pos hpq.2.1.pos hqr.2.1.pos
  constructor
  · intro h
    apply hb.1
    rw [← heq, h, sub_self]
  · intro t ht
    apply cosine_bound_of_phase hR' _ ht
    rwa [heq]

/-- The cosine is exactly the real Hermitian cross-phase response. -/
theorem dyadicPrimePhase_hermitian_eq_cos (R p q r : ℕ) (t : ℝ) :
    (dyadicPrimePhaseWave R p q t *
      star (dyadicPrimePhaseWave (2 * R) q r t)).re =
      Real.cos (t * (dyadicPrimePhase R p q - dyadicPrimePhase (2 * R) q r)) := by
  simp [dyadicPrimePhaseWave, Complex.exp_mul_I, Complex.mul_re, Real.cos_sub, mul_sub]

/-- Both occurrences in the first witness are actual admitted prime products. -/
theorem dyadicPrimeNearResonance_eight_admitted :
    admittedDyadicPrimePair 8 5 11 ∧ admittedDyadicPrimePair 16 11 19 := by
  norm_num [admittedDyadicPrimePair, dyadicPrimePair, squareRootEndpoint]

/-- A second, independent scale has the same genuine shared-prime structure. -/
theorem dyadicPrimeNearResonance_sixtyFour_admitted :
    admittedDyadicPrimePair 64 37 67 ∧ admittedDyadicPrimePair 128 67 149 := by
  norm_num [admittedDyadicPrimePair, dyadicPrimePair, squareRootEndpoint]

/-- A kernel-certified counterexample to nonpositive distinct-phase response.
The symmetric time range is stronger than the requested [sqrt R,2 sqrt R]. -/
theorem dyadicPrimeNearResonance_counterexample :
    ∃ R p q r : ℕ, 8 ≤ R ∧ admittedDyadicPrimePair R p q ∧
      admittedDyadicPrimePair (2 * R) q r ∧
      dyadicPrimePhase R p q ≠ dyadicPrimePhase (2 * R) q r ∧
      ∀ t : ℝ, |t| ≤ 2 * Real.sqrt R →
        (33 : ℝ) / 49 ≤ (dyadicPrimePhaseWave R p q t *
          star (dyadicPrimePhaseWave (2 * R) q r t)).re := by
  obtain ⟨hpq, hqr⟩ := dyadicPrimeNearResonance_eight_admitted
  have h := dyadicPrimePhase_near_resonance 8 5 11 19 (by omega)
    hpq.1 hqr.1 (by omega)
  refine ⟨8, 5, 11, 19, by omega, hpq, hqr, h.1, ?_⟩
  intro t ht
  have ht2 : t ^ 2 ≤ 4 * (8 : ℝ) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
    have hn := Real.sqrt_nonneg (8 : ℝ)
    have hm := mul_nonneg (sub_nonneg.mpr ht)
      (add_nonneg (by positivity : 0 ≤ 2 * Real.sqrt (8 : ℝ)) (abs_nonneg t))
    nlinarith [sq_abs t]
  rw [dyadicPrimePhase_hermitian_eq_cos]
  exact (h.2 t ht2).2

end RHLean.Analysis
