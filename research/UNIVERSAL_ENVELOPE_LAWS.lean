import «research.UNIVERSAL_ENVELOPE_ARITHMETIC»
import «research.UNIVERSAL_ENVELOPE_ZERO_FORCED»

/-!
# The all-scale historical envelope and its exact exponent dictionary

The upper envelope follows from the already identified Mertens growth
boundary.  Its lower envelope comes from an actual zeta zero, through the
proved zero-forced historical estimate.  A zero arbitrarily close to the
supremum is selected only after the positive exponent tolerance is fixed.

The resulting constants are uniform in the integer root but need not be
effective.  The dictionary includes every positive exponent loss; it does
not assert a fixed bound at the boundary exponent or uniform finite A.
-/

noncomputable section

namespace RHLean.Analysis.UniversalEnvelope

open Filter RHLean.Proof RHLean.Analysis.MertensExponent

/-- Excess of the actual zero boundary above the critical line.  The maximum
retains the repository's formal convention for an empty zero set. -/
def envelopeExponent : ℝ := max zetaRightmostRealPart (1 / 2) - 1 / 2

theorem envelopeExponent_nonneg : 0 ≤ envelopeExponent := by
  dsimp [envelopeExponent]
  linarith [le_max_right zetaRightmostRealPart (1 / 2 : ℝ)]

/-- The original Mertens growth bound at the actual, possibly unattained,
zero boundary with the harmless critical-line maximum. -/
theorem growthAtMost_envelope_boundary :
    MertensGrowthAtMost (1 / 2 + envelopeExponent) := by
  apply (growthAtMost_iff_rightmost_le
    (by linarith [envelopeExponent_nonneg] : 0 ≤ 1 / 2 + envelopeExponent)).mpr
  dsimp [envelopeExponent]
  linarith [le_max_left zetaRightmostRealPart (1 / 2 : ℝ)]

/-- A strict lower approximation to the zero supremum has an actual zero
witness.  The nonnegative cutoff also handles the empty-set convention. -/
theorem exists_zero_above_of_lt_rightmost {a : ℝ} (ha : 0 ≤ a)
    (hlt : a < zetaRightmostRealPart) :
    ∃ ρ : ℂ, NontrivialZetaZero ρ ∧ a < ρ.re := by
  by_contra hnone
  push Not at hnone
  have hsup : zetaRightmostRealPart ≤ a := by
    apply Real.sSup_le _ ha
    rintro x ⟨ρ, hρ, rfl⟩
    exact hnone ρ hρ
  exact (not_le_of_gt hlt) hsup

/-- Uniform upper power envelope on the original strict-history maximum. -/
theorem historical_upper_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 1 ≤ R →
      squareRootHistoricalK R ≤ C * (R : ℝ) ^ (2 * envelopeExponent + ε) := by
  obtain ⟨C, hC, hM⟩ := growthAtMost_envelope_boundary (ε / 2) (by linarith)
  refine ⟨(C + 1) ^ 2, by positivity, ?_⟩
  intro R _hR
  have h := historical_le_of_power
    (by linarith [envelopeExponent_nonneg] :
      (1 / 2 : ℝ) ≤ (1 / 2 + envelopeExponent) + ε / 2) hC hM R
  have hexp : 2 * ((1 / 2 + envelopeExponent) + ε / 2) - 1 =
      2 * envelopeExponent + ε := by ring
  simpa only [hexp] using h

/-- Every positive tolerance admits an eventual lower power envelope at all
integer scales.  Its zero witness and constant are chosen before the scale. -/
theorem historical_lower_power (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ R : ℕ in atTop,
      c * (R : ℝ) ^ (2 * envelopeExponent - ε) ≤ squareRootHistoricalK R := by
  by_cases hhalf : zetaRightmostRealPart ≤ (1 / 2 : ℝ)
  · have hh : envelopeExponent = 0 := by
      simp only [envelopeExponent, max_eq_right hhalf, sub_self]
    refine ⟨1, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with R hR
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hp : (R : ℝ) ^ (2 * envelopeExponent - ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hR1 (by rw [hh]; linarith)
    simpa only [one_mul] using hp.trans (squareRootHistoricalK_one_le hR)
  · have hθ : (1 / 2 : ℝ) < zetaRightmostRealPart := lt_of_not_ge hhalf
    let a : ℝ := max (1 / 2) (zetaRightmostRealPart - ε / 2)
    have ha0 : 0 ≤ a := by
      dsimp [a]
      exact (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (le_max_left _ _)
    have halt : a < zetaRightmostRealPart := by
      dsimp [a]
      exact max_lt hθ (by linarith)
    obtain ⟨ρ, hρ, haρ⟩ := exists_zero_above_of_lt_rightmost ha0 halt
    have hβ : (1 / 2 : ℝ) < ρ.re := (le_max_left _ _).trans_lt haρ
    have hnear : zetaRightmostRealPart - ε / 2 < ρ.re :=
      (le_max_right _ _).trans_lt haρ
    obtain ⟨c, hc, hlower⟩ := zero_forces_historical_power hρ.1 hβ hρ.2.2
    refine ⟨c, hc, ?_⟩
    filter_upwards [hlower, eventually_ge_atTop (1 : ℕ)] with R hlow hR
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hexp : 2 * envelopeExponent - ε ≤ 2 * ρ.re - 1 := by
      dsimp [envelopeExponent]
      rw [max_eq_left hθ.le]
      linarith
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hR1 hexp) hc.le).trans hlow

/-- Absorb the finite initial range of the lower power envelope using the
proved baseline K_R >= 1.  This equivalent form is convenient for consumers. -/
theorem historical_power_le_scaled (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ R : ℕ, 1 ≤ R →
      (R : ℝ) ^ (2 * envelopeExponent - ε) ≤ D * squareRootHistoricalK R := by
  obtain ⟨c, hc, hlower⟩ := historical_lower_power ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hlower
  let P : ℝ := ((N + 1 : ℕ) : ℝ) ^ max (2 * envelopeExponent - ε) 0
  have hP : 0 < P := Real.rpow_pos_of_pos (by positivity) _
  have hcInv : 0 < c⁻¹ := inv_pos.mpr hc
  refine ⟨c⁻¹ + P, by positivity, ?_⟩
  intro R hR
  have hK0 := squareRootHistoricalK_nonneg R
  by_cases hNR : N ≤ R
  · have hlarge : (R : ℝ) ^ (2 * envelopeExponent - ε) ≤
        c⁻¹ * squareRootHistoricalK R := by
      calc
        (R : ℝ) ^ (2 * envelopeExponent - ε) ≤ squareRootHistoricalK R / c :=
          (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hN R hNR)
        _ = c⁻¹ * squareRootHistoricalK R := by rw [div_eq_mul_inv, mul_comm]
    exact hlarge.trans (mul_le_mul_of_nonneg_right (by linarith only [hP]) hK0)
  · have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hRN : (R : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show R ≤ N + 1 by omega)
    have hsmall : (R : ℝ) ^ (2 * envelopeExponent - ε) ≤ P := by
      calc
        (R : ℝ) ^ (2 * envelopeExponent - ε) ≤
            (R : ℝ) ^ max (2 * envelopeExponent - ε) 0 :=
          Real.rpow_le_rpow_of_exponent_le hR1 (le_max_left _ _)
        _ ≤ P := Real.rpow_le_rpow (Nat.cast_nonneg R) hRN (le_max_right _ _)
    exact hsmall.trans ((le_mul_of_one_le_right hP.le
      (squareRootHistoricalK_one_le hR)).trans
        (mul_le_mul_of_nonneg_right (by linarith only [hcInv]) hK0))

/-- Centered endpoint upper power at the actual common growth boundary. -/
theorem centered_endpoint_upper_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 2 ≤ R →
      ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤
        C * (R : ℝ) ^ (1 + 2 * envelopeExponent + ε) := by
  obtain ⟨C, hC, hM⟩ := growthAtMost_envelope_boundary (ε / 2) (by linarith)
  refine ⟨C + 1, by linarith, ?_⟩
  intro R hR
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
  have hRsq : 1 ≤ R ^ 2 := by
    simpa using Nat.pow_le_pow_left (show 1 ≤ R by omega) 2
  have he : squareRootEndpoint R + 1 = R ^ 2 := by
    unfold squareRootEndpoint
    omega
  have h := centered_le_succ_power
    (by linarith [envelopeExponent_nonneg] :
      0 ≤ (1 / 2 + envelopeExponent) + ε / 2) hC hM (squareRootEndpoint R)
  have hpow : (((squareRootEndpoint R + 1 : ℕ) : ℝ) ^
      ((1 / 2 + envelopeExponent) + ε / 2)) =
      (R : ℝ) ^ (1 + 2 * envelopeExponent + ε) := by
    rw [he, Nat.cast_pow, ← Real.rpow_natCast (R : ℝ) 2, ← Real.rpow_mul hR0.le]
    congr 1
    ring
  simpa only [hpow] using h

/-- Exact quantitative sufficiency of the exponent balance.  It also covers
the critical universal case lam=2, eta=0 without division by 2-lam. -/
theorem envelopeBound_of_balance {lam eta : ℝ} (hlam : 0 ≤ lam)
    (hbalance : (2 - lam) * envelopeExponent ≤ eta) :
    EnvelopeBound lam eta := by
  intro ε hε
  let δ : ℝ := ε / (lam + 2)
  have hlam2 : 0 < lam + 2 := by linarith
  have hδ : 0 < δ := div_pos hε hlam2
  have hδeq : (lam + 2) * δ = ε := by
    dsimp [δ]
    field_simp [hlam2.ne']
  obtain ⟨A, hA, hendpoint⟩ := centered_endpoint_upper_power δ hδ
  obtain ⟨D, hD, hhistory⟩ := historical_power_le_scaled δ hδ
  refine ⟨A * D ^ (lam / 2), by positivity, ?_⟩
  intro R hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
  have hR0 : (0 : ℝ) < (R : ℝ) := by linarith
  have hKpow : (R : ℝ) ^ ((2 * envelopeExponent - δ) * (lam / 2)) ≤
      D ^ (lam / 2) * (squareRootHistoricalK R) ^ (lam / 2) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hR0.le _)
      (hhistory R (by omega)) (by linarith : 0 ≤ lam / 2)
    rw [← Real.rpow_mul hR0.le,
      Real.mul_rpow hD.le (squareRootHistoricalK_nonneg R)] at h
    exact h
  have hexp : 1 + 2 * envelopeExponent + δ ≤
      (1 + eta + ε) + (2 * envelopeExponent - δ) * (lam / 2) := by
    nlinarith only [hbalance, hδeq, hε]
  calc
    ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤
        A * (R : ℝ) ^ (1 + 2 * envelopeExponent + δ) := hendpoint R hR
    _ ≤ A * (R : ℝ) ^
        ((1 + eta + ε) + (2 * envelopeExponent - δ) * (lam / 2)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR1 hexp) hA.le
    _ = A * (R : ℝ) ^ (1 + eta + ε) *
        (R : ℝ) ^ ((2 * envelopeExponent - δ) * (lam / 2)) := by
      rw [Real.rpow_add hR0]
      ring
    _ ≤ A * (R : ℝ) ^ (1 + eta + ε) *
        (D ^ (lam / 2) * (squareRootHistoricalK R) ^ (lam / 2)) :=
      mul_le_mul_of_nonneg_left hKpow (by positivity)
    _ = (A * D ^ (lam / 2)) * (R : ℝ) ^ (1 + eta + ε) *
        (squareRootHistoricalK R) ^ (lam / 2) := by ring

/-- ENV-4: the critical historical power holds unconditionally for the
actual Möbius source, with a constant for every positive exponent loss. -/
theorem universal_envelope_bound : EnvelopeBound 2 0 := by
  apply envelopeBound_of_balance (by norm_num : (0 : ℝ) ≤ 2)
  simp

/-- ENV-5: exact bidirectional dictionary with all quantifiers retained. -/
theorem envelopeBound_iff_rightmost_le {lam eta : ℝ}
    (hlam0 : 0 ≤ lam) (hlam2 : lam < 2) (heta : 0 ≤ eta) :
    EnvelopeBound lam eta ↔
      zetaRightmostRealPart ≤ 1 / 2 + eta / (2 - lam) := by
  constructor
  · exact rightmost_le_of_envelopeBound hlam0 hlam2 heta
  · intro hboundary
    apply envelopeBound_of_balance hlam0
    by_cases hhalf : zetaRightmostRealPart ≤ (1 / 2 : ℝ)
    · simpa only [envelopeExponent, max_eq_right hhalf, sub_self, mul_zero] using heta
    · have hθ : (1 / 2 : ℝ) ≤ zetaRightmostRealPart := le_of_lt (lt_of_not_ge hhalf)
      have hden : 0 < 2 - lam := by linarith
      have hratio : zetaRightmostRealPart - 1 / 2 ≤ eta / (2 - lam) := by
        linarith only [hboundary]
      have hproduct := (le_div_iff₀ hden).mp hratio
      dsimp [envelopeExponent]
      rw [max_eq_left hθ]
      nlinarith only [hproduct]

private theorem eventually_log_constant_le (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℕ in atTop,
      2 ≤ R ∧ Real.log C ≤ ε * Real.log (R : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (Real.log C / ε))
  apply Filter.eventually_atTop.2
  refine ⟨max 2 N, ?_⟩
  intro R hR
  have hR2 : 2 ≤ R := (le_max_left _ _).trans hR
  have hNR : (N : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast ((le_max_right 2 N).trans hR)
  have hexp : Real.exp (Real.log C / ε) ≤ (R : ℝ) := hN.le.trans hNR
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  refine ⟨hR2, ?_⟩
  simpa only [mul_comm] using (div_le_iff₀ hε).mp hlog

/-- Every positive loss bounds the logarithmic historical exponent above. -/
theorem historical_log_ratio_eventually_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℕ in atTop,
      Real.log (squareRootHistoricalK R) / Real.log (R : ℝ) ≤
        2 * envelopeExponent + ε := by
  obtain ⟨C, hC, hupper⟩ := historical_upper_power (ε / 2) (by linarith)
  filter_upwards [eventually_log_constant_le C (ε / 2) (by linarith)]
    with R hconstant
  have hR1 : 1 ≤ R := by omega
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
  have hlogR : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hK0 := squareRootHistoricalK_pos hR1
  have hlog := Real.log_le_log hK0 (hupper R hR1)
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hR0 _).ne',
    Real.log_rpow hR0] at hlog
  apply (div_le_iff₀ hlogR).mpr
  nlinarith only [hlog, hconstant.2]

/-- Every positive loss bounds the logarithmic historical exponent below. -/
theorem historical_log_ratio_eventually_ge (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℕ in atTop,
      2 * envelopeExponent - ε ≤
        Real.log (squareRootHistoricalK R) / Real.log (R : ℝ) := by
  obtain ⟨D, hD, hlower⟩ := historical_power_le_scaled (ε / 2) (by linarith)
  filter_upwards [eventually_log_constant_le D (ε / 2) (by linarith)]
    with R hconstant
  have hR1 : 1 ≤ R := by omega
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
  have hlogR : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hK0 := squareRootHistoricalK_pos hR1
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hR0 _) (hlower R hR1)
  rw [Real.log_rpow hR0, Real.log_mul hD.ne' hK0.ne'] at hlog
  apply (le_div_iff₀ hlogR).mpr
  nlinarith only [hlog, hconstant.2]

/-- ENV-3(a): the historical logarithmic exponent has a limit along all
integers, rather than merely a subsequential upper limit. -/
theorem historical_log_ratio_tendsto :
    Tendsto (fun R : ℕ =>
      Real.log (squareRootHistoricalK R) / Real.log (R : ℝ))
      atTop (nhds (2 * envelopeExponent)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have hε : 0 < (2 * envelopeExponent - a) / 2 := by linarith
    filter_upwards [historical_log_ratio_eventually_ge _ hε] with R hR
    linarith only [ha, hR]
  · intro b hb
    have hε : 0 < (b - 2 * envelopeExponent) / 2 := by linarith
    filter_upwards [historical_log_ratio_eventually_le _ hε] with R hR
    linarith only [hb, hR]

end RHLean.Analysis.UniversalEnvelope

end
