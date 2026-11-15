import «research.UNIVERSAL_ENVELOPE_LAWS»
import «research.UNIVERSAL_ENVELOPE_HISTORY»
import RHLean.Proof.SquareRootAmplificationPowerBounds

/-!
# The exact exponent of the original amplification maximum

The upper bound combines the universal envelope with the historical upper
power.  The lower bound uses the finite interpolation inequality for the
complete history, together with both historical powers at all sufficiently
large cutoffs.  Thus the conclusion is a limit, not merely a limsup or a
subsequence assertion.  The running maximum and its centering are unchanged.
-/

noncomputable section

namespace RHLean.Analysis.UniversalEnvelope

open Filter RHLean.Proof RHLean.Analysis.MertensExponent
open scoped Topology

/-- Every positive loss gives one simultaneous upper power for all admitted
endpoints.  Its cutoff exponent is `h`, half the historical root exponent. -/
theorem amplification_upper_power (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ, 1 ≤ X →
      squareRootAmplificationMax X ≤ B * (X : ℝ) ^ (envelopeExponent + ε) := by
  have henv : EnvelopeBound 2 0 := envelopeBound_of_balance (by norm_num) (by simp)
  obtain ⟨C, hC, hbound⟩ := henv (ε / 2) (by linarith)
  obtain ⟨D, hD, hhistory⟩ := historical_upper_power ε hε
  let a := envelopeExponent + ε
  have ha : 0 ≤ a := by dsimp [a]; linarith [envelopeExponent_nonneg]
  refine ⟨C ^ 2 * D * (2 : ℝ) ^ a, by positivity, ?_⟩
  intro X hX
  apply (squareRootAmplificationMax_le_iff X _).mpr
  refine ⟨by positivity, ?_⟩
  intro R hR hRX
  have hR1 : 1 ≤ R := by omega
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
  have hK0 := squareRootHistoricalK_nonneg R
  have hcenter : ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤
      C * (R : ℝ) ^ (1 + ε / 2) * squareRootHistoricalK R := by
    simpa using hbound R hR
  have hcenterSq := (sq_le_sq₀ (norm_nonneg _)
    (show 0 ≤ C * (R : ℝ) ^ (1 + ε / 2) * squareRootHistoricalK R by positivity)).mpr hcenter
  have hpowSquare : ((R : ℝ) ^ (1 + ε / 2)) ^ (2 : ℕ) =
      (R : ℝ) ^ ε * (R : ℝ) ^ (2 : ℕ) := by
    rw [pow_two, ← Real.rpow_add hR0]
    rw [show (1 + ε / 2) + (1 + ε / 2) = ε + (2 : ℝ) by ring,
      Real.rpow_add hR0, Real.rpow_natCast (R : ℝ) 2]
  have hroot : (R : ℝ) ^ 2 ≤ 2 * (X : ℝ) := by
    have hs : 1 ≤ R ^ 2 := by nlinarith
    have hnat : R ^ 2 ≤ 2 * X := by unfold squareRootEndpoint at hRX; omega
    exact_mod_cast hnat
  have hpower : (R : ℝ) ^ (2 * a) ≤ (2 : ℝ) ^ a * (X : ℝ) ^ a := by
    calc
      (R : ℝ) ^ (2 * a) = ((R : ℝ) ^ (2 : ℕ)) ^ a := by
        rw [← Real.rpow_natCast (R : ℝ) 2, ← Real.rpow_mul hR0.le]
      _ ≤ (2 * (X : ℝ)) ^ a := Real.rpow_le_rpow (sq_nonneg _) hroot ha
      _ = (2 : ℝ) ^ a * (X : ℝ) ^ a := Real.mul_rpow (by norm_num) (Nat.cast_nonneg X)
  have hcoeff : C ^ 2 * (R : ℝ) ^ ε * squareRootHistoricalK R ≤
      (C ^ 2 * D * (2 : ℝ) ^ a) * (X : ℝ) ^ a := by
    calc
      C ^ 2 * (R : ℝ) ^ ε * squareRootHistoricalK R ≤
          C ^ 2 * (R : ℝ) ^ ε * (D * (R : ℝ) ^ (2 * envelopeExponent + ε)) :=
        mul_le_mul_of_nonneg_left (hhistory R hR1) (by positivity)
      _ = (C ^ 2 * D) * (R : ℝ) ^ (2 * a) := by
        calc
          _ = (C ^ 2 * D) * ((R : ℝ) ^ ε * (R : ℝ) ^ (2 * envelopeExponent + ε)) := by ring
          _ = _ := by rw [← Real.rpow_add hR0]; congr 2; dsimp [a]; ring
      _ ≤ (C ^ 2 * D) * ((2 : ℝ) ^ a * (X : ℝ) ^ a) :=
        mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = _ := by ring
  apply (squareRootEndpointAmplification_le_iff hR1 _).mpr
  rw [← shiftedMertensEnergy_eq_intSquare, shiftedMertensEnergy]
  calc
    ‖mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 ≤
        (C * (R : ℝ) ^ (1 + ε / 2) * squareRootHistoricalK R) ^ 2 := hcenterSq
    _ = (C ^ 2 * (R : ℝ) ^ ε * squareRootHistoricalK R) *
        ((R : ℝ) ^ 2 * squareRootHistoricalK R) := by rw [mul_pow, mul_pow, hpowSquare]; ring
    _ ≤ ((C ^ 2 * D * (2 : ℝ) ^ a) * (X : ℝ) ^ a) *
        ((R : ℝ) ^ 2 * squareRootHistoricalK R) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by ring

/-- The finite complete-history interpolation forces a lower power at every
sufficiently large cutoff, including cutoffs between new record endpoints. -/
theorem amplification_lower_power (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      c * (X : ℝ) ^ (envelopeExponent - ε) ≤ 1 + squareRootAmplificationMax X := by
  obtain ⟨c, hc, hlower⟩ := historical_lower_power (ε / 2) (by linarith)
  obtain ⟨D, hD, hupper⟩ := historical_upper_power ε hε
  let b := envelopeExponent + ε / 2
  let D' := D * (4 : ℝ) ^ b
  have hb : 0 ≤ b := by dsimp [b]; linarith [envelopeExponent_nonneg]
  have hD' : 0 < D' := by dsimp [D']; positivity
  refine ⟨c / (8 * D'), div_pos hc (by positivity), ?_⟩
  filter_upwards [hlower, eventually_ge_atTop (1 : ℕ)] with X hlowerX hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hs0 : (0 : ℝ) < ((Nat.sqrt X + 1 : ℕ) : ℝ) := by positivity
  have hroot : squareRootHistoricalK (Nat.sqrt X + 1) ≤ D' * (X : ℝ) ^ b := by
    calc
      squareRootHistoricalK (Nat.sqrt X + 1) ≤
          D * ((Nat.sqrt X + 1 : ℕ) : ℝ) ^ (2 * envelopeExponent + ε) := hupper _ (by omega)
      _ = D * (((Nat.sqrt X + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ^ b := by
        rw [← Real.rpow_natCast ((Nat.sqrt X + 1 : ℕ) : ℝ) 2, ← Real.rpow_mul hs0.le]
        congr 2
        dsimp [b]
        ring
      _ ≤ D * (4 * (X : ℝ)) ^ b := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (sq_nonneg _) (sqrt_cutoff_square_le hX) hb) hD.le
      _ = D' * (X : ℝ) ^ b := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hX0.le]; dsimp [D']; ring
  have hmax0 := squareRootAmplificationMax_nonneg X
  have htotal : c * (X : ℝ) ^ (2 * envelopeExponent - ε / 2) ≤
      8 * (1 + squareRootAmplificationMax X) * (D' * (X : ℝ) ^ b) :=
    hlowerX.trans ((historical_le_amplification_mul_sqrt_history X).trans
      (mul_le_mul_of_nonneg_left hroot (by positivity)))
  have hsplit : (X : ℝ) ^ (2 * envelopeExponent - ε / 2) =
      (X : ℝ) ^ (envelopeExponent - ε) * (X : ℝ) ^ b := by
    rw [← Real.rpow_add hX0]
    congr 1
    dsimp [b]
    ring
  rw [hsplit] at htotal
  have hcancel : c * (X : ℝ) ^ (envelopeExponent - ε) ≤
      8 * (1 + squareRootAmplificationMax X) * D' := by
    apply (mul_le_mul_right (Real.rpow_pos_of_pos hX0 b)).mp
    nlinarith only [htotal]
  have hdivide : c / (8 * D') * (X : ℝ) ^ (envelopeExponent - ε) =
      (c * (X : ℝ) ^ (envelopeExponent - ε)) / (8 * D') := by ring
  rw [hdivide]
  exact (div_le_iff₀ (show 0 < 8 * D' by positivity)).mpr (by nlinarith only [hcancel])

/-- Taking logarithms preserves the exact `log(1+A(X))/log X` normalization. -/
theorem amplification_logRatio_lower {c a : ℝ} (hc : 0 < c) {X : ℕ}
    (hX : 2 ≤ X)
    (hpower : c * (X : ℝ) ^ a ≤ 1 + squareRootAmplificationMax X) :
    a + Real.log c / Real.log (X : ℝ) ≤ squareRootAmplificationLogRatio X := by
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have h := Real.log_le_log (mul_pos hc (Real.rpow_pos_of_pos hX0 a)) hpower
  rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos hX0 a).ne', Real.log_rpow hX0] at h
  have hdiv := div_le_div_of_nonneg_right h hlog.le
  simpa only [add_div, mul_div_cancel_right₀ _ hlog.ne', add_comm,
    squareRootAmplificationLogRatio] using hdiv

/-- The exact logarithmic amplification law.  This is an unconditional limit
for the original strict-history ratio, with the actual zeta-zero boundary. -/
theorem amplification_logRatio_tendsto :
    Tendsto squareRootAmplificationLogRatio atTop (nhds envelopeExponent) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let ε := (envelopeExponent - a) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨c, hc, hpower⟩ := amplification_lower_power ε hε
    have hconstant : Tendsto (fun X : ℕ => Real.log c / Real.log (X : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hlog
    have hnear := (tendsto_order.mp hconstant).1 (-ε) (by linarith)
    filter_upwards [hpower, hnear, eventually_ge_atTop (2 : ℕ)] with X hXpower hXnear hX
    have hlower := amplification_logRatio_lower hc hX hXpower
    dsimp [ε] at hlower hXnear
    linarith
  · intro b hb
    let ε := (b - envelopeExponent) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨B, hB, hpower⟩ := amplification_upper_power ε hε
    have hconstant : Tendsto (fun X : ℕ => Real.log (1 + B) / Real.log (X : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hlog
    have hnear := (tendsto_order.mp hconstant).2 ε hε
    filter_upwards [hnear, eventually_ge_atTop (2 : ℕ)] with X hXnear hX
    have hupper := squareRootAmplificationLogRatio_le_of_powerBound
      (by linarith [envelopeExponent_nonneg] : 0 ≤ envelopeExponent + ε) hB hpower X hX
    dsimp [ε] at hupper hXnear
    linarith

end RHLean.Analysis.UniversalEnvelope

end
