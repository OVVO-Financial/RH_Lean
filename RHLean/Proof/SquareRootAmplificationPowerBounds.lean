import RHLean.Proof.SquareRootAmplificationLogGrowth

/-!
# Power bounds for the original historical amplification

This module transports a power bound for the actual integer Mertens sum to
the original centered endpoint ratio and its exact running maximum.  The
only denominator estimate used is the proved `squareRootHistoricalK_one_le`.
The centering by one and every admitted square endpoint are retained.

If `|M(n)| <= C * n^b` with `b >= 1/2`, the resulting power is `2*b-1`
and an explicit admissible constant is `(C+1)^2`.  The logarithmic ratio is
bounded by that power plus a constant divided by `log X`.  In particular,
every fixed Mertens power below one makes the original running maximum
strictly less than `X` eventually.  These statements do not assert zero
logarithmic growth at a positive resulting power.
-/

noncomputable section

open Filter

namespace RHLean.Proof

/-- The original centering costs at most one more copy of the power envelope. -/
theorem mertensCentered_abs_le_of_power {b C : ℝ} (hb : 0 ≤ b)
    (hM : ∀ n : ℕ, 1 ≤ n →
      |(mertensSummatoryInt n : ℝ)| ≤ C * (n : ℝ) ^ b)
    (n : ℕ) (hn : 1 ≤ n) :
    |((mertensSummatoryInt n - 1 : ℤ) : ℝ)| ≤ (C + 1) * (n : ℝ) ^ b := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ b := Real.one_le_rpow hn1 hb
  rw [Int.cast_sub, Int.cast_one]
  calc
    |(mertensSummatoryInt n : ℝ) - 1| ≤
        |(mertensSummatoryInt n : ℝ)| + |(1 : ℝ)| := abs_sub _ _
    _ = |(mertensSummatoryInt n : ℝ)| + 1 := by norm_num
    _ ≤ C * (n : ℝ) ^ b + (n : ℝ) ^ b := add_le_add (hM n hn) hpow
    _ = (C + 1) * (n : ℝ) ^ b := by ring

/-- A Mertens power bound controls the literal centered endpoint quotient. -/
theorem squareRootEndpointAmplification_le_of_mertensPower {b C : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n →
      |(mertensSummatoryInt n : ℝ)| ≤ C * (n : ℝ) ^ b)
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootEndpointAmplification R ≤
      (C + 1) ^ 2 * (squareRootEndpoint R : ℝ) ^ (2 * b - 1) := by
  have hR2 : 4 ≤ R ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hR hR
  have hn : 1 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hn1 : (1 : ℝ) ≤ (squareRootEndpoint R : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (squareRootEndpoint R : ℝ) := by linarith
  have hnRnat : squareRootEndpoint R ≤ R ^ 2 := Nat.sub_le _ _
  have hnR : (squareRootEndpoint R : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast hnRnat
  have hK : 1 ≤ squareRootHistoricalK R := squareRootHistoricalK_one_le (by omega)
  have hnK : (squareRootEndpoint R : ℝ) ≤
      (R : ℝ) ^ 2 * squareRootHistoricalK R :=
    hnR.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hK (sq_nonneg (R : ℝ)))
  have hcenter := mertensCentered_abs_le_of_power (by linarith : 0 ≤ b)
    hM (squareRootEndpoint R) hn
  have hboundNonneg : 0 ≤ (C + 1) * (squareRootEndpoint R : ℝ) ^ b :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hsquare : (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) ≤
      ((C + 1) * (squareRootEndpoint R : ℝ) ^ b) ^ 2 := by
    calc
      _ = |((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)| ^ 2 :=
        (sq_abs _).symm
      _ ≤ _ := (sq_le_sq₀ (abs_nonneg _) hboundNonneg).2 hcenter
  have hrpow : ((squareRootEndpoint R : ℝ) ^ b) ^ 2 =
      (squareRootEndpoint R : ℝ) ^ (2 * b - 1) * (squareRootEndpoint R : ℝ) := by
    rw [pow_two, ← Real.rpow_add hnpos]
    rw [show b + b = (2 * b - 1) + 1 by ring, Real.rpow_add_one hnpos.ne']
  apply (squareRootEndpointAmplification_le_iff (by omega) _).2
  calc
    _ ≤ ((C + 1) * (squareRootEndpoint R : ℝ) ^ b) ^ 2 := hsquare
    _ = (C + 1) ^ 2 *
        ((squareRootEndpoint R : ℝ) ^ (2 * b - 1) * (squareRootEndpoint R : ℝ)) := by
      rw [mul_pow, hrpow]
    _ = ((C + 1) ^ 2 * (squareRootEndpoint R : ℝ) ^ (2 * b - 1)) *
        (squareRootEndpoint R : ℝ) := by ring
    _ ≤ ((C + 1) ^ 2 * (squareRootEndpoint R : ℝ) ^ (2 * b - 1)) *
        ((R : ℝ) ^ 2 * squareRootHistoricalK R) :=
      mul_le_mul_of_nonneg_left hnK
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    _ = (C + 1) ^ 2 * (squareRootEndpoint R : ℝ) ^ (2 * b - 1) *
        (R : ℝ) ^ 2 * squareRootHistoricalK R := by ring

/-- One constant bounds every admitted endpoint through the cutoff. -/
theorem squareRootAmplificationMax_le_of_mertensPower {b C : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n →
      |(mertensSummatoryInt n : ℝ)| ≤ C * (n : ℝ) ^ b)
    (X : ℕ) (hX : 1 ≤ X) :
    squareRootAmplificationMax X ≤ (C + 1) ^ 2 * (X : ℝ) ^ (2 * b - 1) := by
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  apply (squareRootAmplificationMax_le_iff X _).2
  refine ⟨mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ X) _), ?_⟩
  intro R hR hRX
  have hpow : (squareRootEndpoint R : ℝ) ^ (2 * b - 1) ≤
      (X : ℝ) ^ (2 * b - 1) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hRX) (by linarith)
  exact (squareRootEndpointAmplification_le_of_mertensPower hb hC hM R hR).trans
    (mul_le_mul_of_nonneg_left hpow (sq_nonneg _))

/-- The logarithmic cost of a fixed power-envelope constant is explicit. -/
theorem squareRootAmplificationLogRatio_le_of_powerBound {a D : ℝ}
    (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hA : ∀ X : ℕ, 1 ≤ X →
      squareRootAmplificationMax X ≤ D * (X : ℝ) ^ a)
    (X : ℕ) (hX : 2 ≤ X) :
    squareRootAmplificationLogRatio X ≤ a + Real.log (1 + D) / Real.log (X : ℝ) := by
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hDpos : 0 < 1 + D := by linarith
  have hpow : (1 : ℝ) ≤ (X : ℝ) ^ a := Real.one_le_rpow hX1 ha
  have hupper : 1 + squareRootAmplificationMax X ≤ (1 + D) * (X : ℝ) ^ a := by
    calc
      _ ≤ 1 + D * (X : ℝ) ^ a := by
        have hAX := hA X (by omega)
        linarith only [hAX]
      _ ≤ (X : ℝ) ^ a + D * (X : ℝ) ^ a := by linarith only [hpow]
      _ = (1 + D) * (X : ℝ) ^ a := by ring
  have hpositive : 0 < 1 + squareRootAmplificationMax X := by
    linarith [squareRootAmplificationMax_nonneg X]
  have hlogs := Real.log_le_log hpositive hupper
  rw [Real.log_mul hDpos.ne' (Real.rpow_pos_of_pos hXpos a).ne',
    Real.log_rpow hXpos] at hlogs
  unfold squareRootAmplificationLogRatio
  have hdiv := div_le_div_of_nonneg_right hlogs hlog.le
  simpa only [add_div, mul_div_cancel_right₀ _ hlog.ne', add_comm] using hdiv

/-- Direct logarithmic bound from the actual integer Mertens power estimate. -/
theorem squareRootAmplificationLogRatio_le_of_mertensPower {b C : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n →
      |(mertensSummatoryInt n : ℝ)| ≤ C * (n : ℝ) ^ b)
    (X : ℕ) (hX : 2 ≤ X) :
    squareRootAmplificationLogRatio X ≤
      2 * b - 1 + Real.log (1 + (C + 1) ^ 2) / Real.log (X : ℝ) := by
  exact squareRootAmplificationLogRatio_le_of_powerBound (by linarith) (sq_nonneg _)
    (squareRootAmplificationMax_le_of_mertensPower hb hC hM) X hX

/-- A finite explicit threshold absorbs the logarithmic constant into any
positive additional exponent. -/
theorem squareRootAmplificationLogRatio_le_of_mertensPower_threshold {b C : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n →
      |(mertensSummatoryInt n : ℝ)| ≤ C * (n : ℝ) ^ b)
    (eta : ℝ) (heta : 0 < eta) (X : ℕ) (hX : 2 ≤ X)
    (hthreshold : Real.exp (Real.log (1 + (C + 1) ^ 2) / eta) ≤ (X : ℝ)) :
    squareRootAmplificationLogRatio X ≤ 2 * b - 1 + eta := by
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hthresholdLog : Real.log (1 + (C + 1) ^ 2) / eta ≤ Real.log (X : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hthreshold
    simpa only [Real.log_exp] using h
  have hpayment : Real.log (1 + (C + 1) ^ 2) / Real.log (X : ℝ) ≤ eta := by
    apply (div_le_iff₀ hlog).2
    have h := (div_le_iff₀ heta).1 hthresholdLog
    simpa only [mul_comm] using h
  have hq := squareRootAmplificationLogRatio_le_of_mertensPower hb hC hM X hX
  linarith only [hq, hpayment]

/-- The resulting logarithmic power bound holds eventually with any positive
additional loss, with the source constant fixed before the cutoff. -/
theorem squareRootAmplificationLogRatio_eventually_le_of_mertensPower {b C : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n →
      |(mertensSummatoryInt n : ℝ)| ≤ C * (n : ℝ) ^ b)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ X : ℕ in atTop, squareRootAmplificationLogRatio X ≤ 2 * b - 1 + eta := by
  obtain ⟨X0, hX0⟩ :=
    exists_nat_gt (Real.exp (Real.log (1 + (C + 1) ^ 2) / eta))
  apply Filter.eventually_atTop.2
  refine ⟨max 2 X0, ?_⟩
  intro X hX
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hX0X : (X0 : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast ((le_max_right 2 X0).trans hX)
  exact squareRootAmplificationLogRatio_le_of_mertensPower_threshold hb hC hM
    eta heta X hX2 (hX0.le.trans hX0X)

/-- A logarithmic ratio strictly below one bounds the actual running maximum
strictly below its cutoff. -/
theorem squareRootAmplificationMax_lt_of_logRatio_lt_one
    (X : ℕ) (hX : 2 ≤ X) (hq : squareRootAmplificationLogRatio X < 1) :
    squareRootAmplificationMax X < (X : ℝ) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hpositive : 0 < 1 + squareRootAmplificationMax X := by
    linarith [squareRootAmplificationMax_nonneg X]
  have hlogs : Real.log (1 + squareRootAmplificationMax X) < Real.log (X : ℝ) := by
    have h := (div_lt_iff₀ hlog).1 hq
    simpa only [one_mul] using h
  have h := (Real.log_lt_log_iff hpositive hXpos).1 hlogs
  linarith

/-- Every fixed Mertens exponent below one proves eventual strict sublinearity
of the user's original amplification maximum. -/
theorem squareRootAmplificationMax_eventually_lt_of_mertensPower {b C : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hb1 : b < 1) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n →
      |(mertensSummatoryInt n : ℝ)| ≤ C * (n : ℝ) ^ b) :
    ∀ᶠ X : ℕ in atTop, squareRootAmplificationMax X < (X : ℝ) := by
  have hq := squareRootAmplificationLogRatio_eventually_le_of_mertensPower
    hb hC hM (1 - b) (by linarith)
  filter_upwards [hq, eventually_ge_atTop (2 : ℕ)] with X hbound hX
  apply squareRootAmplificationMax_lt_of_logRatio_lt_one X hX
  linarith

end RHLean.Proof
end
