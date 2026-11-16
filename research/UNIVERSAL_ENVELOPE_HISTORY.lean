import «research.UNIVERSAL_ENVELOPE_ARITHMETIC»

/-!
# From the endpoint maximum back to the complete historical maximum

The finite inequality in this file supplies the lower-bound direction for
the logarithmic amplification law.  It applies at each cutoff separately;
no uniform amplification assumption and no asymptotic claim is hidden in it.
The gap between adjacent complete-square endpoints is paid using the actual
unit bound for Möbius coefficients.
-/

noncomputable section

namespace RHLean.Analysis.UniversalEnvelope

open RHLean.Proof RHLean.Analysis.MertensExponent

/-- The whole strict history is controlled by the admitted endpoint maximum
and the history at the square-root cutoff.  All maxima are the original ones. -/
theorem historical_le_amplification_mul_sqrt_history (Y : ℕ) :
    squareRootHistoricalK Y ≤
      8 * (1 + squareRootAmplificationMax Y) * squareRootHistoricalK (Nat.sqrt Y + 1) := by
  let A := squareRootAmplificationMax Y
  let K := squareRootHistoricalK (Nat.sqrt Y + 1)
  have hA : 0 ≤ A := squareRootAmplificationMax_nonneg Y
  have hK : 1 ≤ K := squareRootHistoricalK_one_le (by omega)
  have hK0 : 0 ≤ K := by linarith
  apply (squareRootHistoricalK_le_iff Y _).mpr
  refine ⟨by positivity, ?_⟩
  intro y hy
  rw [← shiftedMertensEnergy_eq_intSquare, shiftedMertensEnergy]
  have hy0 : (0 : ℝ) ≤ ((y + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  by_cases hsmall : y < 3
  · have hcenter := norm_shiftedMertens_le_succ y
    have hy3 : ((y + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show y + 1 ≤ 3 by omega)
    have hsq := (sq_le_sq₀ (norm_nonneg _) hy0).mpr hcenter
    have hcoef : 3 ≤ 8 * (1 + A) * K := by nlinarith [mul_nonneg hA hK0]
    calc
      ‖mertensSummatory y - 1‖ ^ 2 ≤ ((y + 1 : ℕ) : ℝ) ^ 2 := hsq
      _ ≤ 3 * ((y + 1 : ℕ) : ℝ) := by nlinarith
      _ ≤ (8 * (1 + A) * K) * ((y + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hcoef hy0
  · let R := Nat.sqrt (y + 1)
    have hRsq : R ^ 2 ≤ y + 1 := Nat.sqrt_le' (y + 1)
    have hynext : y + 1 < (R + 1) ^ 2 := Nat.lt_succ_sqrt' (y + 1)
    have hR : 2 ≤ R := by
      by_contra h
      have hRsmall : R ≤ 1 := by omega
      have hnextsmall : (R + 1) ^ 2 ≤ 4 := by nlinarith
      omega
    have hRsq1 : 1 ≤ R ^ 2 := by nlinarith
    have he : squareRootEndpoint R ≤ y := by unfold squareRootEndpoint; omega
    have hRY : R ≤ Nat.sqrt Y + 1 := by
      have hmono := Nat.sqrt_le_sqrt (show y + 1 ≤ Y by omega)
      dsimp [R]
      omega
    have hKr : squareRootHistoricalK R ≤ K := squareRootHistoricalK_mono hRY
    have hend := (squareRootEndpointAmplification_le_iff (by omega : 1 ≤ R) A).mp
      (squareRootEndpointAmplification_le_max hR (he.trans hy.le))
    have hendpoint : ‖mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 ≤
        A * ((y + 1 : ℕ) : ℝ) * K := by
      rw [← shiftedMertensEnergy_eq_intSquare, shiftedMertensEnergy] at hend
      calc
        ‖mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 ≤ A * (R : ℝ) ^ 2 * squareRootHistoricalK R := hend
        _ ≤ A * (R : ℝ) ^ 2 * K := mul_le_mul_of_nonneg_left hKr (by positivity)
        _ ≤ A * ((y + 1 : ℕ) : ℝ) * K :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by exact_mod_cast hRsq) hA) hK0
    have hgapNat : y - squareRootEndpoint R ≤ 2 * R := by
      have hnext : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
      rw [hnext] at hynext
      unfold squareRootEndpoint
      omega
    have hgap : ‖mertensSummatory y - mertensSummatory (squareRootEndpoint R)‖ ≤ 2 * (R : ℝ) :=
      (norm_mertensSummatory_sub_le _ _ he).trans (by exact_mod_cast hgapNat)
    have hgapSq : ‖mertensSummatory y - mertensSummatory (squareRootEndpoint R)‖ ^ 2 ≤
        4 * ((y + 1 : ℕ) : ℝ) := by
      have hRsqReal : (R : ℝ) ^ 2 ≤ ((y + 1 : ℕ) : ℝ) := by exact_mod_cast hRsq
      nlinarith [norm_nonneg (mertensSummatory y - mertensSummatory (squareRootEndpoint R))]
    have htriangle : ‖mertensSummatory y - 1‖ ≤
        ‖mertensSummatory y - mertensSummatory (squareRootEndpoint R)‖ +
          ‖mertensSummatory (squareRootEndpoint R) - 1‖ := by
      calc
        ‖mertensSummatory y - 1‖ =
            ‖(mertensSummatory y - mertensSummatory (squareRootEndpoint R)) +
              (mertensSummatory (squareRootEndpoint R) - 1)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have htwosq : ‖mertensSummatory y - 1‖ ^ 2 ≤
        2 * ‖mertensSummatory y - mertensSummatory (squareRootEndpoint R)‖ ^ 2 +
          2 * ‖mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 := by
      nlinarith [norm_nonneg (mertensSummatory y - 1),
        norm_nonneg (mertensSummatory y - mertensSummatory (squareRootEndpoint R)),
        norm_nonneg (mertensSummatory (squareRootEndpoint R) - 1),
        sq_nonneg (‖mertensSummatory y - mertensSummatory (squareRootEndpoint R)‖ -
          ‖mertensSummatory (squareRootEndpoint R) - 1‖)]
    have hbase : ((y + 1 : ℕ) : ℝ) ≤ ((y + 1 : ℕ) : ℝ) * K := by nlinarith
    have hAK : 0 ≤ A * ((y + 1 : ℕ) : ℝ) * K := by positivity
    calc
      ‖mertensSummatory y - 1‖ ^ 2 ≤
          8 * ((y + 1 : ℕ) : ℝ) + 2 * (A * ((y + 1 : ℕ) : ℝ) * K) := by nlinarith
      _ ≤ (8 * (1 + A) * K) * ((y + 1 : ℕ) : ℝ) := by nlinarith

/-- The root cutoff is at most twice the real square-root scale, expressed
without a floor or square root on the real side. -/
theorem sqrt_cutoff_square_le {Y : ℕ} (hY : 1 ≤ Y) :
    ((Nat.sqrt Y + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (Y : ℝ) := by
  have hs := Nat.sqrt_le' Y
  have hsY := Nat.sqrt_le_self Y
  have hn : (Nat.sqrt Y + 1) ^ 2 ≤ 4 * Y := by nlinarith
  exact_mod_cast hn

end RHLean.Analysis.UniversalEnvelope

end
