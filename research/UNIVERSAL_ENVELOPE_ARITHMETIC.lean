import «research.MERTENS_CONVERSE_IDENTIFICATION»
import RHLean.Proof.SquareRootAmplificationClosure
import RHLean.Proof.SquareRootAmplificationLogGrowth

/-!
# The exact historical envelope and its exponent consumer

All envelopes in this file use the original centered Mertens numerator,
the complete-square endpoint, and the strict historical maximum.  Constants
are chosen after the positive exponent loss and before the integer scale.
The exponent implication is proved by an actual arithmetic improvement,
followed by the independently established Mertens/zero-boundary identification.
No lower bound for the historical maximum is assumed in this direction.
-/

noncomputable section

namespace RHLean.Analysis.UniversalEnvelope

open RHLean.Proof RHLean.Analysis.MertensExponent

/-- The every-positive-loss envelope with the original historical maximum. -/
def EnvelopeBound (lam eta : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 2 ≤ R →
      ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤
        C * (R : ℝ) ^ (1 + eta + ε) *
          (squareRootHistoricalK R) ^ (lam / 2)

/-- Centering and inclusion of zero are harmless for a nonnegative power. -/
theorem centered_le_succ_power {b C : ℝ} (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n → ‖mertensSummatory n‖ ≤ C * (n : ℝ) ^ b)
    (n : ℕ) :
    ‖mertensSummatory n - 1‖ ≤ (C + 1) * ((n + 1 : ℕ) : ℝ) ^ b := by
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hone := Real.one_le_rpow hn1 hb
  by_cases hn : n = 0
  · subst n
    simpa using (show (1 : ℝ) ≤ C + 1 by linarith)
  · have hnorm := hM n (by omega)
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg n)
      (show (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ n) hb
    calc
      ‖mertensSummatory n - 1‖ ≤ ‖mertensSummatory n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖mertensSummatory n‖ + 1 := by simp
      _ ≤ C * ((n + 1 : ℕ) : ℝ) ^ b + ((n + 1 : ℕ) : ℝ) ^ b :=
        add_le_add (hnorm.trans (mul_le_mul_of_nonneg_left hp hC)) hone
      _ = (C + 1) * ((n + 1 : ℕ) : ℝ) ^ b := by ring

/-- A Mertens power controls every element of the strict historical maximum. -/
theorem historical_le_of_power {b C : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n → ‖mertensSummatory n‖ ≤ C * (n : ℝ) ^ b)
    (R : ℕ) :
    squareRootHistoricalK R ≤ (C + 1) ^ 2 * (R : ℝ) ^ (2 * b - 1) := by
  apply (squareRootHistoricalK_le_iff R _).mpr
  refine ⟨mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _), ?_⟩
  intro y hy
  have hypos : (0 : ℝ) < ((y + 1 : ℕ) : ℝ) := by positivity
  have hcenter := centered_le_succ_power (by linarith : 0 ≤ b) hC hM y
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by linarith : 0 ≤ C + 1) (Real.rpow_nonneg hypos.le _))).mpr hcenter
  have hidentity : (((y + 1 : ℕ) : ℝ) ^ b) ^ (2 : ℕ) =
      ((y + 1 : ℕ) : ℝ) ^ (2 * b - 1) * ((y + 1 : ℕ) : ℝ) := by
    rw [pow_two, ← Real.rpow_add hypos]
    rw [show b + b = (2 * b - 1) + 1 by ring, Real.rpow_add_one hypos.ne']
  have hpow : ((y + 1 : ℕ) : ℝ) ^ (2 * b - 1) ≤ (R : ℝ) ^ (2 * b - 1) :=
    Real.rpow_le_rpow hypos.le (by exact_mod_cast (show y + 1 ≤ R by omega)) (by linarith)
  rw [← shiftedMertensEnergy_eq_intSquare, shiftedMertensEnergy]
  calc
    ‖mertensSummatory y - 1‖ ^ 2 ≤ ((C + 1) * ((y + 1 : ℕ) : ℝ) ^ b) ^ 2 := hsq
    _ = (C + 1) ^ 2 * (((y + 1 : ℕ) : ℝ) ^ (2 * b - 1) * ((y + 1 : ℕ) : ℝ)) := by
      rw [mul_pow, hidentity]
    _ ≤ (C + 1) ^ 2 * ((R : ℝ) ^ (2 * b - 1) * ((y + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hypos.le) (sq_nonneg _)
    _ = (C + 1) ^ 2 * (R : ℝ) ^ (2 * b - 1) * ((y + 1 : ℕ) : ℝ) := by ring

/-- Complete-square endpoint powers interpolate to all integers using the
unit bound on the Möbius increments.  The half-exponent is the exact threshold
at which the square gap can be absorbed. -/
theorem powerBound_of_square_endpoint_power {b C : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hC : 0 ≤ C)
    (hM : ∀ R : ℕ, 2 ≤ R →
      ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤ C * (R : ℝ) ^ (2 * b)) :
    MertensPowerBound b := by
  refine ⟨2 + (C + 3) * (2 : ℝ) ^ b, by positivity, ?_⟩
  intro n hn
  have hb0 : 0 ≤ b := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpow : (1 : ℝ) ≤ (n : ℝ) ^ b := Real.one_le_rpow hn1 hb0
  by_cases hsmall : n < 3
  · have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (show n ≤ 2 by omega)
    have hc0 : 0 ≤ (C + 3) * (2 : ℝ) ^ b := by positivity
    calc
      ‖mertensSummatory n‖ ≤ (n : ℝ) := mertens_norm_le n
      _ ≤ 2 := hn2
      _ ≤ (2 + (C + 3) * (2 : ℝ) ^ b) * (n : ℝ) ^ b := by nlinarith
  · let R : ℕ := Nat.sqrt (n + 1)
    have hRsq : R ^ 2 ≤ n + 1 := Nat.sqrt_le' (n + 1)
    have hnnext : n + 1 < (R + 1) ^ 2 := Nat.lt_succ_sqrt' (n + 1)
    have hR : 2 ≤ R := by
      by_contra hRsmall
      have hRnext : R + 1 ≤ 2 := by omega
      have hnextBound := Nat.pow_le_pow_left hRnext 2
      norm_num at hnextBound
      omega
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
    have hR0 : (0 : ℝ) < (R : ℝ) := by linarith
    have hRsq1 : 1 ≤ R ^ 2 := by nlinarith
    have he : squareRootEndpoint R ≤ n := by unfold squareRootEndpoint; omega
    have hgapNat : n - squareRootEndpoint R ≤ 2 * R := by
      have hnext : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
      rw [hnext] at hnnext
      unfold squareRootEndpoint
      omega
    have hgap : ‖mertensSummatory n - mertensSummatory (squareRootEndpoint R)‖ ≤ 2 * (R : ℝ) :=
      (norm_mertensSummatory_sub_le _ _ he).trans (by exact_mod_cast hgapNat)
    have hRp : (R : ℝ) ≤ (R : ℝ) ^ (2 * b) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hR1 (show (1 : ℝ) ≤ 2 * b by linarith)
    have hRp1 : (1 : ℝ) ≤ (R : ℝ) ^ (2 * b) := hR1.trans hRp
    have hendpoint := hM R hR
    have hnorm : ‖mertensSummatory n‖ ≤ (C + 3) * (R : ℝ) ^ (2 * b) := by
      calc
        ‖mertensSummatory n‖ =
            ‖(mertensSummatory n - mertensSummatory (squareRootEndpoint R)) +
              (mertensSummatory (squareRootEndpoint R) - 1) + 1‖ := by congr 1; ring
        _ ≤ (‖mertensSummatory n - mertensSummatory (squareRootEndpoint R)‖ +
              ‖mertensSummatory (squareRootEndpoint R) - 1‖) + ‖(1 : ℂ)‖ :=
          (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
        _ ≤ (C + 3) * (R : ℝ) ^ (2 * b) := by simp only [norm_one]; nlinarith
    have hp : (R : ℝ) ^ (2 * b) ≤ (2 : ℝ) ^ b * (n : ℝ) ^ b := by
      calc
        (R : ℝ) ^ (2 * b) = ((R : ℝ) ^ (2 : ℕ)) ^ b := by
          rw [← Real.rpow_natCast (R : ℝ) 2, ← Real.rpow_mul hR0.le]
        _ ≤ ((n + 1 : ℕ) : ℝ) ^ b :=
          Real.rpow_le_rpow (sq_nonneg _) (by exact_mod_cast hRsq) hb0
        _ ≤ (2 * (n : ℝ)) ^ b :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show n + 1 ≤ 2 * n by omega)) hb0
        _ = (2 : ℝ) ^ b * (n : ℝ) ^ b := Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)
    calc
      ‖mertensSummatory n‖ ≤ (C + 3) * (R : ℝ) ^ (2 * b) := hnorm
      _ ≤ (C + 3) * ((2 : ℝ) ^ b * (n : ℝ) ^ b) :=
        mul_le_mul_of_nonneg_left hp (by linarith)
      _ ≤ (2 + (C + 3) * (2 : ℝ) ^ b) * (n : ℝ) ^ b := by nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) b]

/-- One genuine exponent improvement from the historical envelope. -/
theorem growthAtMost_of_envelopeBound {lam eta b : ℝ}
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta) (hb : (1 / 2 : ℝ) ≤ b)
    (henv : EnvelopeBound lam eta) (hgrowth : MertensGrowthAtMost b) :
    MertensGrowthAtMost (1 / 2 + eta / 2 + lam * (b - 1 / 2) / 2) := by
  intro ε hε
  let δ : ℝ := ε / (lam + 1)
  have hlam1 : 0 < lam + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hlam1
  have hδeq : (lam + 1) * δ = ε := by dsimp [δ]; field_simp [hlam1.ne']
  obtain ⟨C, hC, hM⟩ := hgrowth δ hδ
  obtain ⟨A, hA, henvA⟩ := henv δ hδ
  let b' : ℝ := 1 / 2 + eta / 2 + lam * (b - 1 / 2) / 2
  have hb' : (1 / 2 : ℝ) ≤ b' := by dsimp [b']; nlinarith [mul_nonneg hlam (sub_nonneg.mpr hb)]
  apply powerBound_mono (a := b' + ε / 2) (by dsimp [b']; linarith)
  apply powerBound_of_square_endpoint_power (by linarith)
    (C := A * ((C + 1) ^ 2) ^ (lam / 2)) (by positivity)
  intro R hR
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
  have hK := historical_le_of_power (by linarith : (1 / 2 : ℝ) ≤ b + δ) hC hM R
  have hKpow := Real.rpow_le_rpow (squareRootHistoricalK_nonneg R) hK (by linarith : 0 ≤ lam / 2)
  calc
    ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤
        A * (R : ℝ) ^ (1 + eta + δ) * (squareRootHistoricalK R) ^ (lam / 2) := henvA R hR
    _ ≤ A * (R : ℝ) ^ (1 + eta + δ) *
        ((C + 1) ^ 2 * (R : ℝ) ^ (2 * (b + δ) - 1)) ^ (lam / 2) :=
      mul_le_mul_of_nonneg_left hKpow (by positivity)
    _ = (A * ((C + 1) ^ 2) ^ (lam / 2)) * (R : ℝ) ^ (2 * (b' + ε / 2)) := by
      rw [Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg hR0.le _),
        ← Real.rpow_mul hR0.le]
      calc
        _ = (A * ((C + 1) ^ 2) ^ (lam / 2)) *
            ((R : ℝ) ^ (1 + eta + δ) * (R : ℝ) ^ ((2 * (b + δ) - 1) * (lam / 2))) := by ring
        _ = _ := by
          rw [← Real.rpow_add hR0]
          congr 2
          dsimp [b']
          nlinarith only [hδeq]

/-- The envelope forces the advertised zero boundary.  This evaluates the
proved improvement at the actual independently defined boundary; it assumes
neither a numerical sub-one seed nor a desired historical lower bound. -/
theorem rightmost_le_of_envelopeBound {lam eta : ℝ}
    (hlam0 : 0 ≤ lam) (hlam2 : lam < 2) (heta : 0 ≤ eta)
    (h : EnvelopeBound lam eta) :
    zetaRightmostRealPart ≤ 1 / 2 + eta / (2 - lam) := by
  have hden : 0 < 2 - lam := by linarith
  by_cases hhalf : zetaRightmostRealPart ≤ (1 / 2 : ℝ)
  · exact hhalf.trans (le_add_of_nonneg_right (div_nonneg heta hden.le))
  · have hθ : (1 / 2 : ℝ) ≤ zetaRightmostRealPart := le_of_lt (lt_of_not_ge hhalf)
    have hcurrent : MertensGrowthAtMost zetaRightmostRealPart :=
      growthAtMost_of_strip rightmost_nonneg strip_at_rightmost
    have hnext := growthAtMost_of_envelopeBound hlam0 heta hθ h hcurrent
    have hnext0 : 0 ≤ 1 / 2 + eta / 2 + lam * (zetaRightmostRealPart - 1 / 2) / 2 := by
      nlinarith [mul_nonneg hlam0 (sub_nonneg.mpr hθ)]
    have hboundary := (growthAtMost_iff_rightmost_le hnext0).mp hnext
    have hprod : (zetaRightmostRealPart - 1 / 2) * (2 - lam) ≤ eta := by nlinarith
    have hdiv := (le_div_iff₀ hden).mpr hprod
    linarith

/-- The half-exponent implies every nonnegative-loss envelope because the
historical maximum contains its proved baseline one. -/
theorem envelopeBound_of_mertens_half {lam eta : ℝ}
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hhalf : MertensGrowthAtMost (1 / 2 : ℝ)) :
    EnvelopeBound lam eta := by
  intro ε hε
  obtain ⟨C, hC, hM⟩ := hhalf (ε / 2) (by linarith)
  refine ⟨C + 1, by linarith, ?_⟩
  intro R hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
  have hR0 : (0 : ℝ) < (R : ℝ) := by linarith
  have hRsq : 1 ≤ R ^ 2 := by nlinarith
  have he : squareRootEndpoint R + 1 = R ^ 2 := by unfold squareRootEndpoint; omega
  have hcenter := centered_le_succ_power (by linarith : 0 ≤ (1 / 2 : ℝ) + ε / 2) hC hM (squareRootEndpoint R)
  have hepow : (((squareRootEndpoint R + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + ε / 2)) = (R : ℝ) ^ (1 + ε) := by
    rw [he, Nat.cast_pow, ← Real.rpow_natCast (R : ℝ) 2, ← Real.rpow_mul hR0.le]
    congr 1
    ring
  rw [hepow] at hcenter
  have hpow := Real.rpow_le_rpow_of_exponent_le hR1 (show 1 + ε ≤ 1 + eta + ε by linarith)
  have hKpow : 1 ≤ (squareRootHistoricalK R) ^ (lam / 2) :=
    Real.one_le_rpow (squareRootHistoricalK_one_le (by omega)) (by linarith)
  calc
    ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤ (C + 1) * (R : ℝ) ^ (1 + ε) := hcenter
    _ ≤ (C + 1) * (R : ℝ) ^ (1 + eta + ε) := mul_le_mul_of_nonneg_left hpow (by linarith)
    _ ≤ (C + 1) * (R : ℝ) ^ (1 + eta + ε) * (squareRootHistoricalK R) ^ (lam / 2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hKpow
        (show 0 ≤ (C + 1) * (R : ℝ) ^ (1 + eta + ε) by positivity)

/-- At zero additional root power, every subquadratic historical exponent is
equivalent to the Mertens half-exponent. -/
theorem envelopeBound_zero_iff_mertens_half {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam2 : lam < 2) :
    EnvelopeBound lam 0 ↔ MertensGrowthAtMost (1 / 2 : ℝ) := by
  constructor
  · intro h
    apply (growthAtMost_iff_rightmost_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
    simpa using rightmost_le_of_envelopeBound hlam0 hlam2 (by norm_num) h
  · exact envelopeBound_of_mertens_half hlam0 (by norm_num)

end RHLean.Analysis.UniversalEnvelope

end
