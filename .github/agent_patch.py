from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNTHasAffineEnvelope_arbitrarily_small' not in s
marker = '\nend RHLean.Analysis\n'
assert s.count(marker) == 1
block = r'''

/-! ## Closing the affine-envelope contraction -/

/-- **Arbitrarily small affine slope.**  The quadratic density of good fibres
and the strict affine-envelope improvement may be iterated at one fixed
positive floor `beta`.  The excess slope above `beta` is multiplied by
`1 - c/4` at each step, hence tends geometrically to zero. -/
theorem nativePNTHasAffineEnvelope_arbitrarily_small
    (eta : ℝ) (heta : 0 < eta) :
    nativePNTHasAffineEnvelope eta := by
  by_cases h6 : 6 ≤ eta
  · rcases nativePNTHasAffineEnvelope_six with ⟨D, hD, henv⟩
    refine ⟨D, hD, ?_⟩
    intro N
    have hscale : 6 * (N : ℝ) ≤ eta * (N : ℝ) :=
      mul_le_mul_of_nonneg_right h6 (by positivity)
    exact (henv N).trans (add_le_add_right hscale D)
  · have heta6 : eta < 6 := lt_of_not_ge h6
    let beta : ℝ := eta / 12
    have hbeta : 0 < beta := by
      dsimp [beta]
      positivity
    have hbetaEta : beta < eta := by
      dsimp [beta]
      nlinarith
    have hbeta1 : beta ≤ 1 := by
      dsimp [beta]
      nlinarith
    rcases nativeLambdaTwoGoodRecipMass_eventually_quadratic
        beta hbeta hbeta1 with ⟨c, hc, hc1, hgood⟩
    let r : ℝ := 1 - c / 4
    have hrpos : 0 < r := by
      dsimp [r]
      nlinarith
    have hrlt : r < 1 := by
      dsimp [r]
      nlinarith
    have hrnorm : ‖r‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hrpos]
      exact hrlt
    have hrpow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hrnorm
    let a : ℕ → ℝ := fun n => beta + (6 - beta) * r ^ n
    have h6beta : 0 < 6 - beta := by
      nlinarith
    have henvAll : ∀ n : ℕ, nativePNTHasAffineEnvelope (a n) := by
      intro n
      induction n with
      | zero =>
          simpa [a] using nativePNTHasAffineEnvelope_six
      | succ n ih =>
          have hrn : 0 < r ^ n := pow_pos hrpos n
          have hgap : beta < a n := by
            dsimp [a]
            have hmul : 0 < (6 - beta) * r ^ n := mul_pos h6beta hrn
            linarith
          have han : 0 < a n := lt_trans hbeta hgap
          have himp := nativePNTHasAffineEnvelope_improve_of_goodMass
            (a n) beta c han hbeta.le hgap hc hc1 hgood ih
          have hcoef :
              a (n + 1) = a n - (a n - beta) * c / 4 := by
            dsimp [a, r]
            rw [pow_succ]
            ring
          rw [← hcoef] at himp
          exact himp
    have halim : Tendsto a atTop (𝓝 beta) := by
      have hmul :
          Tendsto (fun n : ℕ => (6 - beta) * r ^ n) atTop
            (𝓝 ((6 - beta) * 0)) :=
        tendsto_const_nhds.mul hrpow
      simpa [a] using tendsto_const_nhds.add hmul
    have hev : ∀ᶠ n : ℕ in atTop, a n < eta :=
      (tendsto_order.1 halim).2 eta hbetaEta
    rcases eventually_atTop.1 hev with ⟨n0, hn0⟩
    have hcoef : a n0 < eta := hn0 n0 le_rfl
    rcases henvAll n0 with ⟨D, hD, henv⟩
    refine ⟨D, hD, ?_⟩
    intro N
    have hscale : a n0 * (N : ℝ) ≤ eta * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef.le (by positivity)
    exact (henv N).trans (add_le_add_right hscale D)
'''
s = s.replace(marker, block + marker)
p.write_text(s)
