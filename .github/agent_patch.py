from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()

# 1. Add a quantitative telescoping consequence of the already-proved cubic recurrence.
rate_marker = '\n\n/-! ## Signed Selberg recurrence and linear control -/'
assert rate_marker in s
assert 'theorem cubic_recurrence_rate_sub' not in s
rate_block = r'''

/-- The cubic recurrence also retains an explicit finite-step budget.  Since
the sequence is decreasing, every previous cubic decrement dominates the
current cube, so the accumulated drop controls `C * n * a n ^ 3`. -/
theorem cubic_recurrence_rate_sub
    (a : ℕ → ℝ) (C : ℝ)
    (hC : 0 < C)
    (hnonneg : ∀ n, 0 ≤ a n)
    (hrec : ∀ n, a (n + 1) ≤ a n - C * (a n) ^ 3) :
    ∀ n : ℕ, C * (n : ℝ) * (a n) ^ 3 ≤ a 0 - a n := by
  have hstep : ∀ n, a (n + 1) ≤ a n := by
    intro n
    have hdrop : 0 ≤ C * (a n) ^ 3 :=
      mul_nonneg hC.le (pow_nonneg (hnonneg n) 3)
    exact (hrec n).trans (sub_le_self _ hdrop)
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hcube : (a (n + 1)) ^ 3 ≤ (a n) ^ 3 :=
        pow_le_pow_left₀ (hnonneg (n + 1)) (hstep n) 3
      have hfirst :
          C * (n : ℝ) * (a (n + 1)) ^ 3 ≤
            C * (n : ℝ) * (a n) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube
          (mul_nonneg hC.le (by positivity))
      have hsecond : C * (a (n + 1)) ^ 3 ≤ C * (a n) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube hC.le
      have hdrop : C * (a n) ^ 3 ≤ a n - a (n + 1) := by
        linarith [hrec n]
      calc
        C * ((n + 1 : ℕ) : ℝ) * (a (n + 1)) ^ 3 =
            C * (n : ℝ) * (a (n + 1)) ^ 3 +
              C * (a (n + 1)) ^ 3 := by
          push_cast
          ring
        _ ≤ C * (n : ℝ) * (a n) ^ 3 + C * (a n) ^ 3 :=
          add_le_add hfirst hsecond
        _ ≤ (a 0 - a n) + (a n - a (n + 1)) :=
          add_le_add ih hdrop
        _ = a 0 - a (n + 1) := by ring

/-- A convenient weaker form of `cubic_recurrence_rate_sub`. -/
theorem cubic_recurrence_rate
    (a : ℕ → ℝ) (C : ℝ)
    (hC : 0 < C)
    (hnonneg : ∀ n, 0 ≤ a n)
    (hrec : ∀ n, a (n + 1) ≤ a n - C * (a n) ^ 3)
    (n : ℕ) :
    C * (n : ℝ) * (a n) ^ 3 ≤ a 0 := by
  exact (cubic_recurrence_rate_sub a C hC hnonneg hrec n).trans
    (sub_le_self _ (hnonneg n))
'''
s = s.replace(rate_marker, rate_block + rate_marker, 1)

# 2. Add monotonicity of affine envelopes just after the starting slope theorem.
start = s.index('theorem nativePNTHasAffineEnvelope_six')
next_doc = s.index('\n\n/--', start)
mono_block = r'''

/-- Weakening an affine slope preserves the envelope after enlarging only the
linear coefficient. -/
theorem nativePNTHasAffineEnvelope_mono
    {alpha beta : ℝ} (hab : alpha ≤ beta)
    (h : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope beta := by
  rcases h with ⟨D, hD, henv⟩
  refine ⟨D, hD, ?_⟩
  intro N
  have hscale : alpha * (N : ℝ) ≤ beta * (N : ℝ) :=
    mul_le_mul_of_nonneg_right hab (by positivity)
  exact (henv N).trans (add_le_add_right hscale D)
'''
assert 'theorem nativePNTHasAffineEnvelope_mono' not in s
s = s[:next_doc] + mono_block + s[next_doc:]

# 3. Replace the qualitative fixed-beta geometric loop by a calibrated cubic loop.
old_start = s.index('/-- **Arbitrarily small affine slope.**')
old_end = s.index('\n\n/-! ## The Chebyshev prime number theorem -/', old_start)
new_block = r'''/-- Universal cubic contraction constant obtained by taking the good-fibre
threshold `beta = alpha / 6` and the explicit good-mass coefficient
`beta^2 / 6500000`. -/
def nativePNTCubicConstant : ℝ := 1 / 1123200000

/-- One calibrated affine-envelope step.  For every admissible slope
`0 < alpha <= 6`, choosing `beta = alpha / 6` makes the previously proved
quadratic good-mass density turn the affine improvement into the exact cubic
decrement `C * alpha^3`. -/
theorem nativePNTHasAffineEnvelope_cubic_step
    (alpha : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - nativePNTCubicConstant * alpha ^ 3) := by
  let beta : ℝ := alpha / 6
  have hbeta : 0 < beta := by
    dsimp [beta]
    positivity
  have hbeta0 : 0 ≤ beta := hbeta.le
  have hbeta1 : beta ≤ 1 := by
    dsimp [beta]
    linarith
  have hba : beta < alpha := by
    dsimp [beta]
    nlinarith
  let c : ℝ := beta ^ 2 / 6500000
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hsq : beta ^ 2 ≤ 1 := by
    have hprod : 0 ≤ beta * (1 - beta) :=
      mul_nonneg hbeta0 (sub_nonneg.mpr hbeta1)
    nlinarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    nlinarith
  have hgood : ∀ᶠ N : ℕ in atTop,
      c * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N beta := by
    simpa [c] using
      nativeLambdaTwoGoodRecipMass_eventually_quadratic_rate
        beta hbeta hbeta1
  have himp := nativePNTHasAffineEnvelope_improve_of_goodMass
    alpha beta c halpha hbeta0 hba hc hc1 hgood henv
  have hcoef :
      alpha - (alpha - beta) * c / 4 =
        alpha - nativePNTCubicConstant * alpha ^ 3 := by
    dsimp [beta, c, nativePNTCubicConstant]
    ring
  rw [hcoef] at himp
  exact himp

private theorem nativePNT_cubic_step_pos
    (alpha : ℝ) (halpha : 0 < alpha) (halpha6 : alpha ≤ 6) :
    0 < alpha - nativePNTCubicConstant * alpha ^ 3 := by
  have hsq : alpha ^ 2 ≤ (6 : ℝ) ^ 2 :=
    pow_le_pow_left₀ halpha.le halpha6 2
  have hC0 : 0 ≤ nativePNTCubicConstant := by
    norm_num [nativePNTCubicConstant]
  have hmul :
      nativePNTCubicConstant * alpha ^ 2 ≤
        nativePNTCubicConstant * (6 : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hC0
  have hC36 : nativePNTCubicConstant * (6 : ℝ) ^ 2 < 1 := by
    norm_num [nativePNTCubicConstant]
  have hfactor : 0 < 1 - nativePNTCubicConstant * alpha ^ 2 := by
    linarith
  have hrewrite :
      alpha - nativePNTCubicConstant * alpha ^ 3 =
        alpha * (1 - nativePNTCubicConstant * alpha ^ 2) := by
    ring
  rw [hrewrite]
  exact mul_pos halpha hfactor

/-- The calibrated slope sequence whose recurrence is exactly cubic. -/
def nativePNTCubicSlope : ℕ → ℝ
  | 0 => 6
  | Nat.succ n =>
      nativePNTCubicSlope n -
        nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3

@[simp] theorem nativePNTCubicSlope_zero : nativePNTCubicSlope 0 = 6 := rfl

@[simp] theorem nativePNTCubicSlope_succ (n : ℕ) :
    nativePNTCubicSlope (n + 1) =
      nativePNTCubicSlope n -
        nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3 := rfl

/-- Every calibrated slope remains positive, stays in the admissible range,
and is realized by an affine Chebyshev-error envelope. -/
theorem nativePNTCubicSlope_spec :
    ∀ n : ℕ,
      0 < nativePNTCubicSlope n ∧
      nativePNTCubicSlope n ≤ 6 ∧
      nativePNTHasAffineEnvelope (nativePNTCubicSlope n) := by
  intro n
  induction n with
  | zero =>
      exact ⟨by norm_num, le_rfl, nativePNTHasAffineEnvelope_six⟩
  | succ n ih =>
      rcases ih with ⟨hpos, hle6, henv⟩
      have hnextpos := nativePNT_cubic_step_pos
        (nativePNTCubicSlope n) hpos hle6
      have hnextenv := nativePNTHasAffineEnvelope_cubic_step
        (nativePNTCubicSlope n) hpos hle6 henv
      have hdrop :
          0 ≤ nativePNTCubicConstant * (nativePNTCubicSlope n) ^ 3 := by
        exact mul_nonneg
          (by norm_num [nativePNTCubicConstant])
          (pow_nonneg hpos.le 3)
      have hnextle :
          nativePNTCubicSlope (n + 1) ≤ nativePNTCubicSlope n := by
        rw [nativePNTCubicSlope_succ]
        exact sub_le_self _ hdrop
      exact ⟨by simpa using hnextpos, hnextle.trans hle6,
        by simpa using hnextenv⟩

/-- The prime-specific iteration is routed through the abstract cubic
recurrence theorem proved at the start of this file. -/
theorem nativePNTCubicSlope_tendsto_zero :
    Tendsto nativePNTCubicSlope atTop (𝓝 0) := by
  refine tendsto_zero_of_cubic_recurrence
    nativePNTCubicSlope nativePNTCubicConstant ?_ ?_ ?_
  · norm_num [nativePNTCubicConstant]
  · intro n
    exact (nativePNTCubicSlope_spec n).1.le
  · intro n
    rw [nativePNTCubicSlope_succ]

/-- Explicit finite-iteration diagnostic: after `n` cubic improvements the
current slope obeys `C n alpha_n^3 <= 6`. -/
theorem nativePNTCubicSlope_rate (n : ℕ) :
    nativePNTCubicConstant * (n : ℝ) *
        (nativePNTCubicSlope n) ^ 3 ≤ 6 := by
  have hC : 0 < nativePNTCubicConstant := by
    norm_num [nativePNTCubicConstant]
  have hnonneg : ∀ m, 0 ≤ nativePNTCubicSlope m :=
    fun m => (nativePNTCubicSlope_spec m).1.le
  have hrec : ∀ m,
      nativePNTCubicSlope (m + 1) ≤
        nativePNTCubicSlope m -
          nativePNTCubicConstant * (nativePNTCubicSlope m) ^ 3 := by
    intro m
    rw [nativePNTCubicSlope_succ]
  simpa using
    (cubic_recurrence_rate nativePNTCubicSlope nativePNTCubicConstant
      hC hnonneg hrec n)

/-- A concrete iteration budget.  Any `n` for which
`6 < C * n * eta^3` already forces an affine envelope of slope at most `eta`. -/
theorem nativePNTHasAffineEnvelope_of_cubic_budget
    (eta : ℝ) (heta : 0 < eta) (n : ℕ)
    (hbudget :
      6 < nativePNTCubicConstant * (n : ℝ) * eta ^ 3) :
    nativePNTHasAffineEnvelope eta := by
  have hspec := nativePNTCubicSlope_spec n
  have hslopeEta : nativePNTCubicSlope n ≤ eta := by
    by_contra hnot
    have hetaSlope : eta < nativePNTCubicSlope n := lt_of_not_ge hnot
    have hcube : eta ^ 3 ≤ (nativePNTCubicSlope n) ^ 3 :=
      pow_le_pow_left₀ heta.le hetaSlope.le 3
    have hcoef0 :
        0 ≤ nativePNTCubicConstant * (n : ℝ) :=
      mul_nonneg (by norm_num [nativePNTCubicConstant]) (by positivity)
    have hmul :
        nativePNTCubicConstant * (n : ℝ) * eta ^ 3 ≤
          nativePNTCubicConstant * (n : ℝ) *
            (nativePNTCubicSlope n) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube hcoef0
    have hrate := nativePNTCubicSlope_rate n
    linarith
  exact nativePNTHasAffineEnvelope_mono hslopeEta hspec.2.2

/-- **Arbitrarily small affine slope.**  This qualitative corollary now runs
through the calibrated cubic slope sequence rather than a fixed-beta geometric
loop; the separate budget theorem above retains the finite-step rate. -/
theorem nativePNTHasAffineEnvelope_arbitrarily_small
    (eta : ℝ) (heta : 0 < eta) :
    nativePNTHasAffineEnvelope eta := by
  have hev : ∀ᶠ n : ℕ in atTop, nativePNTCubicSlope n < eta :=
    (tendsto_order.1 nativePNTCubicSlope_tendsto_zero).2 eta heta
  rcases eventually_atTop.1 hev with ⟨n0, hn0⟩
  exact nativePNTHasAffineEnvelope_mono (hn0 n0 le_rfl).le
    (nativePNTCubicSlope_spec n0).2.2
'''
s = s[:old_start] + new_block + s[old_end:]

p.write_text(s)
