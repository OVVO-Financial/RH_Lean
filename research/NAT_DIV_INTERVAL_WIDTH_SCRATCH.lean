import RHLean.Analysis.RoughWheelFiniteCounting

/-!
# Floor-width scratch

A single generic floor inequality replaces the large `omega` block in the
quantitative 2310-wheel estimate.  For positive denominators, the width between
two quotient endpoints differs from its continuum width by at most one.
-/

noncomputable section

namespace RHLean.Analysis

/-- Finite quotient endpoints cost at most one unit of interval width. -/
theorem natDiv_interval_width_le_scratch
    (B a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((B / b : ℕ) : ℝ) - ((B / a : ℕ) : ℝ) ≤
      (B : ℝ) / b - (B : ℝ) / a + 1 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hub : ((B / b : ℕ) : ℝ) ≤ (B : ℝ) / b := by
    apply (le_div_iff₀ hbR).2
    exact_mod_cast Nat.div_mul_le_self B b
  have hlowNat : B < B / a * a + a := by
    nlinarith [Nat.mod_add_div B a, Nat.mod_lt B ha]
  have hlowCast :
      (B : ℝ) < ((B / a : ℕ) : ℝ) * (a : ℝ) + (a : ℝ) := by
    exact_mod_cast hlowNat
  have hlow : (B : ℝ) / a < ((B / a : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ haR).2
    nlinarith
  linarith

end RHLean.Analysis
