import Mathlib

/-!
# #919: exact sharp square cutoffs from finite-width half-integer smoothing

The VF AMP sharp cutoffs are X_R = R^2 - 1 and R - 1. Their analytic
midpoint representatives x = X_R + 1/2 and y = (R - 1) + 1/2 avoid every
integer site. A smooth window which equals one below 1-h and zero
above 1+h recovers the EXACT cutoff if h*x < 1/2.

The q^2 daughters use exactly the SAME relative width: the term
M_V(x / q^2) has argument n*q^2/x and n*q^2 remains an integer.
Consequently one common h < 1/(2*x) recovers ALL daughter cutoffs
simultaneously, without a limit or an unproved exchange of limits.

This formal result is purely geometric. It does NOT assert that OpenAI's
smooth sixth-power amplification is uniform in this R-dependent test.
The required seminorm-uniform analytic estimate remains open.
-/

namespace RHLean.Analysis

/-- A cutoff centered exactly between integers is recovered from ANY
transition window narrower than one half of the unit spacing. -/
theorem vf919HalfIntegerWindow_eq_sharp
    (N m : ℕ) (h : ℝ) (V : ℝ → ℝ)
    (hwidth : h * ((N : ℝ) + 1 / 2) < 1 / 2)
    (hone : ∀ u : ℝ, u ≤ 1 - h → V u = 1)
    (hzero : ∀ u : ℝ, 1 + h ≤ u → V u = 0) :
    V ((m : ℝ) / ((N : ℝ) + 1 / 2)) =
      if m ≤ N then 1 else 0 := by
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  by_cases hm : m ≤ N
  · rw [if_pos hm]
    apply hone
    apply (div_le_iff₀ hx).2
    have hcast : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
    calc
      (m : ℝ) ≤ (N : ℝ) := hcast
      _ ≤ ((N : ℝ) + 1 / 2) - h * ((N : ℝ) + 1 / 2) := by linarith
      _ = (1 - h) * ((N : ℝ) + 1 / 2) := by ring
  · rw [if_neg hm]
    apply hzero
    apply (le_div_iff₀ hx).2
    have hs : N + 1 ≤ m := by omega
    have hcast : (N : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hs
    calc
      (1 + h) * ((N : ℝ) + 1 / 2) =
          ((N : ℝ) + 1 / 2) + h * ((N : ℝ) + 1 / 2) := by ring
      _ ≤ (N : ℝ) + 1 := by linarith
      _ ≤ (m : ℝ) := hcast

/-- The common physical scale x = R^2 - 1/2 equals X_R + 1/2. -/
theorem vf919SquareHalfIntegerCenter (R : ℕ) (hR : 2 ≤ R) :
    ((R ^ 2 - 1 : ℕ) : ℝ) + 1 / 2 =
      (R : ℝ) ^ 2 - 1 / 2 := by
  have hsq : 1 ≤ R ^ 2 := by nlinarith
  rw [Nat.cast_sub hsq]
  push_cast
  ring

/-- For EVERY integer q, in particular an odd q^2 daughter, the same
window recovers the original precise floor cutoff. -/
theorem vf919SquareQ2Window_eq_sharp
    (R q n : ℕ) (h : ℝ) (V : ℝ → ℝ)
    (hwidth : h * (((R ^ 2 - 1 : ℕ) : ℝ) + 1 / 2) < 1 / 2)
    (hone : ∀ u : ℝ, u ≤ 1 - h → V u = 1)
    (hzero : ∀ u : ℝ, 1 + h ≤ u → V u = 0) :
    V ((((n * q * q : ℕ) : ℝ) /
        (((R ^ 2 - 1 : ℕ) : ℝ) + 1 / 2))) =
      if n * q * q ≤ R ^ 2 - 1 then 1 else 0 :=
  vf919HalfIntegerWindow_eq_sharp
    (R ^ 2 - 1) (n * q * q) h V hwidth hone hzero

/-- Likewise the smaller root cutoff y = R - 1/2 is recovered exactly. -/
theorem vf919RootWindow_eq_sharp
    (R n : ℕ) (h : ℝ) (V : ℝ → ℝ)
    (hR : 1 ≤ R)
    (hwidth : h * ((R : ℝ) - 1 / 2) < 1 / 2)
    (hone : ∀ u : ℝ, u ≤ 1 - h → V u = 1)
    (hzero : ∀ u : ℝ, 1 + h ≤ u → V u = 0) :
    V ((n : ℝ) / ((R : ℝ) - 1 / 2)) =
      if n ≤ R - 1 then 1 else 0 := by
  have hcenter :
      (((R - 1 : ℕ) : ℝ) + 1 / 2) = (R : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub hR]
    push_cast
    ring
  rw [← hcenter] at hwidth ⊢
  exact vf919HalfIntegerWindow_eq_sharp (R - 1) n h V
    hwidth hone hzero

end RHLean.Analysis
