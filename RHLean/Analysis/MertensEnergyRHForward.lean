import Mathlib
import RHLean.Analysis.MertensMellinAnalyticUniqueness

/-!
# The forward Mertens-energy implication to the Riemann hypothesis

The analytic-uniqueness layer rules out zeta zeros strictly to the right of the
critical line.  To rule out a zero strictly to the left, we use the completed
Riemann zeta function rather than the uncompleted functional equation.  This is
important formally: `completedRiemannZeta_one_sub` has no negative-integer side
condition.

For a nontrivial zero `s`, the Archimedean factor `Gammaℝ s` is nonzero.  Thus
`ζ(s) = 0` implies `Λ(s) = 0`; symmetry gives `Λ(1-s) = 0`, hence
`ζ(1-s) = 0`.  If `re s < 1/2`, the reflected point lies strictly to the right
of the critical line, contradicting the analytic-uniqueness theorem.
-/

noncomputable section

namespace RHLean.Analysis

open Complex

private theorem GammaR_ne_zero_of_not_trivial
    {s : ℂ} (hs0 : s ≠ 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    Gammaℝ s ≠ 0 := by
  rw [Gammaℝ_def]
  apply mul_ne_zero
  · simp [pi_ne_zero]
  · apply Gamma_ne_zero
    intro n hn
    have hs_even : s = -2 * (n : ℂ) := by
      calc
        s = 2 * (s / 2) := by ring
        _ = 2 * (-(n : ℂ)) := by rw [hn]
        _ = -2 * (n : ℂ) := by ring
    cases n with
    | zero =>
        apply hs0
        simpa using hs_even
    | succ n =>
        apply htriv
        refine ⟨n, ?_⟩
        simpa [Nat.cast_succ] using hs_even

/-- The repository's squared Mertens-energy criterion implies the formal
Riemann hypothesis, with no external classical criterion theorem argument. -/
theorem riemannHypothesis_of_mertensEnergy
    (hM : MertensEnergyBoundedStatement) :
    RiemannHypothesis := by
  intro s hz hnontriv hs1
  by_cases hcrit : s.re = (1 : ℝ) / 2
  · exact hcrit
  have hnotRight : ¬(1 : ℝ) / 2 < s.re := by
    intro hright
    exact (riemannZeta_ne_zero_of_half_lt_re hM hright hs1) hz
  have hleft : s.re < (1 : ℝ) / 2 := by
    exact lt_of_le_of_ne (le_of_not_gt hnotRight) hcrit
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hGamma : Gammaℝ s ≠ 0 :=
    GammaR_ne_zero_of_not_trivial hs0 hnontriv
  have hcompleted : completedRiemannZeta s = 0 := by
    have hdef := riemannZeta_def_of_ne_zero hs0
    have hdiv : completedRiemannZeta s / Gammaℝ s = 0 := by
      rw [← hdef, hz]
    simpa [hGamma] using hdiv
  have hrefCompleted : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub s, hcompleted]
  have href0 : 1 - s ≠ 0 := by
    intro h
    apply hs1
    exact (sub_eq_zero.mp h).symm
  have hrefZeta : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_def_of_ne_zero href0, hrefCompleted]
    simp
  have hrefRe : (1 : ℝ) / 2 < (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  have href1 : 1 - s ≠ 1 := by
    intro h
    exact hs0 (sub_eq_self.mp h)
  exfalso
  exact (riemannZeta_ne_zero_of_half_lt_re hM hrefRe href1) hrefZeta

end RHLean.Analysis
