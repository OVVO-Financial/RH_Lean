import Mathlib
import RHLean.Analysis.MertensMellinAnalyticUniqueness

/-!
# The forward Mertens criterion implies the Riemann Hypothesis

The analytic-uniqueness layer gives zeta nonvanishing at every point strictly
to the right of the critical line.  To finish the forward criterion, a
hypothetical nontrivial zero strictly to the left is reflected by the completed
zeta functional equation.

The completed formulation avoids any separate negative-odd-integer analysis.
Mathlib's `Gammaℝ_eq_zero_iff` says that the real archimedean Gamma factor
vanishes only at nonpositive even integers.  For a nontrivial zeta zero those
points are excluded by the trivial-zero hypothesis, with `s = 0` ruled out by
`riemannZeta_zero`.  Thus `ζ(s) = 0` implies `Λ(s) = 0`, hence
`Λ(1-s) = 0`, and therefore `ζ(1-s) = 0`.  If `Re(s) < 1/2`, the reflected
point lies in the already-proved zero-free half-plane.
-/

noncomputable section

namespace RHLean.Analysis

open Complex

/-- A zeta zero cannot occur at zero. -/
private theorem zetaZero_ne_zero {s : ℂ} (hz : riemannZeta s = 0) : s ≠ 0 := by
  intro hs
  subst s
  rw [riemannZeta_zero] at hz
  norm_num at hz

/-- At a nontrivial zeta zero, the real archimedean Gamma factor is nonzero.
Its only zeros are the nonpositive even integers: zero is not a zeta zero, and
the negative even integers are exactly the excluded trivial zeros. -/
private theorem GammaR_ne_zero_of_nontrivial_zetaZero
    {s : ℂ} (hz : riemannZeta s = 0)
    (hnontrivial : ¬ ∃ n : ℕ, s = -2 * (n + 1)) :
    Gammaℝ s ≠ 0 := by
  intro hGamma
  rcases Gammaℝ_eq_zero_iff.mp hGamma with ⟨n, hn⟩
  cases n with
  | zero =>
      exact zetaZero_ne_zero hz (by simpa using hn)
  | succ n =>
      apply hnontrivial
      refine ⟨n, ?_⟩
      convert hn using 1 <;> push_cast <;> ring

/-- A nontrivial zeta zero reflects to a zeta zero at `1 - s` via the completed
functional equation. -/
private theorem riemannZeta_one_sub_eq_zero_of_nontrivial_zero
    {s : ℂ} (hz : riemannZeta s = 0)
    (hnontrivial : ¬ ∃ n : ℕ, s = -2 * (n + 1))
    (hs1 : s ≠ 1) :
    riemannZeta (1 - s) = 0 := by
  have hs0 : s ≠ 0 := zetaZero_ne_zero hz
  have hGamma : Gammaℝ s ≠ 0 :=
    GammaR_ne_zero_of_nontrivial_zetaZero hz hnontrivial
  have hcompleted : completedRiemannZeta s = 0 := by
    have hz' := hz
    rw [riemannZeta_def_of_ne_zero hs0] at hz'
    have hmul := congrArg (fun z : ℂ => z * Gammaℝ s) hz'
    rw [div_mul_cancel₀ _ hGamma] at hmul
    simpa using hmul
  have hcompleted' : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hcompleted
  have hreflect0 : 1 - s ≠ 0 := by
    exact sub_ne_zero.mpr hs1.symm
  rw [riemannZeta_def_of_ne_zero hreflect0, hcompleted']
  simp

/-- The Mertens energy criterion implies Mathlib's formal Riemann Hypothesis.
The right-half-plane exclusion is the analytic-uniqueness theorem; the left
half is eliminated by the completed-zeta reflection above. -/
theorem riemannHypothesis_of_mertensEnergyBounded
    (hM : MertensEnergyBoundedStatement) : RiemannHypothesis := by
  intro s hz hnontrivial hs1
  have hle : s.re ≤ (1 : ℝ) / 2 := by
    by_contra h
    have hright : (1 : ℝ) / 2 < s.re := lt_of_not_ge h
    exact (riemannZeta_ne_zero_of_half_lt_re hM hright hs1) hz
  have hge : (1 : ℝ) / 2 ≤ s.re := by
    by_contra h
    have hleft : s.re < (1 : ℝ) / 2 := lt_of_not_ge h
    have hreflectZero : riemannZeta (1 - s) = 0 :=
      riemannZeta_one_sub_eq_zero_of_nontrivial_zero hz hnontrivial hs1
    have hs0 : s ≠ 0 := zetaZero_ne_zero hz
    have hreflectOne : 1 - s ≠ 1 := sub_ne_self.mpr hs0
    have hreflectRight : (1 : ℝ) / 2 < (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    exact
      (riemannZeta_ne_zero_of_half_lt_re hM hreflectRight hreflectOne)
        hreflectZero
  exact le_antisymm hle hge

end RHLean.Analysis
