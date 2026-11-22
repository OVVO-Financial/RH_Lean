import RHLean.Analysis.AlpogeLandau.LandauTheorems.ZeroFreeOfRpowWindow
import RHLean.Analysis.AlpogeNativeFourCharacterArithmetic

/-!
# The one-sided window consumer for the actual native Gz

The analytic Landau proof is reconstructed in the local AlpogeLandau closure.
This file identifies its principal finite prime-power ramp with RH_Lean's
actual reciprocal-Lambda/psi normalization, including Euler's constant.

The window growth estimate remains an explicit input.  This is the analytic
implication needed by a geometric source proof, not an unconditional RH theorem.
No terminal RH result, external compiled artifact, or retired proof DAG is used.
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis.AlpogeLandau

/-- The exact principal ramp uses every native von Mangoldt prime power.
The index zero vanishes; the original floor cutoff removes the max operation. -/
theorem ramp_one_re_eq_nativePrincipalPrimeSum (x : ℝ) (hx : 0 ≤ x) :
    (ramp (fun _ => (1 : ℂ)) x).re =
      RHLean.Analysis.alpogeNativePrincipalPrimeSum x := by
  have hrange : Finset.range (⌊x⌋₊ + 1) =
      insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  unfold ramp RHLean.Analysis.alpogeNativePrincipalPrimeSum
  rw [hrange, Finset.sum_insert (by simp)]
  have hzero : (Λ (0 : ℕ) : ℝ) = 0 := by simp
  simp only [hzero, Complex.ofReal_zero,
    zero_mul, zero_add, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hn1)
  have hnx : (n : ℝ) ≤ x :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le hx)
  have hcut : 0 ≤ x / (n : ℝ) - 1 := by
    rw [sub_nonneg, le_div_iff₀ hn0]
    simpa using hnx
  simp [max_eq_left hcut, RHLean.Analysis.alpogeNativePrimePowerWeight]

/-- Equality with the existing native real-x Gz, not a new source definition. -/
theorem G_eq_nativeGzArithmetic (x : ℝ) (hx : 0 ≤ x) :
    G x = RHLean.Analysis.alpogeNativeGzArithmetic x := by
  unfold G
  rw [ramp_one_re_eq_nativePrincipalPrimeSum x hx,
    RHLean.Analysis.alpogeNativeGzArithmetic_eq_principal]

/-- The positive one-member character family for zeta. -/
def principalFamily : CharFamily where
  ι := Unit
  fin := inferInstance
  N := fun _ => 1
  nz := fun _ => inferInstance
  χ := fun _ => 1
  a := fun _ => 1
  a_pos := fun _ => zero_lt_one
  adm := fun _ => Or.inl rfl

theorem Gm_principalFamily_eq_G (x : ℝ) :
    Gm principalFamily x = G x := by
  have hval : (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n) =
      fun _ => (1 : ℂ) := by
    funext n
    exact MulChar.one_apply (isUnit_of_subsingleton _)
  change (∑ _ : Unit, 1 * (Gchi (1 : DirichletCharacter ℂ 1) x).re) = _
  rw [Fintype.sum_unique, one_mul]
  unfold Gchi
  rw [ite_eq_left rfl, hval]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  rfl

theorem Gm_principalFamily_eq_nativeGzArithmetic (x : ℝ) (hx : 0 ≤ x) :
    Gm principalFamily x = RHLean.Analysis.alpogeNativeGzArithmetic x := by
  rw [Gm_principalFamily_eq_G, G_eq_nativeGzArithmetic x hx]

/-- Arbitrarily late multiplicative windows suffice.  The constant C and
window width delta are fixed for this exponent and need not be uniform as the
exponent later approaches one half. -/
theorem nativeGz_nonvanishing_of_rpow_window
    {θ δ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
      ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
        RHLean.Analysis.alpogeNativeGzArithmetic y ≤ C * y ^ θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  have hfamily : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
      ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
        Gm principalFamily y ≤ C * y ^ θ := by
    intro Y₀
    obtain ⟨Y, hY, hbound⟩ := h (max Y₀ 1)
    refine ⟨Y, (le_max_left _ _).trans hY, ?_⟩
    intro y hy
    have hy0 : 0 ≤ y :=
      (by linarith : (0 : ℝ) ≤ 1).trans
        (((le_max_right _ _).trans hY).trans hy.1)
    rw [Gm_principalFamily_eq_nativeGzArithmetic y hy0]
    exact hbound y hy
  have hz := zeroFree_of_rpow_window principalFamily hθ hθ1 hδ hfamily
  intro s hs
  have hne := hz () s hs
  change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0 at hne
  simpa only [DirichletCharacter.LFunction_modOne_eq] using hne

/-- Every positive exponent loss, on arbitrarily late windows, excludes all
zeros strictly to the right of one half.  C and delta may depend on epsilon. -/
theorem nativeGz_nonvanishing_right_of_half_of_windows
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ δ C : ℝ, 0 < δ ∧
        ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
          ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
            RHLean.Analysis.alpogeNativeGzArithmetic y ≤
              C * y ^ ((1 : ℝ) / 2 + ε)) :
    ∀ s : ℂ, (1 : ℝ) / 2 < s.re → riemannZeta s ≠ 0 := by
  intro s hs
  by_cases hs1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hs1
  have hs1' : s.re < 1 := lt_of_not_ge hs1
  let ε : ℝ := min (ε₀ / 2) ((s.re - (1 : ℝ) / 2) / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith) (by linarith)
  have hε0 : ε < ε₀ := by
    have hle : ε ≤ ε₀ / 2 := min_le_left _ _
    linarith
  have hθs : (1 : ℝ) / 2 + ε < s.re := by
    have hle : ε ≤ (s.re - (1 : ℝ) / 2) / 2 := min_le_right _ _
    linarith
  obtain ⟨δ, C, hδ, hwindow⟩ := h ε hε hε0
  exact nativeGz_nonvanishing_of_rpow_window
    (θ := (1 : ℝ) / 2 + ε) (δ := δ) (C := C)
    (by linarith) (by linarith) hδ hwindow s hθs

/-- The functional-equation step uses only Mathlib. -/
theorem riemannHypothesis_of_nonvanishing_right_of_half
    (h : ∀ s : ℂ, (1 : ℝ) / 2 < s.re → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hz hnontriv hs1
  by_cases hcrit : s.re = (1 : ℝ) / 2
  · exact hcrit
  have hnotRight : ¬ (1 : ℝ) / 2 < s.re := by
    intro hright
    exact (h s hright) hz
  have hleft : s.re < (1 : ℝ) / 2 :=
    lt_of_le_of_ne (le_of_not_gt hnotRight) hcrit
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hGamma : Gammaℝ s ≠ 0 := by
    intro hG
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hG
    cases n with
    | zero =>
        apply hs0
        simpa using! hn
    | succ n =>
        apply hnontriv
        refine ⟨n, ?_⟩
        simpa [Nat.cast_succ] using! hn
  have hcompleted : completedRiemannZeta s = 0 := by
    have hdef := riemannZeta_def_of_ne_zero hs0
    have hdiv : completedRiemannZeta s / Gammaℝ s = 0 := by
      rw [← hdef, hz]
    simpa [hGamma] using! hdiv
  have hrefCompleted : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub s, hcompleted]
  have href0 : 1 - s ≠ 0 := by
    intro hzero
    apply hs1
    exact (sub_eq_zero.mp hzero).symm
  have hrefZeta : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_def_of_ne_zero href0, hrefCompleted]
    simp
  have hrefRe : (1 : ℝ) / 2 < (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  exact False.elim ((h (1 - s) hrefRe) hrefZeta)

/-- The exact native one-sided window-to-RH consequence.  Its growth premise
is the required output of the same-family geometric source construction. -/
theorem riemannHypothesis_of_nativeGz_windows
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ δ C : ℝ, 0 < δ ∧
        ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
          ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
            RHLean.Analysis.alpogeNativeGzArithmetic y ≤
              C * y ^ ((1 : ℝ) / 2 + ε)) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonvanishing_right_of_half
    (nativeGz_nonvanishing_right_of_half_of_windows hε₀ h)

end RHLean.Analysis.AlpogeLandau

