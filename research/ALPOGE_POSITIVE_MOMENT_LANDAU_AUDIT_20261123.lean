import RHLean.Analysis.AlpogeNativePositiveMomentCriterion

/-!
# Direct positive-moment Landau audit

The typed checks retain the complete source, positive-part placement,
integrability, and the order of the kernel/order quantifiers. The direct
criterion takes no pointwise source estimate. The coarse arithmetic supplier
and the critical conditional consumer are checked separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Complex MeasureTheory Set

namespace RHLean.Analysis.PositiveMomentLandauAudit

open WindowLandau

example (g : ℝ → ℝ) (σ : ℝ) (k : ℕ) :
    weightedPositiveMoment g σ k =
      ∫ u in Ioi (0 : ℝ), max (g u) 0 *
        (u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ)) := rfl

example (σ : ℝ) (k : ℕ) :
    alpogeNativeGzPositiveMoment σ k =
      ∫ u in Ioi (0 : ℝ), max (alpogeNativeGzArithmetic (Real.exp u)) 0 *
        (u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ)) := rfl

/- All native moment orders are genuinely integrable on the chosen line. -/
example {σ : ℝ} (hσ : 2 < σ) (k : ℕ) :
    IntegrableOn (fun u : ℝ => max (alpogeNativeGzArithmetic (Real.exp u)) 0 *
      (u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ))) (Ioi 0) :=
  weightedPositiveMoment_integrable alpogeNativeGzArithmetic_poleData hσ k

/- Retain the signed real coefficient in the one-sided estimate. -/
example {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {σ : ℝ} (hσ : 2 < σ) (k : ℕ) (t : ℝ) :
    ‖(-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + t * I) / (k.factorial : ℂ)‖ +
      ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)).re ≤
        2 * weightedPositiveMoment g σ k :=
  landau_coefficients_le_positiveMoment hP hσ k t

/- The kernel parameter and coefficient precede every requested order. -/
example {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hM : ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ k₀ : ℕ, ∃ k ≥ k₀,
        weightedPositiveMoment g σ k ≤ C / (σ - θ) ^ k) :
    ∀ ρ ∈ Z, ρ.re ≤ θ :=
  landau_of_positiveMoments hP hθ hθ1 hM

/- The old window hypotheses supply the new moment hypothesis directly. -/
example {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {θ δ B : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hW : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1 + δ) * U),
      g u ≤ B * Real.exp (θ * u)) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ k₀ : ℕ, ∃ k ≥ k₀,
        weightedPositiveMoment g σ k ≤ C / (σ - θ) ^ k :=
  positiveMoment_bound_of_windows hP hθ hθ1 hδ hB hW

/- Regression: the old pointwise-window theorem keeps its original type. -/
example {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {θ δ B : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hW : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1 + δ) * U),
      g u ≤ B * Real.exp (θ * u)) :
    ∀ ρ ∈ Z, ρ.re ≤ θ :=
  landau_window hP hθ hθ1 hδ hB hW

/- The direct native consumer has only the explicit moment bound as input. -/
example {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hM : ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ k₀ : ℕ, ∃ k ≥ k₀,
        alpogeNativeGzPositiveMoment σ k ≤ C / (σ - θ) ^ k) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_nativeGz_positiveMoments hθ hθ1 hM

example {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hM : ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ k₀ : ℕ, ∃ k ≥ k₀,
          alpogeNativeGzPositiveMoment σ k ≤
            C / (σ - (1 / 2 + η)) ^ k) :
    RiemannHypothesis :=
  riemannHypothesis_of_nativeGz_positiveMoments hη₀ hM

/- The lower mass and exact centering stay inside the positive part. -/
example (N : ℕ) (hN : 1 ≤ N) :
    max (nativeAlpogeGz N) 0 = (N : ℝ) *
      max (alpogeGzNNSUpper N - alpogeGzNNSLower N +
        (harmonic N : ℝ) - Real.log (N : ℝ) +
          Real.eulerMascheroniConstant) 0 :=
  nativeAlpogeGz_posPart_eq_NNSHistory N hN

example (x : ℝ) (hx : 1 ≤ x) :
    max (alpogeNativeGzArithmetic x) 0 ≤
      (⌊x⌋₊ : ℝ) * max (alpogeGzNNSHistory ⌊x⌋₊) 0 +
        nativeAlpogeSafeSlope * (x - (⌊x⌋₊ : ℝ)) :=
  alpogeNativeGzArithmetic_posPart_le_floorHistory x hx

/- This is an actual unconditional supplier, with its coarse exponent. -/
example : alpogeNativeGzLinearUpperConstant =
    Real.log 4 + 3 + |Real.eulerMascheroniConstant| := rfl

example (x : ℝ) (hx : 1 ≤ x) :
    max (alpogeNativeGzArithmetic x) 0 ≤
      (Real.log 4 + 3 + |Real.eulerMascheroniConstant|) * x :=
  alpogeNativeGzArithmetic_posPart_le_linear x hx

example {σ : ℝ} (hσ : 2 < σ) (k : ℕ) :
    alpogeNativeGzPositiveMoment σ k ≤
      (Real.log 4 + 3 + |Real.eulerMascheroniConstant|) / (σ - 1) ^ (k + 1) :=
  alpogeNativeGzPositiveMoment_le_linear hσ k

end RHLean.Analysis.PositiveMomentLandauAudit

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[
    ``RHLean.Analysis.WindowLandau.weightedPositiveMoment_integrable,
    ``RHLean.Analysis.WindowLandau.weightedPositiveMoment_nonneg,
    ``RHLean.Analysis.WindowLandau.weightedPositiveMoment_le_of_exp_upper,
    ``RHLean.Analysis.WindowLandau.positiveMoment_bound_of_windows,
    ``RHLean.Analysis.WindowLandau.landau_coefficients_le_positiveMoment,
    ``RHLean.Analysis.WindowLandau.landau_of_coefficients,
    ``RHLean.Analysis.WindowLandau.landau_of_positiveMoments,
    ``RHLean.Analysis.WindowLandau.landau_window,
    ``RHLean.Analysis.alpogeNativeGzLinearUpperConstant_nonneg,
    ``RHLean.Analysis.alpogeNativeGzArithmetic_posPart_le_linear,
    ``RHLean.Analysis.alpogeNativeGzPositiveMoment_le_linear,
    ``RHLean.Analysis.nativeAlpogeGz_posPart_eq_NNSHistory,
    ``RHLean.Analysis.alpogeNativeGzArithmetic_posPart_le_floorHistory,
    ``RHLean.Analysis.riemannZeta_ne_zero_of_nativeGz_positiveMoments,
    ``RHLean.Analysis.riemannHypothesis_of_nativeGz_positiveMoments]
  let env ← getEnv
  for root in roots do
    unless env.contains root do
      throwError "Missing direct positive-moment declaration: {root}"
    let axioms ← liftCoreM (Lean.collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved terminal axiom for {root}: {ax}"
    logInfo m!"PASS direct positive-moment Landau {root}: {axioms}"
