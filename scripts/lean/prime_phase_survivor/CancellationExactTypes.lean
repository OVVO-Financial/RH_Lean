import «research.SURVIVOR_CANCELLATION_SCALE_20261117»

set_option autoImplicit false
open Filter RHLean.Analysis RHLean.Proof

example (Λ : ℝ) :
    SurvivorZeroModePowerSavingStatement Λ ↔
      SurvivorPointwiseSquaredBoundStatement Λ :=
  survivorPowerSaving_iff_pointwiseSquared Λ

example {Λ : ℝ} (h : SurvivorZeroModePowerSavingStatement Λ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℕ, 1 ≤ t →
        ‖survivorZeroMode Λ t‖ ^ 2 ≤ C * Real.rpow (t : ℝ) (2 + ε) :=
  survivorPointwiseSquared_of_powerSaving h

example {Λ : ℝ} (hΛ : 0 ≤ Λ) {t : ℕ} (ht : 1 ≤ t)
    (hkX : survivorPrimeCutoff Λ t ≤ squarePrefixEndpoint t) :
    survivorCompositeZeroMode Λ t -
        ((primeCountUpTo (squarePrefixEndpoint t) -
          primeCountUpTo (survivorPrimeCutoff Λ t) : ℕ) : ℂ) =
      survivorZeroMode Λ t :=
  survivorComposite_primeCount_residual_eq_survivor hΛ ht hkX

example {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (h : SurvivorZeroModePowerSavingStatement Λ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℕ, 1 ≤ t → 2 * Λ ≤ (t : ℝ) →
        ‖survivorCompositeZeroMode Λ t -
          ((primeCountUpTo (squarePrefixEndpoint t) -
            primeCountUpTo (survivorPrimeCutoff Λ t) : ℕ) : ℂ)‖ ^ 2 ≤
          C * Real.rpow (t : ℝ) (2 + ε) :=
  survivorComposite_residual_sq_le_of_powerSaving hΛ h

example : ∀ᶠ n : ℕ in atTop, n ^ 7 ≤ Nat.primeCounting (n ^ 8) :=
  survivor_primeCounting_eighth_eventually_ge_seventh

example {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      ‖survivorPrimeZeroMode Λ t‖ ^ 2 ≤ C * (t : ℝ) ^ 3 :=
  survivorPrimeZeroMode_not_cubic_squared_bound hΛ

example {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N H : ℕ, 1 ≤ H → H ≤ N →
        localSequenceEnergy (survivorPrimeZeroMode Λ) N H ≤
          C * (H : ℝ) * Real.rpow (N : ℝ) (2 + ε)) :=
  survivorPrimeZeroMode_not_uniformLocalRHScale hΛ

example {Λ : ℝ} (hΛ : 0 < Λ)
    (h : SurvivorZeroModePowerSavingStatement Λ) : RiemannHypothesis :=
  survivorPowerSaving_implies_mathlibRH hΛ h

#print survivorPowerSaving_iff_pointwiseSquared
#print survivorComposite_primeCount_residual_eq_survivor
#print survivorPrimeZeroMode_not_cubic_squared_bound
#print survivorPowerSaving_implies_mathlibRH
