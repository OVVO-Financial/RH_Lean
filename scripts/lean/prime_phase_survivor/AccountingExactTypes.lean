import «research.SURVIVOR_PRIME_COMPOSITE_ACCOUNTING_20261117»

set_option autoImplicit false
open RHLean.Analysis RHLean.Proof
open RHLean.Proof.CanonicalGapAncestryBridge

example {Λ : ℝ} (hΛ : 0 ≤ Λ) (t : ℕ) :
    (survivorPrimeCutoff Λ t : ℝ) ^ 2 ≤ 2 * Λ * (t : ℝ) + 1 ∧
      2 * Λ * (t : ℝ) + 1 < ((survivorPrimeCutoff Λ t : ℝ) + 1) ^ 2 :=
  survivorPrimeCutoff_bounds hΛ t

example (Λ : ℝ) (t q : ℕ) :
    IsSurvivorZeroModePair Λ t 1 q ↔
      q.Prime ∧ q ≤ squarePrefixEndpoint t ∧
        2 * Λ * (t : ℝ) < (q : ℝ) ^ 2 - 1 :=
  isSurvivorZeroModePair_one_iff Λ t q

example {Λ : ℝ} {t k : ℕ}
    (hlo : (k : ℝ) ^ 2 ≤ 2 * Λ * (t : ℝ) + 1)
    (hhi : 2 * Λ * (t : ℝ) + 1 < ((k : ℝ) + 1) ^ 2)
    (hkX : k ≤ squarePrefixEndpoint t) :
    survivorZeroModeKernel Λ t 1 =
      primeCountUpTo (squarePrefixEndpoint t) - primeCountUpTo k :=
  survivorZeroModeKernel_one_eq_primeCount_sub_of_bounds hlo hhi hkX

example {Λ : ℝ} (hΛ : 0 ≤ Λ) {t : ℕ} (ht : 1 ≤ t)
    (hkX : survivorPrimeCutoff Λ t ≤ squarePrefixEndpoint t) :
    survivorPrimeZeroMode Λ t =
      -((primeCountUpTo (squarePrefixEndpoint t) -
        primeCountUpTo (survivorPrimeCutoff Λ t) : ℕ) : ℂ) :=
  survivorPrimeZeroMode_eq_neg_primeCount_sub hΛ ht hkX

example {Λ : ℝ} (hΛ : 0 ≤ Λ) {t : ℕ} (ht : 1 ≤ t)
    (hkX : survivorPrimeCutoff Λ t ≤ squarePrefixEndpoint t) :
    survivorCompositeZeroMode Λ t = survivorZeroMode Λ t +
      ((primeCountUpTo (squarePrefixEndpoint t) -
        primeCountUpTo (survivorPrimeCutoff Λ t) : ℕ) : ℂ) :=
  survivorCompositeZeroMode_eq_survivor_add_primeCount_sub hΛ ht hkX

example {Λ : ℝ} (hΛ : 0 ≤ Λ) {t : ℕ} (ht : 1 ≤ t)
    (hstage : 2 * Λ ≤ (t : ℝ)) :
    survivorPrimeCutoff Λ t ≤ t :=
  survivorPrimeCutoff_le_stage hΛ ht hstage

example : IsSurvivorZeroModePair 1 1 1 2 := prime_two_survives_stage_one
example : ¬ IsSurvivorZeroModePair 1 2 1 2 := prime_two_not_survivor_stage_two
example : IsSurvivorZeroModePair 1 2 2 3 := composite_six_survives_stage_two

#print survivorPrimeZeroMode_eq_neg_primeCount_sub
#print survivorCompositeZeroMode_eq_survivor_add_primeCount_sub
