import Mathlib
import «research.SQUARE_SHELL_TRAPEZOID_CORRECTED_20261018»

/-!
# Exact finite prime/cofactor interfaces for trapezoidal square shells

This module preserves the half-open product window, floor endpoints, actual
prime indicator, and the Mobius sign on every cofactor. It proves the finite
pi = Li-model + actual-discrepancy decomposition and high-cofactor hyperbola
interchange. There is no PNT short-interval estimate or dispersion lemma.
The low- and high-cofactor cutoffs are disjoint, and the omitted smooth/high
cross terms must remain in the complete signed energy.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- The lower integer boundary at shift k-T (k in 0,...,2T). -/
def shellTrapezoidLower (r T k : ℕ) : ℕ :=
  r ^ 2 - T + k

/-- The upper *included* integer boundary at the same shift. -/
def shellTrapezoidUpper (r T k : ℕ) : ℕ :=
  (r + 1) ^ 2 - T + k

/-- Correct ordering of translated half-open walls. -/
theorem shellTrapezoidLower_le_upper (r T k : ℕ) :
    shellTrapezoidLower r T k ≤ shellTrapezoidUpper r T k := by
  have hexpand : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
  have hr : r ^ 2 ≤ (r + 1) ^ 2 := by omega
  unfold shellTrapezoidLower shellTrapezoidUpper
  omega

/-- Physical membership in the translated half-open product shell. -/
def shellTrapezoidProductAdmitted
    (r T k p c : ℕ) : Prop :=
  shellTrapezoidLower r T k < p * c ∧
    p * c ≤ shellTrapezoidUpper r T k

/-- Prime-indicator count on a genuine finite integer prefix. -/
def shellTrapezoidPrimePi (x : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 x, if p.Prime then (1 : ℝ) else 0

/-- Exact prime count on a half-open integer interval. -/
theorem shellTrapezoidPrimePi_Ioc
    (a b : ℕ) (hab : a ≤ b) :
    (∑ p ∈ Finset.Ioc a b, if p.Prime then (1 : ℝ) else 0) =
      shellTrapezoidPrimePi b - shellTrapezoidPrimePi a := by
  have hsum := Finset.sum_Ioc_consecutive
    (f := fun p : ℕ => if p.Prime then (1 : ℝ) else 0)
    (Nat.zero_le a) hab
  unfold shellTrapezoidPrimePi
  apply (eq_sub_iff_add_eq).2
  simpa [add_comm] using! hsum

/-- Integer division translates the strict lower and weak upper inequalities
without introducing an erroneous lower-endpoint -1 correction. -/
theorem shellTrapezoidFloorWindow_iff
    (a b c p : ℕ) (hc : 0 < c) :
    (a / c < p ∧ p ≤ b / c) ↔
      (a < p * c ∧ p * c ≤ b) := by
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨(Nat.div_lt_iff_lt_mul hc).1 hl,
      (Nat.le_div_iff_mul_le hc).1 hu⟩
  · rintro ⟨hl, hu⟩
    exact ⟨(Nat.div_lt_iff_lt_mul hc).2 hl,
      (Nat.le_div_iff_mul_le hc).2 hu⟩

/-- The translated true-prime cofactor population, including c=1. -/
def shellTrapezoidPrimeCofactorCount (r T k c : ℕ) : ℝ :=
  shellTrapezoidPrimePi (shellTrapezoidUpper r T k / c) -
    shellTrapezoidPrimePi (shellTrapezoidLower r T k / c)

/-- Exact finite prime-fibre equality with both floor endpoints. -/
theorem shellTrapezoidPrimeCofactorCount_eq_Ioc
    (r T k c : ℕ) :
    shellTrapezoidPrimeCofactorCount r T k c =
      ∑ p ∈ Finset.Ioc
        (shellTrapezoidLower r T k / c)
        (shellTrapezoidUpper r T k / c),
        if p.Prime then (1 : ℝ) else 0 := by
  have hdiv : shellTrapezoidLower r T k / c ≤
      shellTrapezoidUpper r T k / c :=
    Nat.div_le_div_right (shellTrapezoidLower_le_upper r T k)
  unfold shellTrapezoidPrimeCofactorCount
  rw [shellTrapezoidPrimePi_Ioc _ _ hdiv]

/-- Real coefficient of the actual Mobius cofactor, not a positive density. -/
def shellTrapezoidMu (c : ℕ) : ℝ :=
  ((μ c : ℤ) : ℝ)

/-- Low-cofactor high-prime incidence for any chosen prime-count function. -/
def shellTrapezoidLowCofactorSum
    (piModel : ℕ → ℝ) (r T k : ℕ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 T,
    shellTrapezoidMu c *
      (piModel (shellTrapezoidUpper r T k / c) -
        piModel (shellTrapezoidLower r T k / c))

/-- Finite, literal actual-pi = smooth-model + discrepancy identity.
The actual discrepancy is retained and not estimated. -/
theorem shellTrapezoidLowCofactor_pi_eq_model_add_error
    (piActual piModel : ℕ → ℝ) (r T k : ℕ) :
    shellTrapezoidLowCofactorSum piActual r T k =
      shellTrapezoidLowCofactorSum piModel r T k +
      shellTrapezoidLowCofactorSum
        (fun n => piActual n - piModel n) r T k := by
  unfold shellTrapezoidLowCofactorSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  ring

/-- Same identity after averaging all 2T+1 translated shells. -/
theorem shellTrapezoidLowCofactor_mean_pi_eq_model_add_error
    (piActual piModel : ℕ → ℝ) (r T : ℕ) :
    shellTrapezoidMean T
        (fun k => shellTrapezoidLowCofactorSum piActual r T k) =
      shellTrapezoidMean T
        (fun k => shellTrapezoidLowCofactorSum piModel r T k) +
      shellTrapezoidMean T
        (fun k => shellTrapezoidLowCofactorSum
          (fun n => piActual n - piModel n) r T k) := by
  unfold shellTrapezoidMean
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact shellTrapezoidLowCofactor_pi_eq_model_add_error
    piActual piModel r T k

/-- An actual prime P times a cofactor C contributes only on admitted sites.
Keeping this expression as a genuine prime indicator prevents an implicit
replacement by Li and preserves zero/squareful factors. -/
noncomputable def shellTrapezoidPrimeProductIndicator
    (r T k p c : ℕ) : ℝ := by
  classical
  exact if p.Prime ∧ shellTrapezoidProductAdmitted r T k p c then 1 else 0

/-- High-cofactor sum in cofactor-first order. -/
def shellTrapezoidHighCofactorFirst
    (r T k : ℕ) (q : ℕ → ℕ → ℝ) : ℝ :=
  ∑ c ∈ Finset.Ioc T r,
    shellTrapezoidMu c *
      (∑ p ∈ Finset.Ioc r (shellTrapezoidUpper r T k), q p c)

/-- Exactly the same physical sum in prime-first order. -/
def shellTrapezoidHighPrimeFirst
    (r T k : ℕ) (q : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc r (shellTrapezoidUpper r T k),
    ∑ c ∈ Finset.Ioc T r, shellTrapezoidMu c * q p c

/-- Exact high-cofactor hyperbola switch, with original Mobius signs and
moving real-prime support intact. No bound on the off-diagonal is implied. -/
theorem shellTrapezoidHighCofactor_eq_primeFirst
    (r T k : ℕ) (q : ℕ → ℕ → ℝ) :
    shellTrapezoidHighCofactorFirst r T k q =
      shellTrapezoidHighPrimeFirst r T k q := by
  unfold shellTrapezoidHighCofactorFirst shellTrapezoidHighPrimeFirst
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Coefficient growth constraint from high-cofactor support. -/
theorem shellTrapezoidHighProduct_bound
    (r T k p c : ℕ)
    (hc : T < c) (hadmit : shellTrapezoidProductAdmitted r T k p c) :
    p * (T + 1) ≤ shellTrapezoidUpper r T k := by
  have hc' : T + 1 ≤ c := by omega
  have hmul := Nat.mul_le_mul_left p hc'
  exact hmul.trans hadmit.2

#print axioms shellTrapezoidFloorWindow_iff
#print axioms shellTrapezoidPrimeCofactorCount_eq_Ioc
#print axioms shellTrapezoidLowCofactor_mean_pi_eq_model_add_error
#print axioms shellTrapezoidHighCofactor_eq_primeFirst
#print axioms shellTrapezoidHighProduct_bound

end RHLean.Analysis
