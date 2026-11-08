import RHLean.Proof.PrimeAdmissionLogPotential
import RHLean.Proof.SquareRootAmplificationLogGrowth
import «research.EULER_ADMISSIBLE_PRIME_POPULATION_CODIV_20261028»

/-!
# Original square-root amplification in prime-admission logarithms

At the fixed physical endpoint `X_R = R^2 - 1`, reuse the genuine
product-admissible Euler population and its proved chronological update.
Every candidate `p` from `R` through `X_R` is included: a prime contributes
`M(floor(X_R/p))`, a composite contributes zero, and the prime `p = R`
is retained when present.  Subtract the exceptional unit source before
taking the square.

The complete logarithmic return is exactly `log (1 + alpha_R)`, with
`alpha_R` using the original finite historical maximum `K_R`.  In
particular the mixed term `-2 * F * m` remains inside every logarithm.
The result is an identity on the original Mertens source.  It supplies
neither a bound on the complete signed return nor a proof that the
limiting logarithmic power-growth ratio is zero.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- The real, unit-centered value of the actual admitted Euler population. -/
def eulerAdmissibleCenteredRealState (R p : ℕ) : ℝ :=
  (eulerAdmissibleState R p).re - 1

/-- Real cofactor contribution at a candidate admission; composites give zero. -/
def eulerAdmissibleAdmissionDebtReal (R p : ℕ) : ℝ :=
  (eulerAdmissibleAdmissionDebt R p).re

/-- The centered real update is supplied by the arithmetic admission theorem,
not postulated as a new recurrence hypothesis. -/
theorem eulerAdmissibleCenteredRealState_step
    (R p : ℕ) (hR : 2 ≤ R)
    (hp : R ≤ p) (hpX : p ≤ squareRootEndpoint R) :
    eulerAdmissibleCenteredRealState R p =
      eulerAdmissibleCenteredRealState R (p - 1) -
        eulerAdmissibleAdmissionDebtReal R p := by
  unfold eulerAdmissibleCenteredRealState eulerAdmissibleAdmissionDebtReal
  rw [eulerAdmissibleState_step R p hR hp hpX]
  simp only [Complex.sub_re]
  ring

/-- The initial state includes exactly the genuine products of primes `< R`. -/
theorem eulerAdmissibleCenteredRealState_initial (R : ℕ) :
    eulerAdmissibleCenteredRealState R (R - 1) =
      (eulerAdmissibleLowPopulation R).re - 1 := rfl

/-- Full admission recovers the original integer Mertens numerator, including
its shift by one. -/
theorem eulerAdmissibleCenteredRealState_terminal
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAdmissibleCenteredRealState R (squareRootEndpoint R) =
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)) := by
  unfold eulerAdmissibleCenteredRealState
  rw [eulerAdmissibleState_terminal R hR,
    ← mertensSummatoryInt_cast (squareRootEndpoint R)]
  simp only [Complex.intCast_re, Int.cast_sub, Int.cast_one]

/-- At a genuine prime the daughter is the actual lower Mertens prefix. -/
theorem eulerAdmissibleAdmissionDebtReal_of_prime
    (R p : ℕ) (hp : p.Prime) :
    eulerAdmissibleAdmissionDebtReal R p =
      ((mertensSummatoryInt (squareRootEndpoint R / p) : ℤ) : ℝ) := by
  unfold eulerAdmissibleAdmissionDebtReal eulerAdmissibleAdmissionDebt
  rw [ite_eq_left hp, ← mertensSummatoryInt_cast (squareRootEndpoint R / p)]
  simp only [Complex.intCast_re]

/-- A composite candidate introduces no family. -/
theorem eulerAdmissibleAdmissionDebtReal_of_not_prime
    (R p : ℕ) (hp : ¬p.Prime) :
    eulerAdmissibleAdmissionDebtReal R p = 0 := by
  simp [eulerAdmissibleAdmissionDebtReal, eulerAdmissibleAdmissionDebt, hp]

/-- Every admitted late-prime daughter lies strictly inside the original
historical range.  The inclusive boundary `p = R` is covered. -/
theorem eulerAdmissibleAdmissionCutoff_lt_root
    (R p : ℕ) (hR : 2 ≤ R) (hp : R ≤ p) :
    squareRootEndpoint R / p < R := by
  have hpPos : 0 < p := by omega
  have hX : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hsqPos : 0 < R ^ 2 := by positivity
    omega
  apply (Nat.div_lt_iff_lt_mul hpPos).2
  calc
    squareRootEndpoint R < R ^ 2 := hX
    _ = R * R := by ring
    _ ≤ R * p := Nat.mul_le_mul_left R hp

/-- All primes in the top reciprocal band contribute the same daughter `1`.
The logarithmic calculation therefore retains their coherent mixed terms. -/
theorem eulerAdmissibleAdmissionDebtReal_eq_one_of_top_band
    (R p : ℕ) (hp : p.Prime)
    (hhalf : squareRootEndpoint R / 2 < p)
    (hpX : p ≤ squareRootEndpoint R) :
    eulerAdmissibleAdmissionDebtReal R p = 1 := by
  have hhigh : squareRootEndpoint R < (1 + 1) * p := by
    have h := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).1 hhalf
    omega
  have hdiv : squareRootEndpoint R / p = 1 := by
    apply Nat.div_eq_of_lt_le
    · simpa using hpX
    · exact hhigh
  rw [eulerAdmissibleAdmissionDebtReal_of_prime R p hp, hdiv]
  simp [mertensSummatoryInt_eq_Icc]

/-- Exact logarithmic update on each actual candidate admission. -/
theorem eulerAdmissibleCenteredRealState_log_step
    (R p : ℕ) (W : ℝ) (hR : 2 ≤ R) (hW : 0 < W)
    (hp : R ≤ p) (hpX : p ≤ squareRootEndpoint R) :
    primeAdmissionLogPotential W (eulerAdmissibleCenteredRealState R p) =
      primeAdmissionLogPotential W (eulerAdmissibleCenteredRealState R (p - 1)) +
        primeAdmissionLogIncrement W
          (eulerAdmissibleCenteredRealState R (p - 1))
          (eulerAdmissibleAdmissionDebtReal R p) := by
  rw [eulerAdmissibleCenteredRealState_step R p hR hp hpX]
  exact primeAdmissionLogPotential_step W
    (eulerAdmissibleCenteredRealState R (p - 1))
    (eulerAdmissibleAdmissionDebtReal R p) hW

/-- Composite candidates are literal zero increments in the logarithmic sum. -/
theorem eulerAdmissibleLogIncrement_of_not_prime
    (R p : ℕ) (W : ℝ) (hp : ¬p.Prime) :
    primeAdmissionLogIncrement W
      (eulerAdmissibleCenteredRealState R (p - 1))
      (eulerAdmissibleAdmissionDebtReal R p) = 0 := by
  rw [eulerAdmissibleAdmissionDebtReal_of_not_prime R p hp]
  exact primeAdmissionLogIncrement_zero W _

/-- Telescope over every actual admission from `R` through `X_R`, keeping the
same historical denominator and the complete signed increment at each step. -/
theorem eulerAdmissibleCenteredRealState_log_telescope
    (R : ℕ) (W : ℝ) (hR : 2 ≤ R) (hW : 0 < W) :
    primeAdmissionLogPotential W
        (eulerAdmissibleCenteredRealState R (squareRootEndpoint R)) =
      primeAdmissionLogPotential W (eulerAdmissibleCenteredRealState R (R - 1)) +
        ∑ p ∈ Finset.Icc R (squareRootEndpoint R),
          primeAdmissionLogIncrement W
            (eulerAdmissibleCenteredRealState R (p - 1))
            (eulerAdmissibleAdmissionDebtReal R p) := by
  let X := squareRootEndpoint R
  have hRle : R ≤ X := by
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    dsimp [X, squareRootEndpoint]
    omega
  let f : ℕ → ℝ := fun n =>
    primeAdmissionLogPotential W (eulerAdmissibleCenteredRealState R (n - 1))
  have hset : Finset.Icc R X = Finset.Ico R (X + 1) := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have htel :
      (∑ p ∈ Finset.Icc R X,
          (primeAdmissionLogPotential W (eulerAdmissibleCenteredRealState R p) -
            primeAdmissionLogPotential W
              (eulerAdmissibleCenteredRealState R (p - 1)))) =
        primeAdmissionLogPotential W (eulerAdmissibleCenteredRealState R X) -
          primeAdmissionLogPotential W
            (eulerAdmissibleCenteredRealState R (R - 1)) := by
    calc
      _ = ∑ p ∈ Finset.Ico R (X + 1), (f (p + 1) - f p) := by
        rw [hset]
        apply Finset.sum_congr rfl
        intro p _hp
        simp [f]
      _ = f (X + 1) - f R := by
        rw [Finset.sum_Ico_sub f (by omega : R ≤ X + 1)]
      _ = _ := by simp [f]
  have hstep :
      (∑ p ∈ Finset.Icc R X,
        primeAdmissionLogIncrement W
          (eulerAdmissibleCenteredRealState R (p - 1))
          (eulerAdmissibleAdmissionDebtReal R p)) =
      ∑ p ∈ Finset.Icc R X,
        (primeAdmissionLogPotential W (eulerAdmissibleCenteredRealState R p) -
          primeAdmissionLogPotential W
            (eulerAdmissibleCenteredRealState R (p - 1))) := by
    apply Finset.sum_congr rfl
    intro p hp
    rcases Finset.mem_Icc.mp hp with ⟨hpR, hpX⟩
    rw [primeAdmissionLogIncrement_eq_sub W
      (eulerAdmissibleCenteredRealState R (p - 1))
      (eulerAdmissibleAdmissionDebtReal R p) hW]
    rw [← eulerAdmissibleCenteredRealState_step R p hR hpR
      (by simpa [X] using hpX)]
  change primeAdmissionLogPotential W (eulerAdmissibleCenteredRealState R X) =
    primeAdmissionLogPotential W (eulerAdmissibleCenteredRealState R (R - 1)) +
      ∑ p ∈ Finset.Icc R X,
        primeAdmissionLogIncrement W
          (eulerAdmissibleCenteredRealState R (p - 1))
          (eulerAdmissibleAdmissionDebtReal R p)
  linarith only [htel, hstep]

/-- The complete signed logarithmic return, including its initial low-prime
population.  A bound on this whole expression is the open arithmetic task. -/
def eulerAdmissibleLogReturn (R : ℕ) (W : ℝ) : ℝ :=
  primeAdmissionLogPotential W ((eulerAdmissibleLowPopulation R).re - 1) +
    ∑ p ∈ Finset.Icc R (squareRootEndpoint R),
      primeAdmissionLogIncrement W
        (eulerAdmissibleCenteredRealState R (p - 1))
        (eulerAdmissibleAdmissionDebtReal R p)

/-- The full signed return is exactly the original shifted Mertens logarithm,
for every fixed positive normalization. -/
theorem eulerAdmissibleLogReturn_eq_endpoint
    (R : ℕ) (W : ℝ) (hR : 2 ≤ R) (hW : 0 < W) :
    eulerAdmissibleLogReturn R W =
      primeAdmissionLogPotential W
        (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)) := by
  have h := eulerAdmissibleCenteredRealState_log_telescope R W hR hW
  rw [eulerAdmissibleCenteredRealState_terminal R hR,
    eulerAdmissibleCenteredRealState_initial R] at h
  exact h.symm

/-- With the exact historical maximum `K_R`, the logarithmic return is the
original endpoint amplification.  No cancellation bound is an assumption. -/
theorem squareRootEndpointAmplification_log_eq_primeAdmission
    (R : ℕ) (hR : 2 ≤ R) :
    Real.log (1 + squareRootEndpointAmplification R) =
      eulerAdmissibleLogReturn R
        ((R : ℝ) ^ 2 * squareRootHistoricalK R) := by
  have hW : 0 < (R : ℝ) ^ 2 * squareRootHistoricalK R :=
    squareRootAmplificationDenominator_pos (by omega : 1 ≤ R)
  have h := (eulerAdmissibleLogReturn_eq_endpoint R
    ((R : ℝ) ^ 2 * squareRootHistoricalK R) hR hW).symm
  simpa only [squareRootEndpointAmplification, primeAdmissionLogPotential] using h

/-- Expanded original-amplification identity.  Both the centered initial
population and every signed mixed term remain visible in the statement. -/
theorem squareRootEndpointAmplification_log_identity
    (R : ℕ) (hR : 2 ≤ R) :
    Real.log (1 + squareRootEndpointAmplification R) =
      Real.log (1 + ((eulerAdmissibleLowPopulation R).re - 1) ^ 2 /
        ((R : ℝ) ^ 2 * squareRootHistoricalK R)) +
        ∑ p ∈ Finset.Icc R (squareRootEndpoint R),
          Real.log (1 +
            ((eulerAdmissibleAdmissionDebtReal R p) ^ 2 -
              2 * eulerAdmissibleCenteredRealState R (p - 1) *
                eulerAdmissibleAdmissionDebtReal R p) /
            ((R : ℝ) ^ 2 * squareRootHistoricalK R +
              (eulerAdmissibleCenteredRealState R (p - 1)) ^ 2)) := by
  simpa only [eulerAdmissibleLogReturn, primeAdmissionLogPotential,
    primeAdmissionLogIncrement] using
    squareRootEndpointAmplification_log_eq_primeAdmission R hR

/-- Direct consumer for the user's running-maximum ratio.  A proposed bound
must control the complete signed prime-admission return at every admitted
square endpoint, with the same right side `epsilon * log X`.  This equivalence
does not supply that bound or assert convergence to zero. -/
theorem squareRootAmplificationLogRatio_le_iff_primeAdmissionLogReturn
    (X : ℕ) (ε : ℝ) (hX : 2 ≤ X) (hε : 0 ≤ ε) :
    squareRootAmplificationLogRatio X ≤ ε ↔
      ∀ R : ℕ, 2 ≤ R → squareRootEndpoint R ≤ X →
        eulerAdmissibleLogReturn R
            ((R : ℝ) ^ 2 * squareRootHistoricalK R) ≤
          ε * Real.log (X : ℝ) := by
  rw [squareRootAmplificationLogRatio_le_iff X ε hX hε]
  constructor
  · intro h R hR hRX
    rw [← squareRootEndpointAmplification_log_eq_primeAdmission R hR]
    exact h R hR hRX
  · intro h R hR hRX
    rw [squareRootEndpointAmplification_log_eq_primeAdmission R hR]
    exact h R hR hRX

end RHLean.Proof
