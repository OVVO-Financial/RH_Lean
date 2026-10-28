import Mathlib
import «research.EULER_ADMISSIBLE_WEIGHTED_CODIV_20261028»

/-!
# Complete chronological admissible-prime signed energy and Co-Div seam

This is the energy of the ONE evolving genuine product-admissible Euler
population. The endpoint is fixed at X=R^2-1. The insertion of p>=R
contributes -M(floor(X/p)) for p prime and nothing for composite p.

There is no family independence hypothesis. The mixed signed return is
retained as a real scalar and is not replaced by the sum of squared
prime-family amplitudes.  The native weighted Co-Div enters via the
exact self-dual Euler endpoint, not by claiming pair-by-pair equality
between two different Gram coordinate systems.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- The literal diagonal (sum of squares), NOT the square of the prime debt. -/
def eulerAdmissibleChronologicalDiagonal (R : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc R (squareRootEndpoint R),
    Complex.normSq (eulerAdmissibleAdmissionDebt R p)

/-- Original signed old-population/new-prime-family mixed interaction. -/
def eulerAdmissibleChronologicalMixed (R : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc R (squareRootEndpoint R),
    2 * ((starRingEnd ℂ (eulerAdmissibleState R (p - 1))) *
      eulerAdmissibleAdmissionDebt R p).re

/-- Exact chronological energy telescope. The source at final admission
is the actual Mertens value, not an independent-sign model. -/
theorem eulerAdmissibleChronologicalEnergy_identity
    (R : ℕ) (hR : 2 ≤ R) :
    Complex.normSq (mertensSummatory (squareRootEndpoint R)) =
      Complex.normSq (eulerAdmissibleLowPopulation R) +
        eulerAdmissibleChronologicalDiagonal R -
        eulerAdmissibleChronologicalMixed R := by
  let X := squareRootEndpoint R
  have hRle : R ≤ X := by
    have hm : R + 1 ≤ R ^ 2 := by nlinarith
    dsimp [X, squareRootEndpoint]
    omega
  have hstep :
      (∑ p ∈ Finset.Icc R X,
          (Complex.normSq (eulerAdmissibleState R p) -
            Complex.normSq (eulerAdmissibleState R (p - 1)))) =
        ∑ p ∈ Finset.Icc R X,
          (Complex.normSq (eulerAdmissibleAdmissionDebt R p) -
            2 * ((starRingEnd ℂ (eulerAdmissibleState R (p - 1))) *
              eulerAdmissibleAdmissionDebt R p).re) := by
    apply Finset.sum_congr rfl
    intro p hp
    rcases Finset.mem_Icc.mp hp with ⟨hpR, hpX⟩
    exact eulerAdmissibleState_energy_step R p hR hpR (by simpa [X] using hpX)
  let f : ℕ → ℝ := fun n => Complex.normSq (eulerAdmissibleState R (n - 1))
  have hset : Finset.Icc R X = Finset.Ico R (X + 1) := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have htel :
      (∑ p ∈ Finset.Icc R X,
          (Complex.normSq (eulerAdmissibleState R p) -
            Complex.normSq (eulerAdmissibleState R (p - 1)))) =
        Complex.normSq (eulerAdmissibleState R X) -
          Complex.normSq (eulerAdmissibleState R (R - 1)) := by
    calc
      _ = ∑ p ∈ Finset.Ico R (X + 1), (f (p + 1) - f p) := by
        rw [hset]
        apply Finset.sum_congr rfl
        intro p hp
        have hp1 : p + 1 - 1 = p := by omega
        simp [f, hp1]
      _ = f (X + 1) - f R := by
        rw [Finset.sum_Ico_sub f (by omega : R ≤ X + 1)]
      _ = _ := by
        have hX : X + 1 - 1 = X := by omega
        simp [f, hX]
  have hlast := eulerAdmissibleState_terminal R hR
  have hfirst := eulerAdmissibleState_initial R
  rw [← hstep] 
  rw [htel]
  rw [show eulerAdmissibleState R X = mertensSummatory X from
    (by simpa [X] using hlast)]
  rw [hfirst]
  unfold eulerAdmissibleChronologicalDiagonal
    eulerAdmissibleChronologicalMixed
  rw [← Finset.sum_sub_distrib]
  rfl

/-- The mixed return is the exact payment needed against the positive
chronological diagonal and the prepared low-population energy. This statement
has no bound and does NOT itself imply any exponent improvement. -/
theorem eulerAdmissibleChronologicalMixed_eq_required_payment
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAdmissibleChronologicalMixed R =
      Complex.normSq (eulerAdmissibleLowPopulation R) +
        eulerAdmissibleChronologicalDiagonal R -
        Complex.normSq (mertensSummatory (squareRootEndpoint R)) := by
  have h := eulerAdmissibleChronologicalEnergy_identity R hR
  linarith

/-- Explicit scalar interface to the ORIGINAL weighted Co-Div floor Gram.
It does not assert an occurrence-preserving pair bijection between the two
different Gram expansions. -/
theorem eulerAdmissibleChronologicalMixed_eq_weighted_CoDiv_payment
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAdmissibleChronologicalMixed R =
      Complex.normSq (eulerAdmissibleLowPopulation R) +
        eulerAdmissibleChronologicalDiagonal R -
        Complex.normSq
          (2 * mertensSummatory (R - 1) -
            (eulerHybridDiagonal R +
              2 * (eulerAdmissibleWeightedCo R -
                eulerAdmissibleWeightedDiv R))) := by
  have hgram := eulerAdmissible_weighted_CoDiv_eq_primePopulation R hR
  have hendpoint := eulerAdmissible_endpoint_eq_low_add_innovation R hR
  have hM :
      mertensSummatory (squareRootEndpoint R) =
        2 * mertensSummatory (R - 1) -
          (eulerHybridDiagonal R +
            2 * (eulerAdmissibleWeightedCo R -
              eulerAdmissibleWeightedDiv R)) := by
    rw [hgram, hendpoint]
    unfold eulerAdmissibleHighInnovation
    ring
  rw [eulerAdmissibleChronologicalMixed_eq_required_payment R hR, hM]

#print axioms eulerAdmissibleChronologicalEnergy_identity
#print axioms eulerAdmissibleChronologicalMixed_eq_required_payment
#print axioms eulerAdmissibleChronologicalMixed_eq_weighted_CoDiv_payment

end RHLean.Proof
