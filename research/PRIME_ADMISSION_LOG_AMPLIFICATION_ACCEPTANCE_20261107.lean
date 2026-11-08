import «research.PRIME_ADMISSION_LOG_AMPLIFICATION_20261107»

/-!
# Exact type acceptance for prime-admission logarithmic amplification

These examples deliberately spell out the arithmetic endpoint and all
permitted hypotheses.  A generic recurrence parameter or a hidden signed
cancellation assumption cannot replace the original-source theorem.
The zero-limit proposition is a proof target, not an accepted theorem.
-/

noncomputable section

set_option autoImplicit false

open scoped BigOperators
open RHLean.Proof

example (R : ℕ) (K : ℝ) :
    squareRootHistoricalK R ≤ K ↔ LowerMertensCriticalEnvelope R K :=
  squareRootHistoricalK_le_iff R K

example (X : ℕ) (A : ℝ) :
    squareRootAmplificationMax X ≤ A ↔
      0 ≤ A ∧ ∀ R : ℕ, 2 ≤ R → squareRootEndpoint R ≤ X →
        squareRootEndpointAmplification R ≤ A :=
  squareRootAmplificationMax_le_iff X A

example :
    SquareRootMertensEndpointAmplificationStatement ↔
      ∃ A : ℝ, 0 ≤ A ∧ ∀ X : ℕ, squareRootAmplificationMax X ≤ A :=
  squareRootMertensEndpointAmplification_iff_boundedRunningMax

example : squareRootHistoricalK 2 = 1 := squareRootHistoricalK_two

example : squareRootEndpointAmplification 2 = 1 :=
  squareRootEndpointAmplification_two

example (W F m : ℝ) (hW : 0 < W) :
    Real.log (1 + (F - m) ^ 2 / W) =
      Real.log (1 + F ^ 2 / W) +
        Real.log (1 + (m ^ 2 - 2 * F * m) / (W + F ^ 2)) := by
  exact primeAdmissionLogPotential_step W F m hW

example (R p : ℕ) (hR : 2 ≤ R)
    (hp : R ≤ p) (hpX : p ≤ squareRootEndpoint R) :
    eulerAdmissibleCenteredRealState R p =
      eulerAdmissibleCenteredRealState R (p - 1) -
        eulerAdmissibleAdmissionDebtReal R p :=
  eulerAdmissibleCenteredRealState_step R p hR hp hpX

example (R : ℕ) (hR : 2 ≤ R) :
    eulerAdmissibleCenteredRealState R (squareRootEndpoint R) =
      (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ)) :=
  eulerAdmissibleCenteredRealState_terminal R hR

example (R : ℕ) (hR : 2 ≤ R) :
    Real.log (1 + squareRootEndpointAmplification R) =
      Real.log (1 + ((eulerAdmissibleLowPopulation R).re - 1) ^ 2 /
        ((R : ℝ) ^ 2 * squareRootHistoricalK R)) +
        ∑ p ∈ Finset.Icc R (squareRootEndpoint R),
          Real.log (1 +
            ((eulerAdmissibleAdmissionDebtReal R p) ^ 2 -
              2 * eulerAdmissibleCenteredRealState R (p - 1) *
                eulerAdmissibleAdmissionDebtReal R p) /
            ((R : ℝ) ^ 2 * squareRootHistoricalK R +
              (eulerAdmissibleCenteredRealState R (p - 1)) ^ 2)) :=
  squareRootEndpointAmplification_log_identity R hR

-- Every value of the original amplification, at every valid root, is used.
-- No finite test range is substituted for either of these universal types.
example (R : ℕ) (hR : 2 ≤ R) :
    Real.log (1 + squareRootEndpointAmplification R) =
      eulerAdmissibleLogReturn R
        ((R : ℝ) ^ 2 * squareRootHistoricalK R) :=
  squareRootEndpointAmplification_log_eq_primeAdmission R hR

example (X : ℕ) (ε : ℝ) (hX : 2 ≤ X) (hε : 0 ≤ ε) :
    squareRootAmplificationLogRatio X ≤ ε ↔
      ∀ R : ℕ, 2 ≤ R → squareRootEndpoint R ≤ X →
        eulerAdmissibleLogReturn R
            ((R : ℝ) ^ 2 * squareRootHistoricalK R) ≤
          ε * Real.log (X : ℝ) :=
  squareRootAmplificationLogRatio_le_iff_primeAdmissionLogReturn X ε hX hε
