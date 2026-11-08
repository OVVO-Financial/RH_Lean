import «research.SQUARE_ROOT_PRIME_PHASE_SIGNED_ENERGY_20261108»

/-!
# Exact actual-prime run contradiction and the spatial phase no-go

P_R-F_R is the discrete derivative of the genuine prime/floor-Li
backlog D_R. This source makes the precise endpoint-budget contradiction
reusable WITHOUT pretending that sqrt-prime half-phase uniformity
automatically controls prime counts.

Every arithmetic run lemma below uses actual prime counts. The final
abstract witnesses concern arbitrary real-valued hypothetical populations,
NOT an alternative population of the actual primes.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- Genuine square-endpoint count-minus-floor-Li backlog, as a real. -/
def squarePhaseRealBacklog (R : ℕ) : ℝ :=
  (vfMidPrimeFloorLiBacklog R : ℝ)

/-- Exactly telescope the actual prime-count error through any run. -/
theorem squarePhaseCountExcess_sum_eq_backlogDifference
    (A B : ℕ) (hAB : A ≤ B) :
    (∑ R ∈ Finset.Ico A B, squarePhaseCountExcess R) =
      squarePhaseRealBacklog B - squarePhaseRealBacklog A := by
  have hstep (R : ℕ) :
      squarePhaseCountExcess R =
        squarePhaseRealBacklog (R + 1) - squarePhaseRealBacklog R := by
    exact squarePhaseCountExcess_eq_floorLiBacklogStep R
  calc
    (∑ R ∈ Finset.Ico A B, squarePhaseCountExcess R) =
        ∑ R ∈ Finset.Ico A B,
          (squarePhaseRealBacklog (R + 1) -
            squarePhaseRealBacklog R) := by
      apply Finset.sum_congr rfl
      intro R _hR
      exact hstep R
    _ = squarePhaseRealBacklog B - squarePhaseRealBacklog A := by
      rw [Finset.sum_Ico_eq_sub _ hAB,
        Finset.sum_range_sub, Finset.sum_range_sub]
      ring

/-- A persistent actual-prime deficit must pay the historical backlog. -/
theorem squarePhasePersistentDeficit_forces_backlogDrop
    (A B : ℕ) (hAB : A ≤ B) (δ : ℝ)
    (hdeficit : ∀ R ∈ Finset.Ico A B,
      squarePhaseCountExcess R ≤ -δ) :
    squarePhaseRealBacklog B - squarePhaseRealBacklog A ≤
      -(((B - A : ℕ) : ℝ) * δ) := by
  rw [← squarePhaseCountExcess_sum_eq_backlogDifference A B hAB]
  calc
    (∑ R ∈ Finset.Ico A B, squarePhaseCountExcess R) ≤
        ∑ R ∈ Finset.Ico A B, -δ := by
      apply Finset.sum_le_sum
      intro R hR
      exact hdeficit R hR
    _ = -(((B - A : ℕ) : ℝ) * δ) := by
      simp [Nat.card_Ico]

/-- Symmetric persistent actual-prime surplus. -/
theorem squarePhasePersistentSurplus_forces_backlogRise
    (A B : ℕ) (hAB : A ≤ B) (δ : ℝ)
    (hsurplus : ∀ R ∈ Finset.Ico A B,
      δ ≤ squarePhaseCountExcess R) :
    ((B - A : ℕ) : ℝ) * δ ≤
      squarePhaseRealBacklog B - squarePhaseRealBacklog A := by
  rw [← squarePhaseCountExcess_sum_eq_backlogDifference A B hAB]
  calc
    ((B - A : ℕ) : ℝ) * δ =
        ∑ R ∈ Finset.Ico A B, δ := by
      simp [Nat.card_Ico]
    _ ≤ ∑ R ∈ Finset.Ico A B, squarePhaseCountExcess R := by
      apply Finset.sum_le_sum
      intro R hR
      exact hsurplus R hR

/-- Exact deficit contradiction gate with explicit, noncircular endpoint
errors EA, EB. Its use with a seven-eighths bound on D is a separate,
classical analytic prime-counting transfer. -/
theorem squarePhaseDeficitRun_le_endpointBudget
    (A B : ℕ) (hAB : A ≤ B) (δ EA EB : ℝ)
    (hA : |squarePhaseRealBacklog A| ≤ EA)
    (hB : |squarePhaseRealBacklog B| ≤ EB)
    (hdeficit : ∀ R ∈ Finset.Ico A B,
      squarePhaseCountExcess R ≤ -δ) :
    ((B - A : ℕ) : ℝ) * δ ≤ EA + EB := by
  have hdrop :=
    squarePhasePersistentDeficit_forces_backlogDrop A B hAB δ hdeficit
  have ha := (abs_le.mp hA).2
  have hb := (abs_le.mp hB).1
  linarith

theorem squarePhaseSurplusRun_le_endpointBudget
    (A B : ℕ) (hAB : A ≤ B) (δ EA EB : ℝ)
    (hA : |squarePhaseRealBacklog A| ≤ EA)
    (hB : |squarePhaseRealBacklog B| ≤ EB)
    (hsurplus : ∀ R ∈ Finset.Ico A B,
      δ ≤ squarePhaseCountExcess R) :
    ((B - A : ℕ) : ℝ) * δ ≤ EA + EB := by
  have hrise :=
    squarePhasePersistentSurplus_forces_backlogRise A B hAB δ hsurplus
  have ha := (abs_le.mp hA).1
  have hb := (abs_le.mp hB).2
  linarith

/-- If the accumulated deficit exceeds both possible endpoint errors, the
hypothetical run is impossible for the genuine primes. -/
theorem squarePhaseNoDeficitRun_exceeding_endpointBudget
    (A B : ℕ) (hAB : A ≤ B) (δ EA EB : ℝ)
    (hA : |squarePhaseRealBacklog A| ≤ EA)
    (hB : |squarePhaseRealBacklog B| ≤ EB)
    (hdeficit : ∀ R ∈ Finset.Ico A B,
      squarePhaseCountExcess R ≤ -δ)
    (hImpossible : EA + EB < ((B - A : ℕ) : ℝ) * δ) : False := by
  have hb :=
    squarePhaseDeficitRun_le_endpointBudget
      A B hAB δ EA EB hA hB hdeficit
  linarith

/-- Algebraic counterexample: perfect prime count and total placement in
the left half can coexist in an ABSTRACT prime-like population. The actual
prime sequence is never modified by this declaration. -/
theorem perfectCountYetNonuniformHalfPhase (F : ℝ) (hF : 0 < F) :
    ∃ P L : ℝ,
      P = F ∧ L = P ∧ P - F = 0 ∧ 0 < L - P / 2 := by
  refine ⟨F, F, rfl, rfl, by ring, ?_⟩
  linarith

/-- The converse abstract no-go is already proved in the original module. -/
theorem balancedHalfPhaseDoesNotBoundCountExcess (K : ℝ) :
    ∃ P L F : ℝ, 0 ≤ P ∧ 0 ≤ L ∧
      L - P / 2 = 0 ∧ P - F > K :=
  no_count_bound_from_halfPhaseUniformity K

end RHLean.Analysis
