import Mathlib
import «research.EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027»
import RHLean.Proof.SquareRootAmplificationClosure
import RHLean.Analysis.MertensEnergyRHForward

/-!
# Original finite-C to critical-energy amplification handoff

The pointwise Newton coefficient identity and exact triple Fubini map the
literal PR #1034 bilinear Q_R to 2*M(R-1)-M(R^2-1). This module then records
an honest conditional finite-C estimate, with one scalar C independent of R
and the historical envelope K.

The universal signed estimate IS NOT PROVED HERE; it is a hypothesis.
Its finite-C -> finite-A -> Mertens energy -> RH consequence is proved by
consuming the repository's already certified implication chain.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- The arithmetic endpoint formula, coefficientwise and floor-faithfully,
for R>=2. Neither asymptotics nor a sign hypothesis is involved. -/
theorem eulerSelfDualBilinear_eq_two_mertens_sub_endpoint
    (R : ℕ) (hR : 2 ≤ R) :
    eulerSelfDualBilinear R =
      2 * mertensSummatory (R - 1) -
        mertensSummatory (squareRootEndpoint R) := by
  let X : ℕ := squareRootEndpoint R
  have hR2 : X < R * R := by
    have hRpos : 0 < R ^ 2 := by positivity
    have hlt : R ^ 2 - 1 < R ^ 2 :=
      Nat.sub_lt hRpos (by norm_num)
    simpa [X, squareRootEndpoint, pow_two] using hlt
  have hprefix : R - 1 ≤ X := by
    dsimp [X, squareRootEndpoint]
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hfilter :
      (Finset.Icc 1 X).filter (fun n => n < R) =
        Finset.Icc 1 (R - 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hsum :
      (∑ n ∈ Finset.Icc 1 X,
        ((eulerSelfDualConvolutionCoefficient R n : ℤ) : ℂ)) =
        2 * (∑ n ∈ Finset.Icc 1 (R - 1), (((μ n : ℤ) : ℂ))) -
          ∑ n ∈ Finset.Icc 1 X, (((μ n : ℤ) : ℂ)) := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 X,
          (2 * (if n < R then (((μ n : ℤ) : ℂ)) else 0) -
            (((μ n : ℤ) : ℂ))) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
        rw [eulerSelfDualConvolutionCoefficient_eq_signed_moebius
            R n hR (lt_of_le_of_lt hnX hR2)]
        push_cast
        by_cases hnr : n < R
        · simp [hnr]
        · simp [hnr]
      _ =
        2 * (∑ n ∈ Finset.Icc 1 X,
          if n < R then (((μ n : ℤ) : ℂ)) else 0) -
          ∑ n ∈ Finset.Icc 1 X, (((μ n : ℤ) : ℂ)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ =
        2 * (∑ n ∈ Finset.Icc 1 (R - 1), (((μ n : ℤ) : ℂ))) -
          ∑ n ∈ Finset.Icc 1 X, (((μ n : ℤ) : ℂ)) := by
        rw [← Finset.sum_filter, hfilter]
  calc
    eulerSelfDualBilinear R =
        ∑ n ∈ Finset.Icc 1 X,
          ((eulerSelfDualConvolutionCoefficient R n : ℤ) : ℂ) := by
      simpa [X] using eulerSelfDualBilinear_eq_convolutionSummatory R hR
    _ =
        2 * (∑ n ∈ Finset.Icc 1 (R - 1), (((μ n : ℤ) : ℂ))) -
          ∑ n ∈ Finset.Icc 1 X, (((μ n : ℤ) : ℂ)) := hsum
    _ = 2 * mertensSummatory (R - 1) -
        mertensSummatory (squareRootEndpoint R) := by
      rw [← mertensSummatory_eq_sum_Icc (R - 1),
        ← mertensSummatory_eq_sum_Icc X]
      rfl

/-- Original finite-C estimate, with a universal scalar C and *every*
valid historical critical envelope K. This is the OPEN number-theoretic
statement, not an axiom or a bound asserted by this file. -/
def EulerSelfDualFiniteCStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, ∀ K : ℝ, 2 ≤ R →
      LowerMertensCriticalEnvelope R K →
        ‖eulerSelfDualBilinear R‖ ≤
          C * (R : ℝ) * Real.sqrt K

/-- Conditional handoff: any fixed historical finite-C constant produces
a fixed finite-A endpoint amplification constant (C+3)^2.
No assumption about a subunit contraction is required. -/
theorem squareRootEndpointAmplification_of_eulerFiniteC
    (hFiniteC : EulerSelfDualFiniteCStatement) :
    SquareRootMertensEndpointAmplificationStatement := by
  rcases hFiniteC with ⟨C, hC, hBound⟩
  refine ⟨(C + 3) ^ 2, sq_nonneg _, ?_⟩
  intro R K hR hK
  obtain ⟨hKnonneg, hHistorical⟩ := hK
  have hRp : R - 1 < R := by omega
  have hMprevious :=
    hHistorical (R - 1) hRp
  have hMzero := hHistorical 0 (by omega : 0 < R)
  have hMzeroVal : mertensSummatoryInt 0 = 0 := by
    simp [mertensSummatoryInt]
  have hKone : (1 : ℝ) ≤ K := by
    simpa [hMzeroVal] using hMzero
  have hSnonneg : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hSsq : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hKnonneg
  have hSone : (1 : ℝ) ≤ Real.sqrt K := by
    simpa using Real.sqrt_le_sqrt hKone
  have hRone : (1 : ℝ) ≤ R := by
    exact_mod_cast (show 1 ≤ R by omega)
  have hRN : (0 : ℝ) ≤ (R : ℝ) := by positivity
  have hRSnonneg : 0 ≤ (R : ℝ) * Real.sqrt K :=
    mul_nonneg hRN hSnonneg
  have hRSone : (1 : ℝ) ≤ (R : ℝ) * Real.sqrt K := by
    nlinarith
  have hMpreviousNorm :
      ‖mertensSummatory (R - 1) - 1‖ ^ 2 ≤
        K * (R : ℝ) := by
    change shiftedMertensEnergy (R - 1) ≤ K * (R : ℝ)
    rw [shiftedMertensEnergy_eq_intSquare]
    exact hMprevious
  have hKpos : (0 : ℝ) ≤ K := hKnonneg
  have hRpow : (R : ℝ) ≤ (R : ℝ) ^ 2 := by
    nlinarith
  have hMpreviousNorm2 :
      ‖mertensSummatory (R - 1) - 1‖ ^ 2 ≤
        ((R : ℝ) * Real.sqrt K) ^ 2 := by
    calc
      _ ≤ K * (R : ℝ) := hMpreviousNorm
      _ ≤ K * (R : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hRpow hKpos
      _ = ((R : ℝ) * Real.sqrt K) ^ 2 := by rw [hSsq]; ring
  have hMpreviousLinear :
      ‖mertensSummatory (R - 1) - 1‖ ≤
        (R : ℝ) * Real.sqrt K := by
    nlinarith [norm_nonneg (mertensSummatory (R - 1) - 1)]
  have hQ : ‖eulerSelfDualBilinear R‖ ≤
      C * (R : ℝ) * Real.sqrt K :=
    hBound R K hR ⟨hKnonneg, hHistorical⟩
  have hconserve :
      mertensSummatory (squareRootEndpoint R) - 1 =
        2 * (mertensSummatory (R - 1) - 1) +
          1 - eulerSelfDualBilinear R := by
    rw [eulerSelfDualBilinear_eq_two_mertens_sub_endpoint R hR]
    ring
  have htriangle :
      ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤
        2 * ‖mertensSummatory (R - 1) - 1‖ +
          1 + ‖eulerSelfDualBilinear R‖ := by
    rw [hconserve]
    calc
      ‖2 * (mertensSummatory (R - 1) - 1) + 1 -
          eulerSelfDualBilinear R‖ ≤
        ‖2 * (mertensSummatory (R - 1) - 1) + 1‖ +
          ‖eulerSelfDualBilinear R‖ := norm_sub_le _ _
      _ ≤
          (‖2 * (mertensSummatory (R - 1) - 1)‖ + ‖(1 : ℂ)‖) +
            ‖eulerSelfDualBilinear R‖ :=
        add_le_add_right (norm_add_le _ _) _
      _ = 2 * ‖mertensSummatory (R - 1) - 1‖ +
          1 + ‖eulerSelfDualBilinear R‖ := by
        simp
  have hCnonneg : 0 ≤ C + 3 := by linarith
  have hrightNonneg : 0 ≤ (C + 3) * (R : ℝ) * Real.sqrt K :=
    mul_nonneg (mul_nonneg hCnonneg hRN) hSnonneg
  have hendpointLinear :
      ‖mertensSummatory (squareRootEndpoint R) - 1‖ ≤
        (C + 3) * (R : ℝ) * Real.sqrt K := by
    calc
      _ ≤ 2 * ‖mertensSummatory (R - 1) - 1‖ +
          1 + ‖eulerSelfDualBilinear R‖ := htriangle
      _ ≤ 2 * ((R : ℝ) * Real.sqrt K) +
          1 + (C * (R : ℝ) * Real.sqrt K) := by linarith
      _ ≤ (C + 3) * (R : ℝ) * Real.sqrt K := by
        nlinarith [hRSone]
  rw [← shiftedMertensEnergy_eq_intSquare (squareRootEndpoint R)]
  have hsqBound :
      ‖mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 ≤
        ((C + 3) * (R : ℝ) * Real.sqrt K) ^ 2 := by
    nlinarith [norm_nonneg
      (mertensSummatory (squareRootEndpoint R) - 1)]
  calc
    ‖mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 ≤
        ((C + 3) * (R : ℝ) * Real.sqrt K) ^ 2 := hsqBound
    _ = (C + 3) ^ 2 * (R : ℝ) ^ 2 * K := by rw [hSsq]; ring

/-- **Conditional RH export**: no new number-theoretic hypothesis is hidden.
The entire unproved payload is EulerSelfDualFiniteCStatement. -/
theorem riemannHypothesis_of_eulerSelfDualFiniteC
    (hFiniteC : EulerSelfDualFiniteCStatement) :
    RiemannHypothesis :=
  RHLean.Analysis.riemannHypothesis_of_mertensEnergy
    (mertensEnergyBounded_of_squareRootEndpointAmplification
      (squareRootEndpointAmplification_of_eulerFiniteC hFiniteC))

#print axioms eulerSelfDualBilinear_eq_two_mertens_sub_endpoint
#print axioms squareRootEndpointAmplification_of_eulerFiniteC
#print axioms riemannHypothesis_of_eulerSelfDualFiniteC

end RHLean.Proof
