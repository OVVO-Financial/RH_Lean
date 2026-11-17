import «research.NYMAN_RADICAL_INCREMENT_20261106»

/-!
Source-faithful regression for 20261117-census-0311-EST/DJ1 and the finite
profile underlying 20261117-referee-0413-EST/SG1. The same squarefree integer
has opposite signs at two legal quadratic long-middle cutoffs. The final
transport retains the full residual and its explicit moment/support premises.
No selected-head membership, infinite family, norm lower bound or RH claim
is asserted. All finite arithmetic is reduced by the kernel.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace RHLean.Analysis

private theorem divisors_210 : (210 : Nat).divisors =
    {1, 2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70, 105, 210} := by
  decide +kernel

private theorem moebius_210_profile :
    ArithmeticFunction.moebius 42 = (-1 : Int) ∧
    ArithmeticFunction.moebius 70 = (-1 : Int) ∧
    ArithmeticFunction.moebius 105 = (-1 : Int) ∧
    ArithmeticFunction.moebius 210 = (1 : Int) := by
  decide +kernel

private theorem log_210_profile :
    Real.log (42 : Real) + Real.log 70 + Real.log 105 =
      Real.log 210 + Real.log 1470 := by
  rw [<- Real.log_mul (by norm_num : (42 : Real) ≠ 0)
      (by norm_num : (70 : Real) ≠ 0),
    <- Real.log_mul (by norm_num : (42 * 70 : Real) ≠ 0)
      (by norm_num : (105 : Real) ≠ 0),
    <- Real.log_mul (by norm_num : (210 : Real) ≠ 0)
      (by norm_num : (1470 : Real) ≠ 0)]
  norm_num

/-- Both equality endpoints are retained; a divisor at the cutoff has log zero. -/
theorem nymanHighDivisorJump_210_profile (H : Nat)
    (hlo : 35 <= H) (hhi : H <= 42) :
    nymanHighDivisorJump H 210 = Real.log ((H : Real) ^ 2 / 1470) := by
  obtain ⟨h42, h70, h105, h210⟩ := moebius_210_profile
  have he : nymanHighDivisorJump H 210 = 2 * Real.log H - Real.log 1470 := by
    by_cases hH : H = 42
    · subst H
      have hf : (210 : Nat).divisors.filter (fun d => 42 < d) =
          {70, 105, 210} := by decide +kernel
      simp [nymanHighDivisorJump, hf, nymanLogKernel, h70, h105, h210]
      linarith [log_210_profile]
    · have hf : (210 : Nat).divisors.filter (fun d => H < d) =
          {42, 70, 105, 210} := by
        ext d
        simp only [divisors_210, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton]
        omega
      simp [nymanHighDivisorJump, hf, nymanLogKernel, h42, h70, h105, h210]
      linarith [log_210_profile]
  have hHz : (H : Real) ≠ 0 := by
    exact_mod_cast (show H ≠ 0 by omega)
  rw [he, Real.log_div (pow_ne_zero 2 hHz) (by norm_num), Real.log_pow]
  norm_num

theorem nymanHighDivisorJump_210_opposite_signs :
    nymanHighDivisorJump 38 210 < 0 ∧
      0 < nymanHighDivisorJump 39 210 := by
  rw [nymanHighDivisorJump_210_profile 38 (by norm_num) (by norm_num),
    nymanHighDivisorJump_210_profile 39 (by norm_num) (by norm_num)]
  constructor
  · exact Real.log_neg (by norm_num) (by norm_num)
  · exact Real.log_pos (by norm_num)

/-- The original quadratic ceiling, factor depth, and correction separation. -/
theorem nyman_210_long_middle_witness :
    Squarefree (210 : Nat) ∧ (210 : Nat).primeFactors = {2, 3, 5, 7} ∧
      ArithmeticFunction.moebius 210 = (1 : Int) ∧
      4 * 38 <= (210 : Nat) ∧ 210 <= (6 * ((38 ^ 2 + 5) / 6)) / 2 ∧
      8 * 38 < (6 * ((38 ^ 2 + 5) / 6) : Nat) ∧
      4 * 39 <= (210 : Nat) ∧ 210 <= (6 * ((39 ^ 2 + 5) / 6)) / 2 ∧
      8 * 39 < (6 * ((39 ^ 2 + 5) / 6) : Nat) := by
  decide +kernel

/-- Refutes only the all-head local parity rule, even on squarefree sources. -/
theorem not_nyman_long_middle_parity_nonnegative :
    ¬ (∀ H m : Nat, 2 <= H -> Squarefree m ->
      8 * H < 6 * ((H ^ 2 + 5) / 6) ->
      4 * H <= m -> m <= (6 * ((H ^ 2 + 5) / 6)) / 2 ->
      0 <= (ArithmeticFunction.moebius m : Real) * nymanHighDivisorJump H m) := by
  intro h
  have hh := h 38 210 (by norm_num) nyman_210_long_middle_witness.1
    (by norm_num) (by norm_num) (by norm_num)
  rw [moebius_210_profile.2.2.2] at hh
  norm_num at hh
  exact (not_le_of_gt nymanHighDivisorJump_210_opposite_signs.1) hh

/-- The signs transport to cumulative original floor sums, with the correct minus. -/
theorem nymanLogTail_210_opposite_steps :
    0 < nymanLogTail 38 210 - nymanLogTail 38 209 ∧
      nymanLogTail 39 210 - nymanLogTail 39 209 < 0 := by
  have h38 := nymanLogTail_step 38 210 (by norm_num)
  have h39 := nymanLogTail_step 39 210 (by norm_num)
  norm_num only at h38 h39
  rw [h38, h39]
  constructor
  · linarith [nymanHighDivisorJump_210_opposite_signs.1]
  · linarith [nymanHighDivisorJump_210_opposite_signs.2]

/-- Complete original residual, not a clipped or independently renormalized model. -/
theorem nyman_flat_210_step_profile (N H : Nat) (h : Nat -> Real)
    (hlo : 35 <= H) (hhi : H <= 42) (hN : 210 <= N)
    (hlow : ∀ k, k ∈ Icc 2 210 -> h k = 0)
    (hmoment : nymanCorrectionMoment N h = nymanFlatMoment N H) :
    nymanFlatScale N H *
        (nymanResidual N (nymanFlatCoefficient N H h) 210 -
          nymanResidual N (nymanFlatCoefficient N H h) 209) =
      Real.log ((H : Real) ^ 2 / 1470) := by
  have ht := nyman_flat_step_before_corrections N H 210 h
    (by omega) (by omega) (by norm_num) hN hlow
  rw [hmoment, sub_self, zero_add,
    <- nymanHighDivisorJump_radical H 210 (by norm_num),
    nymanHighDivisorJump_210_profile H hlo hhi] at ht
  exact ht

theorem nyman_flat_210_opposite_steps (h38 h39 : Nat -> Real)
    (hlow38 : ∀ k, k ∈ Icc 2 210 -> h38 k = 0)
    (hlow39 : ∀ k, k ∈ Icc 2 210 -> h39 k = 0)
    (hm38 : nymanCorrectionMoment 1446 h38 = nymanFlatMoment 1446 38)
    (hm39 : nymanCorrectionMoment 1524 h39 = nymanFlatMoment 1524 39) :
    nymanResidual 1446 (nymanFlatCoefficient 1446 38 h38) 210 <
        nymanResidual 1446 (nymanFlatCoefficient 1446 38 h38) 209 ∧
      nymanResidual 1524 (nymanFlatCoefficient 1524 39 h39) 209 <
        nymanResidual 1524 (nymanFlatCoefficient 1524 39 h39) 210 := by
  have h38 := nyman_flat_210_step_profile 1446 38 h38
    (by norm_num) (by norm_num) (by norm_num) hlow38 hm38
  have h39 := nyman_flat_210_step_profile 1524 39 h39
    (by norm_num) (by norm_num) (by norm_num) hlow39 hm39
  rw [<- nymanHighDivisorJump_210_profile 38 (by norm_num) (by norm_num)] at h38
  rw [<- nymanHighDivisorJump_210_profile 39 (by norm_num) (by norm_num)] at h39
  have hL38 := nymanFlatScale_pos 1446 38 (by norm_num) (by norm_num)
  have hL39 := nymanFlatScale_pos 1524 39 (by norm_num) (by norm_num)
  obtain ⟨hj38, hj39⟩ := nymanHighDivisorJump_210_opposite_signs
  constructor
  · by_contra hn
    have hp := mul_nonneg (le_of_lt hL38) (sub_nonneg.mpr (le_of_not_gt hn))
    linarith
  · by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hL39)
      (sub_nonpos.mpr (le_of_not_gt hn))
    linarith

end RHLean.Analysis
