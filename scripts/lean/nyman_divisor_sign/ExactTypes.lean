import «research.NYMAN_DIVISOR_JUMP_SIGN_OBSTRUCTION»

set_option autoImplicit false
open Finset RHLean.Analysis

example (H : Nat) (hlo : 35 <= H) (hhi : H <= 42) :
    nymanHighDivisorJump H 210 = Real.log ((H : Real) ^ 2 / 1470) :=
  nymanHighDivisorJump_210_profile H hlo hhi

example : nymanHighDivisorJump 38 210 < 0 ∧ 0 < nymanHighDivisorJump 39 210 :=
  nymanHighDivisorJump_210_opposite_signs

example : ¬ (∀ H m : Nat, 2 <= H -> Squarefree m ->
    8 * H < 6 * ((H ^ 2 + 5) / 6) ->
    4 * H <= m -> m <= (6 * ((H ^ 2 + 5) / 6)) / 2 ->
    0 <= (ArithmeticFunction.moebius m : Real) * nymanHighDivisorJump H m) :=
  not_nyman_long_middle_parity_nonnegative

example : 0 < nymanLogTail 38 210 - nymanLogTail 38 209 ∧
    nymanLogTail 39 210 - nymanLogTail 39 209 < 0 :=
  nymanLogTail_210_opposite_steps

example (N H : Nat) (h : Nat -> Real)
    (hlo : 35 <= H) (hhi : H <= 42) (hN : 210 <= N)
    (hlow : ∀ k, k ∈ Icc 2 210 -> h k = 0)
    (hmoment : nymanCorrectionMoment N h = nymanFlatMoment N H) :
    nymanFlatScale N H *
        (nymanResidual N (nymanFlatCoefficient N H h) 210 -
          nymanResidual N (nymanFlatCoefficient N H h) 209) =
      Real.log ((H : Real) ^ 2 / 1470) :=
  nyman_flat_210_step_profile N H h hlo hhi hN hlow hmoment

example (h38 h39 : Nat -> Real)
    (hlow38 : ∀ k, k ∈ Icc 2 210 -> h38 k = 0)
    (hlow39 : ∀ k, k ∈ Icc 2 210 -> h39 k = 0)
    (hm38 : nymanCorrectionMoment 1446 h38 = nymanFlatMoment 1446 38)
    (hm39 : nymanCorrectionMoment 1524 h39 = nymanFlatMoment 1524 39) :
    nymanResidual 1446 (nymanFlatCoefficient 1446 38 h38) 210 <
        nymanResidual 1446 (nymanFlatCoefficient 1446 38 h38) 209 ∧
      nymanResidual 1524 (nymanFlatCoefficient 1524 39 h39) 209 <
        nymanResidual 1524 (nymanFlatCoefficient 1524 39 h39) 210 :=
  nyman_flat_210_opposite_steps h38 h39 hlow38 hlow39 hm38 hm39

#print nymanHighDivisorJump_210_profile
#print nymanHighDivisorJump_210_opposite_signs
#print nyman_210_long_middle_witness
#print not_nyman_long_middle_parity_nonnegative
#print nymanLogTail_210_opposite_steps
#print nyman_flat_210_step_profile
#print nyman_flat_210_opposite_steps
