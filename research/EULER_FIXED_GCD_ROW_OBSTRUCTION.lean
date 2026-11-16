import «research.EULER_SELF_DUAL_ENDPOINT_GATE_20261027»

/-!
# A fixed gcd row does not pointwise dominate the original endpoint

Claim 20261116-referee-1203-EST/FR4, independently reconstructed by Lean
Verification. All ordered historical pairs, original Mobius coefficients,
and the natural floor at R^2-1 are retained. The integer implementation has
an explicit transport to the existing complex Euler source.

The witness refutes only a pointwise estimate with no history/return term.
It does not refute the fixed-row all-scale growth equivalence, finite C,
or RH. Every finite certificate below is checked by the Lean kernel.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis

/-- One exact gcd-labelled row, retaining both pair orientations. -/
def eulerFixedGcdRowInt (R g : Nat) : Int :=
  (Icc 1 (R - 1)).sum (fun b => ArithmeticFunction.moebius b *
    (Icc 1 (R - 1)).sum (fun a =>
      if Nat.gcd a b = g then
        ArithmeticFunction.moebius a * (squareRootEndpoint R / (a * b) : Nat)
      else 0))

/-- Integral coordinates for the existing complete Euler bilinear source. -/
def eulerBilinearInt (R : Nat) : Int :=
  (Icc 1 (R - 1)).sum (fun b => ArithmeticFunction.moebius b *
    (Icc 1 (R - 1)).sum (fun a =>
      ArithmeticFunction.moebius a * (squareRootEndpoint R / (a * b) : Nat)))

theorem eulerFixedGcdRowInt_cast (R g : Nat) :
    (eulerFixedGcdRowInt R g : Complex) =
      (Icc 1 (R - 1)).sum (fun b => (ArithmeticFunction.moebius b : Complex) *
        (Icc 1 (R - 1)).sum (fun a =>
          if Nat.gcd a b = g then
            (ArithmeticFunction.moebius a : Complex) * eulerSelfDualFloor R a b
          else 0)) := by
  unfold eulerFixedGcdRowInt eulerSelfDualFloor
  push_cast
  rfl

theorem eulerBilinearInt_cast (R : Nat) :
    (eulerBilinearInt R : Complex) = eulerSelfDualBilinear R := by
  unfold eulerBilinearInt eulerSelfDualBilinear eulerSelfDualFloor
  push_cast
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem eulerFixedGcdRowInt_139_six : eulerFixedGcdRowInt 139 6 = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem eulerBilinearInt_139 : eulerBilinearInt 139 = -49 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem moebius_prefix_138 :
    (Icc 1 138).sum ArithmeticFunction.moebius = (-3 : Int) := by
  decide +kernel

theorem mertensSummatory_19320 : mertensSummatory 19320 = (43 : Complex) := by
  have hm : mertensSummatory 138 = (-3 : Complex) := by
    have h := congrArg (fun z : Int => (z : Complex)) moebius_prefix_138
    push_cast at h
    simpa only [mertensSummatory_eq_sum_Icc] using h
  have hq : eulerSelfDualBilinear 139 = (-49 : Complex) := by
    rw [<- eulerBilinearInt_cast, eulerBilinearInt_139]
    norm_num
  have he := eulerSelfDualBilinear_eq_two_mertens_sub_endpoint 139 (by norm_num)
  have hx : squareRootEndpoint 139 = 19320 := by norm_num [squareRootEndpoint]
  simp only [hq, hx, show (139 : Nat) - 1 = 138 by norm_num, hm] at he
  linear_combination he

/-- The original endpoint is nonzero while the specified, nonempty row vanishes. -/
theorem eulerFixedGcdRow_six_witness :
    7 <= (139 : Nat) ∧ eulerFixedGcdRowInt 139 6 = 0 ∧
      mertensSummatory (squareRootEndpoint 139) = (43 : Complex) := by
  refine ⟨by norm_num, eulerFixedGcdRowInt_139_six, ?_⟩
  simpa only [show squareRootEndpoint 139 = 19320 by norm_num [squareRootEndpoint]]
    using mertensSummatory_19320

/-- No real constant gives pointwise domination without a restored return.
This is not an assertion about eventual or all-scale growth estimates. -/
theorem not_pointwise_mertens_le_fixedGcdRow_six :
    ¬ ∃ C : Real, ∀ R : Nat, 7 <= R ->
      ‖mertensSummatory (squareRootEndpoint R)‖ <=
        C * ‖(eulerFixedGcdRowInt R 6 : Complex)‖ := by
  rintro ⟨C, h⟩
  have hh := h 139 (by norm_num)
  rw [eulerFixedGcdRow_six_witness.2.1, eulerFixedGcdRow_six_witness.2.2] at hh
  norm_num at hh

/-- Centering at the original unit anchor does not remove the obstruction. -/
theorem not_pointwise_centered_mertens_le_fixedGcdRow_six :
    ¬ ∃ C : Real, ∀ R : Nat, 7 <= R ->
      ‖mertensSummatory (squareRootEndpoint R) - 1‖ <=
        C * ‖(eulerFixedGcdRowInt R 6 : Complex)‖ := by
  rintro ⟨C, h⟩
  have hh := h 139 (by norm_num)
  rw [eulerFixedGcdRow_six_witness.2.1, eulerFixedGcdRow_six_witness.2.2] at hh
  norm_num at hh

end RHLean.Proof
