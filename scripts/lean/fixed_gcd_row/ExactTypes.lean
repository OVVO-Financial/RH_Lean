import «research.EULER_FIXED_GCD_ROW_OBSTRUCTION»

set_option autoImplicit false
open RHLean.Proof RHLean.Analysis

example : eulerFixedGcdRowInt 139 6 = 0 := eulerFixedGcdRowInt_139_six
example : eulerBilinearInt 139 = -49 := eulerBilinearInt_139
example : mertensSummatory 19320 = (43 : Complex) := mertensSummatory_19320
example : ¬ ∃ C : Real, ∀ R : Nat, 7 <= R ->
    ‖mertensSummatory (squareRootEndpoint R)‖ <=
      C * ‖(eulerFixedGcdRowInt R 6 : Complex)‖ :=
  not_pointwise_mertens_le_fixedGcdRow_six

example : ¬ ∃ C : Real, ∀ R : Nat, 7 <= R ->
    ‖mertensSummatory (squareRootEndpoint R) - 1‖ <=
      C * ‖(eulerFixedGcdRowInt R 6 : Complex)‖ :=
  not_pointwise_centered_mertens_le_fixedGcdRow_six

#check eulerFixedGcdRowInt_cast
#check eulerBilinearInt_cast
#print not_pointwise_mertens_le_fixedGcdRow_six
#print not_pointwise_centered_mertens_le_fixedGcdRow_six
