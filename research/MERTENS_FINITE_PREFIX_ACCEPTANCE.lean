import «research.MERTENS_FINITE_PREFIX_EXTENSION»

/-! Exact signatures of the finite-prefix lift and interval guard.
No uniform envelope-preservation hypothesis is supplied or claimed. -/

open RHLean.Analysis RHLean.Analysis.MertensFiniteExtension

example (a : ArithmeticFunction Int) :
    inverseDefect (newtonLift a) = inverseDefect a * inverseDefect a :=
  inverseDefect_newtonLift a

example (n : Nat) (hn : n < 1002001) :
    newtonLift (mobiusPrefix 1000) n = ArithmeticFunction.moebius n :=
  newtonLift_prefix_exact hn

example (j : Nat) :
    AgreeBelow (2 ^ (2 ^ j)) (newtonIterates j) ArithmeticFunction.moebius := by
  rw [<- precisionCutoff_eq_pow]
  exact newtonIterates_agree j

example {B L U : Nat} {a : ArithmeticFunction Int}
    {C sigma : Real} (ha : AgreeBelow B a ArithmeticFunction.moebius)
    (hL : L < B * B) (hC : 0 <= C) (hsigma : 0 <= sigma)
    (hbudget : norm (liftSummatory a L) + ((U - L : Nat) : Real) <=
      C * (L : Real) ^ sigma) :
    forall x : Nat, L <= x -> x <= U ->
      norm (mertensSummatory x) <= C * (x : Real) ^ sigma :=
  guarded_interval_extension ha hL hC hsigma hbudget

example {N p : Nat} (hN : 1 <= N) (hp : p.Prime) (hNp : N < p) :
    inverseDefect (mobiusPrefix N) p = -1 :=
  inverseDefect_prefix_prime hN hp hNp

#print axioms RHLean.Analysis.MertensFiniteExtension.inverseDefect_newtonLift
#print axioms RHLean.Analysis.MertensFiniteExtension.newtonLift_eq_moebius_sub_tail
#print axioms RHLean.Analysis.MertensFiniteExtension.mul_zero_below
#print axioms RHLean.Analysis.MertensFiniteExtension.newtonLift_agrees_below_square
#print axioms RHLean.Analysis.MertensFiniteExtension.newtonLift_abs_le_one
#print axioms RHLean.Analysis.MertensFiniteExtension.mobiusPrefix_agrees
#print axioms RHLean.Analysis.MertensFiniteExtension.newtonLift_prefix_exact
#print axioms RHLean.Analysis.MertensFiniteExtension.precisionCutoff_eq_pow
#print axioms RHLean.Analysis.MertensFiniteExtension.newtonIterates_agree
#print axioms RHLean.Analysis.MertensFiniteExtension.precisionCutoff_ge
#print axioms RHLean.Analysis.MertensFiniteExtension.newtonIterates_coefficient
#print axioms RHLean.Analysis.MertensFiniteExtension.liftSummatory_eq_mertens
#print axioms RHLean.Analysis.MertensFiniteExtension.guarded_interval_extension
#print axioms RHLean.Analysis.MertensFiniteExtension.inverseDefect_prefix_prime
