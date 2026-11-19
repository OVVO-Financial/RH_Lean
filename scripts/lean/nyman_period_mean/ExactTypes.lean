import «research.NYMAN_PERIOD_MEAN»

open Finset RHLean.Analysis
open scoped BigOperators

example (k m : Nat) : nymanCellFluct k m = ((m % k : Nat) : Real) - ((k : Real)-1)/2 := rfl
example (N : Nat) (c : Nat → Real) : nymanPeriodBias N c =
    1 - ∑ k ∈ Icc 2 N, (c k / k)*(((k : Real)-1)/2) := rfl
example (P k : Nat) (hd : k ∣ P) : ∑ m : Fin P, nymanCellFluct k m.val = 0 :=
  nyman_period_cell_sum P k hd
example (P k l : Nat) (hk : 0<k) (hl : 0<l) (h : k ∣ P) (h' : l ∣ P) :
    (∑ m : Fin P, nymanCellFluct k m.val * nymanCellFluct l m.val) =
      (P : Real)*((Nat.gcd k l : Real)^2-1)/12 := nyman_period_cell_pair P k l hk hl h h'
example (N P : Nat) (c : Nat → Real) (h : ∀ k ∈ Icc 2 N, k ∣ P) :
    (∑ m : Fin P, (nymanResidual N c m.val)^2) =
      (P : Real)*((nymanPeriodBias N c)^2 + nymanCovariance N c) := nyman_period_residual_energy N P c h
example (N P : Nat) (hP : 0<P) (c : Nat → Real) (h : ∀ k ∈ Icc 2 N, k ∣ P) :
    (∑ m : Fin P, (nymanResidual N c m.val)^2)/(P : Real) = nymanCovariance N c ↔
      nymanPeriodBias N c = 0 := nyman_period_mean_eq_covariance_iff N P hP c h
