import «research.NYMAN_VARIANCE_REPAIR»

open Finset RHLean.Analysis
open scoped BigOperators

#print nyman_jordan_two_divisor_sum
#print nyman_jordan_two_lower
#print nyman_covariance_divisor_squares
#print nyman_covariance_singleton_lower
#print nyman_flat_same_support_repair

example (n : Nat) :
    ∑ d ∈ n.divisors, nymanJordanTwo d = (n : Real)^2 :=
  nyman_jordan_two_divisor_sum n

example (n : Nat) : (n : Real)^2/2 <= nymanJordanTwo n :=
  nyman_jordan_two_lower n

example (N : Nat) (a : Nat -> Real) :
    12 * nymanCovariance N a =
      ∑ d ∈ Icc 2 N, nymanJordanTwo d *
        (∑ k ∈ Icc 2 N, if d ∣ k then a k/k else 0)^2 :=
  nyman_covariance_divisor_squares N a

example (N : Nat) (a : Nat -> Real) (s : Finset Nat)
    (hs : s ⊆ Icc 2 N) (htop : ∀ q ∈ s, N < 2*q) :
    ∑ q ∈ s, (a q)^2 <= 24 * nymanCovariance N a :=
  nyman_covariance_singleton_lower N a s hs htop

example (K H : Nat) (hK : 1 <= K) (hH : 1 <= H) (hHK : H <= 4*K)
    (A Z : Real) (e : Nat -> Real) :
    (∑ q ∈ Ioc (4*K) (5*K),
      (e q - (ArithmeticFunction.moebius q : Real) *
        Real.log ((6*K : Nat) / (q : Real)) / nymanFlatScale (6*K) H)^2) <=
      24 * nymanCovariance (6*K) (fun k =>
        nymanFlatCoefficient (6*K) H
          (fun j => if j ∈ Ioc (3*K) (4*K) then A
            else if j ∈ Ioc (5*K) (6*K) then Z else 0) k + e k) :=
  nyman_flat_same_support_repair K H hK hH hHK A Z e

-- This source bridge is checked, not assumed as a quadratic-bound hypothesis.
example (N : Nat) (a : Nat -> Real) : nymanCovariance N a =
    (1/12 : Real) * ∑ k ∈ Icc 2 N, ∑ l ∈ Icc 2 N,
      (a k/k)*(a l/l)*((Nat.gcd k l : Real)^2-1) := rfl
