import «research.NYMAN_RIDGE_PROFILES»
open RHLean.Analysis Finset
open scoped BigOperators

example (K : Nat) (hk : 0 < K) : (1:Real)/12 ≤
    (∑ k ∈ Ioc (3*K) (4*K), 1/(k:Real)) - ∑ k ∈ Ioc (5*K) (6*K), 1/(k:Real) :=
  nyman_ridge_gap K hk
example (a b m : Nat) : (∑ k ∈ Ioc a b, nymanResidue k m) =
    m * nymanRidgeS a b - (nymanBandCount a b m : Real) := nyman_ridge_residue_floor a b m
example (K m : Nat) (hm : m ≤ 6*K+1) :
    nymanBandCount (3*K) (4*K) m = min (4*K) m - 3*K ∧
    nymanBandCount (5*K) (6*K) m = min (6*K) m - 5*K := nyman_ridge_first_layer K m hm
example (K : Nat) (hk : 0 < K) : nymanBandCount (3*K) (4*K) (6*K+2) = K+1 ∧
    nymanBandCount (5*K) (6*K) (6*K+2) = K := nyman_ridge_first_double K hk
example (K H : Nat) (hk : 0 < K) (hh : 1 ≤ H) (hn : H < 6*K) :
    (∑ k ∈ Icc 2 (6*K), nymanRidgeCoeff K H k / (k:Real)) = 1 ∧
    (∑ k ∈ Icc 2 (6*K), nymanRidgeCoeff K H k) = 3 := nyman_ridge_moments K H hk hh hn
example (K H m : Nat) (hk : 0 < K) :
    nymanResidual (6*K) (nymanRidgeCoeff K H) m =
      nymanResidual (6*K) (nymanFlatCoefficient (6*K) H (fun _ => 0)) m -
      nymanFlatMoment (6*K) H / nymanFlatScale (6*K) H * nymanRidgeD K m -
      nymanRidgeV K H / K / nymanFlatScale (6*K) H * nymanRidgeP K m :=
  nyman_ridge_residual_profiles K H m hk
example (K m : Nat) (hk : 0 < K) :
    let c := (nymanBandCount (3*K) (4*K) m : Real)
    let e := (nymanBandCount (5*K) (6*K) m : Real)
    nymanRidgeD K m = m - (c-e)/nymanRidgeGap K ∧
    nymanRidgeP K m = (nymanRidgeS (5*K) (6*K)*c - nymanRidgeS (3*K) (4*K)*e)/nymanRidgeGap K :=
  nyman_ridge_floor_profiles K m hk
