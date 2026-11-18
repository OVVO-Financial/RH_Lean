import «research.NYMAN_ALL_PROFILE_COERCIVITY»

open Finset RHLean.Analysis
open scoped BigOperators

#print nyman_dual_profile_leakage
#print nyman_all_profile_coercivity
#print nyman_all_profile_restored_lower

example (K m : Nat) (hK : 1 <= K) :
    |nymanDualPair (nymanDualProfile K) m| <= 3 * K :=
  nyman_dual_profile_leakage K m hK

example (K n : Nat) (hK : 40 <= K) (t : Nat -> Real) :
    (21 / 10240000 : Real) * K * (∑ i ∈ range n, t i^2) <=
      nymanDualEnergy (nymanDualWindows K n) (nymanDualSum K n t) :=
  nyman_all_profile_coercivity K n hK t

example (K n : Nat) (hK : 40 <= K) (t r : Nat -> Real) :
    (21 / 20480000 : Real) * K * (∑ i ∈ range n, t i^2) -
        nymanDualEnergy (nymanDualWindows K n) r <=
      nymanDualEnergy (nymanDualWindows K n) (fun m => nymanDualSum K n t m + r m) :=
  nyman_all_profile_restored_lower K n hK t r

-- The original independently accepted DUAL1 constant is a checked corollary.
example (K n : Nat) (hK : 40 <= K) (t : Nat -> Real) :
    (121 / 808704000 : Real) * (12 * K) * (∑ i ∈ range n, t i^2) <=
      nymanDualEnergy (nymanDualWindows K n) (nymanDualSum K n t) := by
  have hp := nyman_all_profile_coercivity K n hK t
  have hs : 0 <= (K : Real) * (∑ i ∈ range n, t i^2) := by positivity
  nlinarith

-- The profile is literally the existing correction-floor source.
example (K m : Nat) : nymanDualProfile K m =
    nymanCorrectionFloor (12 * K)
      (fun k => if k ∈ Ioc (6 * K) (8 * K) then 1
        else if k ∈ Ioc (10 * K) (12 * K) then -1 else 0) m := rfl
