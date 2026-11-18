import «research.NYMAN_THREE_PROFILE_COERCIVITY»

set_option autoImplicit false
open Finset RHLean.Analysis
open scoped BigOperators

example (K m : Nat) (hK : 1 <= K) (alpha v : Real) :
    nymanCorrectionFloor (12 * K)
      (fun k => if k ∈ Ioc (6 * K) (8 * K) then alpha
        else if k ∈ Ioc (10 * K) (12 * K) then v - alpha else 0) m =
      alpha * nymanTwoBandProfile K m +
        v * (nymanBandCount (10 * K) (12 * K) m : Real) :=
  nyman_two_band_profile_source K m hK alpha v

example (K : Nat) (hK : 1 <= K) (t0 t1 t2 : Real) :
    (K : Real) / 956592 * (t0^2 + t1^2 + t2^2) <=
      nymanWindowEnergy (nymanThreeProfileWindows K) (nymanThreeProfile K t0 t1 t2) :=
  nyman_three_profile_coercivity K hK t0 t1 t2

example (K : Nat) (hK : 1 <= K) (t0 t1 t2 : Real) (r : Nat -> Real) :
    (K : Real) / 1913184 * (t0^2 + t1^2 + t2^2) -
        nymanWindowEnergy (nymanThreeProfileWindows K) r <=
      nymanWindowEnergy (nymanThreeProfileWindows K)
        (fun m => nymanThreeProfile K t0 t1 t2 m + r m) :=
  nyman_three_profile_restored_lower K hK t0 t1 t2 r

-- The accepted paper constant follows for the same complete profiles.
example (K : Nat) (hK : 1 <= K) (t0 t1 t2 : Real) :
    (12 * K : Real) / 49647168 * (t0^2 + t1^2 + t2^2) <=
      nymanWindowEnergy (nymanThreeProfileWindows K) (nymanThreeProfile K t0 t1 t2) := by
  have h := nyman_three_profile_coercivity K hK t0 t1 t2
  have hp : 0 <= (K : Real) * (t0^2 + t1^2 + t2^2) := by positivity
  nlinarith

#print nyman_two_band_profile_source
#print nyman_three_profile_coercivity
#print nyman_three_profile_restored_lower
