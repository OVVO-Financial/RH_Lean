import Mathlib
import «research.STABLE_FAR_RECIPROCAL_OWNER_FUBINI»
import «research.STABLE_FAR_RETURNED_FIBER_PRODUCTION»

/-!
# Reciprocal returned-fibre frozen-window normal form

PR #718 performs the reciprocal finite Fubini on the literal stable-far
occurrence carrier.  This file rewrites the same reciprocal weighting in the
older returned-coordinate frozen-window language.

At fixed returned owner `r` and far prime `p`, the q^2 descended baseline is
weighted by `1/r`, while every old crossing owner `q` is weighted by `1/q`.
Thus the exact returned-coordinate packet is

  (1/r) F_{r^-}(X/(r^2 p))
    - sum_q (1/q)
        [F_{r^-}(X/(q r p)) - F_{r^-}(X/(q^2 r p))].

No norm, endpoint factorization, PNT input, or estimate is used.  This is the
finite-difference coordinate in which the AMP normalization correction can be
compared to the reciprocal owner graph only after the signed reassembly has
been completed.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Reciprocal old-owner crossing column at fixed returned coordinates `(r,p)`. -/
def stableFarReturnedReciprocalCrossingColumn
    (R r p : ℕ) : ℂ :=
  ∑ q ∈ stableFarReturnedOldOwners R r p,
    ((1 : ℂ) / (q : ℂ)) *
      (((∑ e ∈ stableFarReturnedCrossingCofactors R r p q, μ e) : ℤ) : ℂ)

/-- Reciprocal q^2 descended baseline at fixed returned coordinates `(r,p)`. -/
def stableFarReturnedReciprocalDescendedMass
    (R r p : ℕ) : ℂ :=
  ((1 : ℂ) / (r : ℂ)) *
    ((stableFarReturnedDescendedMass R r p : ℤ) : ℂ)

/-- Baseline minus all reciprocal old-owner returns. -/
def stableFarReturnedReciprocalCenteredMass
    (R r p : ℕ) : ℂ :=
  stableFarReturnedReciprocalDescendedMass R r p -
    stableFarReturnedReciprocalCrossingColumn R r p

/-- One reciprocal old-owner fibre is the corresponding reciprocal-weighted
frozen-window finite difference. -/
theorem stableFarReturnedReciprocalCrossingColumn_eq_frozenWindows
    {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedReciprocalCrossingColumn R r p =
      ∑ q ∈ stableFarReturnedOldOwners R r p,
        ((1 : ℂ) / (q : ℂ)) *
          (((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * r * p)) : ℤ) : ℂ) -
            ((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * q * r * p)) : ℤ) : ℂ)) := by
  unfold stableFarReturnedReciprocalCrossingColumn
  apply Finset.sum_congr rfl
  intro q hq
  have hqPrime : q.Prime := (mem_frozenPrimeUniverseHighPrimeSet.mp hq).1
  rw [stableFarReturnedCrossingCofactors_mass_eq_frozenWindow hr hp hqPrime]
  push_cast

/-- The reciprocal descended baseline is the reciprocal-weighted predecessor
prefix. -/
theorem stableFarReturnedReciprocalDescendedMass_eq_frozenPrefix
    {R r p : ℕ} (hr : r.Prime) :
    stableFarReturnedReciprocalDescendedMass R r p =
      ((1 : ℂ) / (r : ℂ)) *
        ((frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootEndpoint R / (r * r * p)) : ℤ) : ℂ) := by
  unfold stableFarReturnedReciprocalDescendedMass
  rw [stableFarReturnedDescendedMass_eq_frozenPrefix hr]

/-- **Reciprocal returned-fibre normal form.**  After signed finite Fubini, the
normalization correction is one reciprocal baseline minus reciprocal-weighted
complete frozen-window differences. -/
theorem stableFarReturnedReciprocalCenteredMass_eq_frozenPrefix_sub_windows
    {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedReciprocalCenteredMass R r p =
      ((1 : ℂ) / (r : ℂ)) *
        ((frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootEndpoint R / (r * r * p)) : ℤ) : ℂ) -
      ∑ q ∈ stableFarReturnedOldOwners R r p,
        ((1 : ℂ) / (q : ℂ)) *
          (((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * r * p)) : ℤ) : ℂ) -
            ((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * q * r * p)) : ℤ) : ℂ)) := by
  unfold stableFarReturnedReciprocalCenteredMass
  rw [stableFarReturnedReciprocalDescendedMass_eq_frozenPrefix hr,
    stableFarReturnedReciprocalCrossingColumn_eq_frozenWindows hr hp]

end RHLean.Proof
