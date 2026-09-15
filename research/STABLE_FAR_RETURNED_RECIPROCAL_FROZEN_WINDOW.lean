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

The final section keeps an arbitrary owner weight `w`.  Unit weight is the raw
physical centered packet, reciprocal weight is the Perron-normalized packet,
and their exact difference is the `(1-1/q)` normalization memory on the same
frozen windows.  No norm is taken in passing between these coordinates.

No endpoint factorization, PNT input, or estimate is used.
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
  rfl

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

/-! ## One exact owner-weight interpolation contains both endpoints -/

/-- Returned packet with an arbitrary scalar weight on the owner coordinate. -/
def stableFarReturnedOwnerWeightedCenteredMass
    (w : ℕ → ℂ) (R r p : ℕ) : ℂ :=
  w r * ((stableFarReturnedDescendedMass R r p : ℤ) : ℂ) -
    ∑ q ∈ stableFarReturnedOldOwners R r p,
      w q * (((∑ e ∈ stableFarReturnedCrossingCofactors R r p q, μ e) : ℤ) : ℂ)

/-- Generic owner-weighted frozen-window form.  This is finite signed Fubini
with the owner weight left symbolic. -/
theorem stableFarReturnedOwnerWeightedCenteredMass_eq_frozenPrefix_sub_windows
    (w : ℕ → ℂ) {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedOwnerWeightedCenteredMass w R r p =
      w r *
        ((frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootEndpoint R / (r * r * p)) : ℤ) : ℂ) -
      ∑ q ∈ stableFarReturnedOldOwners R r p,
        w q *
          (((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * r * p)) : ℤ) : ℂ) -
            ((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * q * r * p)) : ℤ) : ℂ)) := by
  unfold stableFarReturnedOwnerWeightedCenteredMass
  rw [stableFarReturnedDescendedMass_eq_frozenPrefix hr]
  apply congrArg₂ (· - ·) rfl
  apply Finset.sum_congr rfl
  intro q hq
  have hqPrime : q.Prime := (mem_frozenPrimeUniverseHighPrimeSet.mp hq).1
  rw [stableFarReturnedCrossingCofactors_mass_eq_frozenWindow hr hp hqPrime]
  push_cast
  rfl

/-- Reciprocal weight is exactly the specialized reciprocal packet above. -/
theorem stableFarReturnedOwnerWeightedCenteredMass_reciprocal
    (R r p : ℕ) :
    stableFarReturnedOwnerWeightedCenteredMass
        (fun q => (1 : ℂ) / (q : ℂ)) R r p =
      stableFarReturnedReciprocalCenteredMass R r p := by
  rfl

/-- Unit owner weight recovers the original unweighted returned centered mass. -/
theorem stableFarReturnedOwnerWeightedCenteredMass_one
    {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedOwnerWeightedCenteredMass (fun _ => (1 : ℂ)) R r p =
      ((stableFarReturnedCenteredMass R r p : ℤ) : ℂ) := by
  rw [stableFarReturnedOwnerWeightedCenteredMass_eq_frozenPrefix_sub_windows
      (fun _ => (1 : ℂ)) hr hp,
    stableFarReturnedCenteredMass_eq_frozenPrefix_sub_windows hr hp]
  push_cast
  simp

/-- **Exact normalization-memory identity.**  Passing from raw unit owner weight
to reciprocal owner weight leaves precisely the `(1-1/owner)` weighted frozen
baseline/windows.  This is the returned-fibre form of the correction exposed by
the physical AMP transport, still before any norm. -/
theorem stableFarReturned_unit_sub_reciprocal_eq_eulerMemoryWindows
    {R r p : ℕ} (hr : r.Prime) (hp : p.Prime) :
    stableFarReturnedOwnerWeightedCenteredMass (fun _ => (1 : ℂ)) R r p -
        stableFarReturnedReciprocalCenteredMass R r p =
      (1 - (1 : ℂ) / (r : ℂ)) *
        ((frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootEndpoint R / (r * r * p)) : ℤ) : ℂ) -
      ∑ q ∈ stableFarReturnedOldOwners R r p,
        (1 - (1 : ℂ) / (q : ℂ)) *
          (((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * r * p)) : ℤ) : ℂ) -
            ((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * q * r * p)) : ℤ) : ℂ)) := by
  rw [stableFarReturnedOwnerWeightedCenteredMass_eq_frozenPrefix_sub_windows
      (fun _ => (1 : ℂ)) hr hp,
    stableFarReturnedReciprocalCenteredMass_eq_frozenPrefix_sub_windows hr hp]
  have hsum :
      (∑ q ∈ stableFarReturnedOldOwners R r p,
          (((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * r * p)) : ℤ) : ℂ) -
            ((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * q * r * p)) : ℤ) : ℂ))) -
        (∑ q ∈ stableFarReturnedOldOwners R r p,
          ((1 : ℂ) / (q : ℂ)) *
            (((frozenPrimeUniverseMass (primesUpTo (r - 1))
                  (squareRootEndpoint R / (q * r * p)) : ℤ) : ℂ) -
              ((frozenPrimeUniverseMass (primesUpTo (r - 1))
                  (squareRootEndpoint R / (q * q * r * p)) : ℤ) : ℂ))) =
      ∑ q ∈ stableFarReturnedOldOwners R r p,
        (1 - (1 : ℂ) / (q : ℂ)) *
          (((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * r * p)) : ℤ) : ℂ) -
            ((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * q * r * p)) : ℤ) : ℂ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    ring
  simp only [one_mul]
  rw [← hsum]
  ring

end RHLean.Proof
