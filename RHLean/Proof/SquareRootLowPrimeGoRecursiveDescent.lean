import Mathlib
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence
import RHLean.Proof.SquareRootLowPrimeGoWallStripTelescope

/-!
# Recursive Go descent through the unique smaller prime owner

The square-dilated Go residual is a frozen predecessor cube.  When its cutoff
has not yet fallen below the owner prime `q`, split at the completed lower
prefix `q - 1`.  The remaining rough/smooth window is exactly the difference
of two fresh-prime upper-column telescopes.

Algebraically this gives

`F_{q^-}(y) = M(q-1) - sum_{r<q prime} (F_{r^-}(y/r) - F_{r^-}((q-1)/r))`.

The prime coordinate in every summand is strictly smaller than `q`; the
underlying recurrence is the same fresh-prime Euler recurrence already used by
the wall telescope.  No norm, PNT input, or asymptotic estimate is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- At its own predecessor cutoff, the frozen prime universe is already the
complete ordinary Mertens prefix. -/
theorem frozenPrimeUniverseMass_pred_eq_mertensSummatoryInt
    {q : ℕ} (hq : q.Prime) :
    frozenPrimeUniverseMass (primesUpTo (q - 1)) (q - 1) =
      mertensSummatoryInt (q - 1) := by
  unfold frozenPrimeUniverseMass mertensSummatoryInt
  exact truncatedPrimeCube_eq_moebiusPrefix (q - 1)

/-- **Recursive Go law.**  An unfinished frozen predecessor state at owner `q`
is the completed lower-scale Mertens state through `q-1` minus disjoint
smaller-prime boundary strips.  Each strip is itself the difference between two
frozen predecessor states belonging to a prime `r < q`.

This is the signed recursion to use before taking any norm. -/
theorem frozenPrimeUniverseMass_eq_mertensPred_sub_smallerOwnerStrips
    {q y : ℕ} (hq : q.Prime) (hqy : q ≤ y) :
    frozenPrimeUniverseMass (primesUpTo (q - 1)) y =
      mertensSummatoryInt (q - 1) -
        ∑ r ∈ primesUpTo (q - 1),
          (frozenPrimeUniverseMass (primesUpTo (r - 1)) (y / r) -
            frozenPrimeUniverseMass (primesUpTo (r - 1)) ((q - 1) / r)) := by
  have hy := frozenPrimeUniverse_upperColumn_telescope y (q - 1) (by omega)
  have hpred :=
    frozenPrimeUniverse_upperColumn_telescope (q - 1) (q - 1) (by omega)
  rw [frozenPrimeUniverseMass_pred_eq_mertensSummatoryInt hq] at hpred
  rw [Finset.sum_sub_distrib, hy, hpred]
  ring

/-- Every recursive Go owner in the preceding law is strictly smaller than the
current owner. -/
theorem mem_primesUpTo_pred_lt_owner
    {q r : ℕ} (hr : r ∈ primesUpTo (q - 1)) :
    r < q := by
  have hrq := (mem_primesUpTo.mp hr).2
  omega

/-- Square-residual specialization of the recursive Go law.  In the unfinished
region `q <= floor(X/q^2)`, the residual is a completed `M(q-1)` state plus only
strictly descending owner strips. -/
theorem squareRootLowPrimeGoWallSquareResidual_eq_mertensPred_sub_smallerOwnerStrips
    {q X : ℕ} (hq : q.Prime)
    (hunfinished : q ≤ X / (q * q)) :
    squareRootLowPrimeGoWallSquareResidual q X =
      mertensSummatoryInt (q - 1) -
        ∑ r ∈ primesUpTo (q - 1),
          (frozenPrimeUniverseMass (primesUpTo (r - 1))
              ((X / (q * q)) / r) -
            frozenPrimeUniverseMass (primesUpTo (r - 1)) ((q - 1) / r)) := by
  rw [squareRootLowPrimeGoWallSquareResidual_eq_squareCutoff]
  exact frozenPrimeUniverseMass_eq_mertensPred_sub_smallerOwnerStrips
    hq hunfinished

end RHLean.Proof
