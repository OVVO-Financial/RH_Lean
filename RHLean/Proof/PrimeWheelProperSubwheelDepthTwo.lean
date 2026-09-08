import RHLean.Proof.PrimeWheelFrozenRoughSeatBridge
import RHLean.Arithmetic.LeastPrimeDepthHierarchy
import RHLean.Arithmetic.TruncatedCubeMertensPrefix
import RHLean.Proof.LowWheelCanonicalSqrtDenseContraction
import RHLean.Proof.SquareRootLowPrimeGoHyperbolicStripRecursion
import RHLean.Proof.SquareRootLowPrimeGoWallQuantitative

/-!
# Cubic proper-subwheel decomposition

Stop the prime wheel at `Y`, before the physical endpoint `X` has been fully
resolved.  The frozen rough-seat identity says this is still exactly `M(X)`.
This file then changes chronology without taking a norm.

The existing high-prime upper-column telescope gives

`M(X) = F_Y(X) - sum_{Y < p <= X} F_{p^-}(X/p)`.

If `X < (Y+1)^3`, every owner `p > Y` satisfies `X < p^3`.  Opening that
moving predecessor column at its own fresh prime therefore leaves a square
residual at `X/p^2` which is already below `p`, hence is an *ordinary lower
Mertens state*.  Thus

`M(X) = F_Y(X)
        - sum_{Y < p <= X} F_p(X/p)
        - sum_{Y < p <= X} M(X/p^2)`.

This is the exact algebraic form of the prime/semiprime cancellation visible in
the proper-subwheel rough-seat coordinate.  The second sum is the unresolved
moving boundary ledger; the third sum has already lost two owner factors in
scale.  No triangle inequality, density estimate, PNT input, or Mertens bound
is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- At its own full prime cutoff the frozen cube is exactly ordinary integer
Mertens. -/
theorem frozenPrimeUniverseMass_primesUpTo_self_eq_mertensSummatoryInt
    (X : ℕ) :
    frozenPrimeUniverseMass (primesUpTo X) X = mertensSummatoryInt X := by
  unfold frozenPrimeUniverseMass mertensSummatoryInt
  exact truncatedPrimeCube_eq_moebiusPrefix X

/-- **Proper-subwheel high-owner column.**  Advancing the frozen prime universe
from `Y` all the way through `X` recovers ordinary Mertens.  This is the
chronological reading of the same signed object represented by the rough-seat
correlation. -/
theorem mertensSummatoryInt_eq_properSubwheel_sub_highOwnerColumn
    (X Y : ℕ) (hYX : Y ≤ X) :
    mertensSummatoryInt X =
      frozenPrimeUniverseMass (primesUpTo Y) X -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p) := by
  have htel := frozenPrimeUniverse_highUpperColumn_telescope X Y X hYX
  rw [frozenPrimeUniverseMass_primesUpTo_self_eq_mertensSummatoryInt] at htel
  omega

/-- The proper-subwheel rough-seat correlation and the chronological high-owner
column are literally the same Mertens value. -/
theorem primeWheelFrozenFullRoughSeatCorrelation_eq_base_sub_highOwnerColumn
    (X Y : ℕ) (hYX : Y ≤ X) :
    primeWheelFrozenFullRoughSeatCorrelation (primesUpTo Y) X =
      frozenPrimeUniverseMass (primesUpTo Y) X -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p) := by
  rw [← mertensSummatoryInt_eq_properSubwheel_sub_highOwnerColumn X Y hYX]
  rw [← roughMertens_one_eq_primeWheel_frozenFullRoughSeatCorrelation
    (primesUpTo Y) (fun p hp => prime_of_mem_primesUpTo hp) X]
  unfold roughMertens mertensSummatoryInt
  simp [roughMoebius]

/-- Above a cubic proper-subwheel cutoff, every chronological owner is itself
past the cubic completion threshold. -/
theorem properSubwheelHighPrime_owner_cube_gt
    {X Y p : ℕ}
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet Y X)
    (hcubic : X < (Y + 1) ^ 3) :
    X < p ^ 3 := by
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
  have hYp : Y < p := hpData.2.1
  have hsucc : Y + 1 ≤ p := by omega
  have hpow : (Y + 1) ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hsucc 3
  exact hcubic.trans_le hpow

/-- **One high owner opens into a boundary state plus a completed square
residual.**  The latter is already ordinary Mertens because `X/p^2 < p` under
the cubic proper-subwheel hypothesis. -/
theorem properSubwheel_highOwnerMovingTerm_eq_boundary_add_mertensSquare
    {X Y p : ℕ}
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet Y X)
    (hcubic : X < (Y + 1) ^ 3) :
    frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p) =
      frozenPrimeUniverseMass (primesUpTo p) (X / p) +
        mertensSummatoryInt (X / (p * p)) := by
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
  have hpPrime : p.Prime := hpData.1
  have hcube : X < p ^ 3 :=
    properSubwheelHighPrime_owner_cube_gt hp hcubic
  have hcomplete : X / (p * p) < p :=
    squareRootLowPrimeGo_squareCutoff_lt_owner_of_lt_cube hpPrime hcube
  have hstep :=
    frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor
      p (X / p) hpPrime
  unfold predecessorPrimeMass at hstep
  rw [Nat.div_div_eq_div_mul] at hstep
  have hmertens :=
    frozenPrimeUniverseMass_eq_mertensSummatoryInt_of_lt_owner
      hpPrime hcomplete
  rw [hmertens] at hstep
  omega

/-- The entire high-owner moving column splits before any norm into the moving
boundary ledger plus completed lower Mertens square residuals. -/
theorem properSubwheel_highOwnerColumn_eq_boundary_add_mertensSquares
    (X Y : ℕ) (hcubic : X < (Y + 1) ^ 3) :
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) =
      (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        frozenPrimeUniverseMass (primesUpTo p) (X / p)) +
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        mertensSummatoryInt (X / (p * p)) := by
  calc
    (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        frozenPrimeUniverseMass (primesUpTo (p - 1)) (X / p)) =
      ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
        (frozenPrimeUniverseMass (primesUpTo p) (X / p) +
          mertensSummatoryInt (X / (p * p))) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact properSubwheel_highOwnerMovingTerm_eq_boundary_add_mertensSquare
        hp hcubic
    _ = _ := by rw [Finset.sum_add_distrib]

/-- **Cubic proper-subwheel normal form.**  The full outer Mobius cancellation
has been consumed exactly.  What remains is one signed chronological boundary
ledger and a twice-dilated lower Mertens column. -/
theorem mertensSummatoryInt_eq_properSubwheelBoundary_sub_mertensSquares
    (X Y : ℕ) (hYX : Y ≤ X) (hcubic : X < (Y + 1) ^ 3) :
    mertensSummatoryInt X =
      frozenPrimeUniverseMass (primesUpTo Y) X -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          frozenPrimeUniverseMass (primesUpTo p) (X / p)) -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          mertensSummatoryInt (X / (p * p)) := by
  rw [mertensSummatoryInt_eq_properSubwheel_sub_highOwnerColumn X Y hYX,
    properSubwheel_highOwnerColumn_eq_boundary_add_mertensSquares X Y hcubic]
  ring

/-- Same normal form on the literal frozen rough-seat correlation. -/
theorem primeWheelFrozenFullRoughSeatCorrelation_eq_boundary_sub_mertensSquares
    (X Y : ℕ) (hYX : Y ≤ X) (hcubic : X < (Y + 1) ^ 3) :
    primeWheelFrozenFullRoughSeatCorrelation (primesUpTo Y) X =
      frozenPrimeUniverseMass (primesUpTo Y) X -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          frozenPrimeUniverseMass (primesUpTo p) (X / p)) -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y X,
          mertensSummatoryInt (X / (p * p)) := by
  rw [← mertensSummatoryInt_eq_properSubwheelBoundary_sub_mertensSquares
    X Y hYX hcubic]
  rw [← roughMertens_one_eq_primeWheel_frozenFullRoughSeatCorrelation
    (primesUpTo Y) (fun p hp => prime_of_mem_primesUpTo hp) X]
  unfold roughMertens mertensSummatoryInt
  simp [roughMoebius]

/-- Square-endpoint specialization.  The wheel may stop strictly below the
physical root; only the cubic inequality and the harmless range condition are
needed. -/
theorem squareRootProperSubwheelFrozenCorrelation_eq_boundary_sub_mertensSquares
    (R Y : ℕ)
    (hYX : Y ≤ squareRootEndpoint R)
    (hcubic : squareRootEndpoint R < (Y + 1) ^ 3) :
    squareRootProperSubwheelFrozenCorrelation R Y =
      frozenPrimeUniverseMass (primesUpTo Y) (squareRootEndpoint R) -
        (∑ p ∈ frozenPrimeUniverseHighPrimeSet Y (squareRootEndpoint R),
          frozenPrimeUniverseMass (primesUpTo p)
            (squareRootEndpoint R / p)) -
        ∑ p ∈ frozenPrimeUniverseHighPrimeSet Y (squareRootEndpoint R),
          mertensSummatoryInt (squareRootEndpoint R / (p * p)) := by
  unfold squareRootProperSubwheelFrozenCorrelation
  exact primeWheelFrozenFullRoughSeatCorrelation_eq_boundary_sub_mertensSquares
    (squareRootEndpoint R) Y hYX hcubic

end RHLean.Proof
