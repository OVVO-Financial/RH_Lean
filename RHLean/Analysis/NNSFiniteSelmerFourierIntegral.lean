import Mathlib
import RHLean.Analysis.AlpogeNativeSharpASKBalance
import RHLean.Proof.FinitePartialMoments

/-!
# Native finite cochain kernel: NNS moments and complete character orthogonality

For any finite set of arithmetic cochain variables X, finite abelian group of
constraints Y, and any (in particular linear) constraint operator L : X -> Y:

1. The exact integer kernel count is its finite zero-indicator sum.
2. This is EXACTLY NNS UPM1 - LPM1 at any real target, with target mass.
3. The full native Alpoge additive-character detector recovers the SAME
   zero-indicator from a complete Fourier sum over the constraints.

An actual finite-level Sha group requires the *specific* cochain and local
coboundary operator of the SAME finite Galois quotient and local subgroups.
A paper proof and exact modular arithmetic tests are in
research/ALPOGE_NNS_FINITE_SELMER_COHOMOLOGY_INTEGRAL_20261121.md.

No surrogated Frobenius host is identified with an actual number field here.
No infinite torsion-level comparison or RH-strength estimate is assumed.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- The complete finite cochain constraint indicator. A zero means all
global cocycle and local coboundary relations (encoded by L) hold. -/
def nnsFiniteRelationIndicator {X Y : Type*} [Zero Y] [DecidableEq Y]
    (L : X -> Y) (x : X) : Real :=
  if L x = 0 then 1 else 0

/-- The exact finite solution mass of the FULL relation operator. -/
def nnsFiniteRelationMass {X Y : Type*} [Fintype X] [Zero Y]
    [DecidableEq Y] (L : X -> Y) : Real :=
  ∑ x : X, nnsFiniteRelationIndicator L x

/-- NNS does not discard negative/positive mass when a target is changed.
This is an unconditional exact identity for the SAME finite source. -/
theorem nnsFiniteRelationMass_eq_UPM_sub_LPM_target
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Zero Y] [DecidableEq Y] (L : X -> Y) (tau : Real) :
    nnsFiniteRelationMass L =
      upperPartialMass (Finset.univ : Finset X)
          (fun x => nnsFiniteRelationIndicator L x - tau) -
      lowerPartialMass (Finset.univ : Finset X)
          (fun x => nnsFiniteRelationIndicator L x - tau) +
      (Fintype.card X : Real) * tau := by
  rw [upperPartialMass_sub_lowerPartialMass_eq_finiteSignedSum]
  unfold finiteSignedSum nnsFiniteRelationMass
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The SAME complete native additive-character orthogonality theorem used
for Frobenius/inertia masks detects the zero set of any finite
arithmetic relation operator L, including actual cochain matrices. -/
theorem nnsFiniteRelation_fullCharacterDetector
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [AddCommGroup Y] [Fintype Y] [DecidableEq Y]
    (L : X -> Y) :
    (∑ x : X, ∑ psi : AddChar Y Complex, psi (L x)) =
      (Fintype.card Y : Complex) *
        (∑ x : X, if L x = 0 then (1 : Complex) else 0) := by
  have h (x : X) :
      (∑ psi : AddChar Y Complex, psi (L x)) =
        if L x = 0 then (Fintype.card Y : Complex) else 0 := by
    simpa using alpogeNativeCharacterDetector (L x) (0 : Y)
  calc
    (∑ x : X, ∑ psi : AddChar Y Complex, psi (L x)) =
        ∑ x : X, if L x = 0 then (Fintype.card Y : Complex) else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact h x
    _ = (Fintype.card Y : Complex) *
        (∑ x : X, if L x = 0 then (1 : Complex) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hzero : L x = 0 <;> simp [hzero]

end RHLean.Analysis
