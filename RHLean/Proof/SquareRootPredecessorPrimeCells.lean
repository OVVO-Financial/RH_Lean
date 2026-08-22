import Mathlib
import RHLean.Analysis.SquareRootMiddleSequentialCoherence
import RHLean.Proof.LowWheelSequentialSmoothRoughBoundary

/-!
# Predecessor-prime cells in the square-root reciprocal corridor

The completed one-prime frontier is killed by full divisor-fibre Möbius
inversion.  This module keeps one chronological low-prime coordinate visible.
For a prime `p` and reciprocal label `k`, define

`A_p(k) = F_{<p}(floor(k/p))`,

where `F_{<p}` is the truncated Boolean-cube mass on primes strictly below `p`.
On squarefree support this is exactly the signed mass

`sum_{d <= k/p, P+(d) < p} mu(d)`.

The point is not to claim an estimate.  The exact identities below record two
guardrails for the next finite gate.

* `A_p(k)` is the decrement produced when the frozen lower-scale cube admits
  the fresh prime `p`.
* The cumulative smooth-shell coefficient after processing `p` plus `A_p(k)`
  is just the parent prefix before `p`.  Thus pairing `A_p(k)` against the
  cumulative `p`-window state would merely reconstruct an earlier coordinate;
  a meaningful `(p,k)` cancellation test has to use the additive fresh-prime
  increment instead.
* Once the cutoff `k/p` contains the complete Boolean cube on primes below `p`,
  `A_p(k)` is exactly zero.  This is the primorial deletion mechanism.

No analytic estimate, asymptotic, PNT input, or RH hypothesis is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- Signed predecessor-prime mass at reciprocal label `k`.

This is the frozen old-prime cube strictly before `p`, evaluated at the child
cutoff `floor(k/p)`. -/
def predecessorPrimeMass (p k : ℕ) : ℤ :=
  frozenPrimeUniverseMass (primesUpTo (p - 1)) (k / p)

/-- Literal Boolean-face form of `A_p(k)`. -/
theorem predecessorPrimeMass_eq_faceSum (p k : ℕ) :
    predecessorPrimeMass p k =
      ∑ t ∈ (primesUpTo (p - 1)).powerset,
        if primeFaceProduct t ≤ k / p then booleanCubeSign t else 0 := by
  unfold predecessorPrimeMass
  exact frozenPrimeUniverseMass_eq_cutoffSum _ _

/-- **Fresh-prime decrement.**  Admitting a prime `p` to the frozen lower-scale
cube subtracts exactly `A_p(k)`. -/
theorem frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor
    (p k : ℕ) (hp : p.Prime) :
    frozenPrimeUniverseMass (primesUpTo p) k =
      frozenPrimeUniverseMass (primesUpTo (p - 1)) k -
        predecessorPrimeMass p k := by
  rw [primesUpTo_eq_insert_pred_of_prime hp]
  rw [frozenPrimeUniverseMass_insert
    (freshPrime_not_mem_primesUpTo_pred hp) hp]
  rfl

/-- The sequential smooth-face shell is exactly the frozen lower-scale state
after the fresh prime `p` has been processed. -/
theorem lowWheelSmoothFaceShellMass_eq_frozenPrimeUniverseMass
    (p k : ℕ) (hp : p.Prime) :
    lowWheelSmoothFaceShellMass p k =
      frozenPrimeUniverseMass (primesUpTo p) k := by
  rw [lowWheelSmoothFaceShellMass_eq_truncatedCubeDiff]
  change
    frozenPrimeUniverseMass (primesUpTo (p - 1)) k -
        frozenPrimeUniverseMass (primesUpTo (p - 1)) (k / p) =
      frozenPrimeUniverseMass (primesUpTo p) k
  rw [frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor p k hp]
  rfl

/-- **Cumulative-state guardrail.**  Adding `A_p(k)` back to the already-
processed smooth-shell coefficient reconstructs the old parent prefix exactly.
Therefore this pair is not an independent cancellation mechanism. -/
theorem lowWheelSmoothFaceShellMass_add_predecessor_eq_parentPrefix
    (p k : ℕ) (hp : p.Prime) :
    lowWheelSmoothFaceShellMass p k + predecessorPrimeMass p k =
      frozenPrimeUniverseMass (primesUpTo (p - 1)) k := by
  rw [lowWheelSmoothFaceShellMass_eq_frozenPrimeUniverseMass p k hp]
  have hstep := frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor p k hp
  omega

/-- **Primorial deletion.**  If `k/p` already contains the complete Boolean cube
on all primes below `p`, then `A_p(k)` vanishes exactly. -/
theorem predecessorPrimeMass_eq_zero_of_predPrimeCube_complete
    {p k : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hfit : p * primeFaceProduct (primesUpTo (p - 1)) ≤ k) :
    predecessorPrimeMass p k = 0 := by
  unfold predecessorPrimeMass
  apply frozenPrimeUniverseMass_eq_zero_of_complete_old_cube
  · refine ⟨2, mem_primesUpTo_of_prime_le Nat.prime_two ?_⟩
    omega
  · intro q hq
    exact prime_of_mem_primesUpTo hq
  · apply (Nat.le_div_iff_mul_le hp.pos).2
    simpa [Nat.mul_comm] using hfit

/-- The first predecessor-prime channel at `k=2` has unit mass. -/
theorem predecessorPrimeMass_two_two : predecessorPrimeMass 2 2 = 1 := by
  have hS : primesUpTo (2 - 1) = ∅ := by
    ext q
    simp [primesUpTo]
  unfold predecessorPrimeMass
  rw [hS]
  simp [frozenPrimeUniverseMass, truncatedCubeAlternatingSum,
    primeProductAdmissible, primeFaceProduct, booleanCubeSign]

/-- **Prime edge plus `p=2` cancellation in the `k=2` fibre.** -/
theorem edge_prime_plus_p2_cancel_of_k2 :
    (-1 : ℤ) + predecessorPrimeMass 2 2 = 0 := by
  rw [predecessorPrimeMass_two_two]
  norm_num

/-- The already-formalized exact middle corridor, displayed in reciprocal
coordinates.  The quotient label `k` is the only surviving large-prime label
after primes `q` in the same fibre are counted. -/
theorem squareRootMiddle_exact_reciprocalLayers
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleMertensTail R =
      ∑ k ∈ Finset.Icc 2 (R - 1),
        primeSieveReciprocalPrimeCount R (squareRootEndpoint R) k *
          mertensSummatory k :=
  squareRootMiddleMertensTail_eq_reciprocalPrimeLayers R hR

/-- The `k=2` reciprocal band is identically zero, not merely small. -/
theorem squareRootMiddle_k2_band_exact_zero (R : ℕ) :
    (∑ q ∈ Finset.Ioc (squareRootEndpoint R / 3) (squareRootEndpoint R / 2),
      if q.Prime then mertensSummatory (squareRootEndpoint R / q) else 0) = 0 :=
  squareRootMiddleHarmonicBand_two_eq_zero R

end RHLean.Proof
