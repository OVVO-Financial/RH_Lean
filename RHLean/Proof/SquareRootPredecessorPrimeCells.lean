import Mathlib
import RHLean.Analysis.SquareRootMiddleSequentialCoherence
import RHLean.Proof.LowWheelSequentialSmoothRoughBoundary

/-!
# Predecessor-prime cells in the square-root reciprocal corridor

The completed one-prime frontier is killed by full divisor-fibre Möbius
inversion. This module keeps one chronological low-prime coordinate visible.
For a prime `p` and reciprocal label `k`, define

`A_p(k) = F_{<p}(floor(k/p))`,

where `F_{<p}` is the truncated Boolean-cube mass on primes strictly below `p`.
On squarefree support this is exactly the signed mass

`sum_{d <= k/p, P+(d) < p} mu(d)`.

The exact identities below separate the genuinely additive fresh-prime state
from the cumulative state, record the primorial deletion of completed old
cubes, and expose the cross-root cancellation against the terminal prime fibre.
They also give the elementary `p^3 < R^2` support condition for any unresolved
composite in a reciprocal cell with `p <= k`.

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

/-- **Fresh-prime decrement.** Admitting a prime `p` to the frozen lower-scale
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

/-- **Cumulative-state guardrail.** Adding `A_p(k)` back to the already-
processed smooth-shell coefficient reconstructs the old parent prefix exactly.
Therefore this pair by itself is not an independent cancellation mechanism. -/
theorem lowWheelSmoothFaceShellMass_add_predecessor_eq_parentPrefix
    (p k : ℕ) (hp : p.Prime) :
    lowWheelSmoothFaceShellMass p k + predecessorPrimeMass p k =
      frozenPrimeUniverseMass (primesUpTo (p - 1)) k := by
  rw [lowWheelSmoothFaceShellMass_eq_frozenPrimeUniverseMass p k hp]
  rw [frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor p k hp]
  ring

/-- **Primorial deletion.** If `k/p` already contains the complete Boolean cube
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
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqData := mem_primesUpTo.mp hq
    have hq2 : 2 ≤ q := hqData.1.two_le
    omega
  unfold predecessorPrimeMass
  rw [hS]
  simp [frozenPrimeUniverseMass, truncatedCubeAlternatingSum,
    primeProductAdmissible, primeFaceProduct, booleanCubeSign]

/-- **Prime edge plus `p=2` cancellation in the `k=2` fibre.** -/
theorem edge_prime_plus_p2_cancel_of_k2 :
    (-1 : ℤ) + predecessorPrimeMass 2 2 = 0 := by
  rw [predecessorPrimeMass_two_two]
  norm_num

/-- Algebra of one additive fresh-prime `(p,k)` cell. If `C` and `Q` are the
cofactor and unresolved-quotient states before `p`, while `A` and `H` are their
respective fresh-`p` deletions, then the four-corner update has the exact two
component form used by the finite gate. -/
theorem freshPrimePKCell_eq_cofactorDeletion_add_hitDeletion
    (C A Q H : ℤ) :
    (C - A) * (Q - H) - C * Q =
      -A * (Q - H) - C * H := by
  ring

/-- **Exact cross-root cancellation.** Add the terminal-prime predecessor mass
`N*A` to the additive low-prime step. The terminal-prime part cancels
algebraically, leaving only future composite hits and the current hit. -/
theorem freshPrimePKCrossRoot_eq_futureHitResidual
    (C A Q H N : ℤ) :
    ((C - A) * (Q - H) - C * Q) + N * A =
      -A * ((Q - H) - N) - C * H := by
  ring

/-- Replacing the evolving survivor population by the terminal prime population
necessarily drops the future-hit channel. This is the residual term exposed by
the preceding cross-root identity. -/
theorem predecessorPrime_terminalProjection_exposes_futureHits
    (A N future : ℤ) :
    -A * (N + future) = -A * N - A * future := by
  ring

/-- **Two-thirds support law.** In a reciprocal cell `k = floor(X_R/q)` with
`p <= k`, any unresolved composite `q` whose least prime factor is at least `p`
forces `p^3 < R^2`. Hence above the `R^(2/3)` predecessor scale the supported
cross-root residual has no current or future composite hit. -/
theorem reciprocalMiddle_composite_survivor_forces_predCube_lt_square
    {R p k q : ℕ}
    (hR : 2 ≤ R) (hp : 1 ≤ p) (hRq : R < q)
    (hqk : squareRootEndpoint R / q = k)
    (hpk : p ≤ k) (hqPrime : ¬ q.Prime)
    (hpMin : p ≤ q.minFac) :
    p ^ 3 < R ^ 2 := by
  have hqpos : 0 < q := by omega
  have hminSq : q.minFac ^ 2 ≤ q :=
    Nat.minFac_sq_le_self hqpos hqPrime
  have hpSq : p ^ 2 ≤ q.minFac ^ 2 :=
    Nat.pow_le_pow_left hpMin 2
  have hpSqQ : p ^ 2 ≤ q := hpSq.trans hminSq
  have hkq : k * q ≤ squareRootEndpoint R := by
    rw [← hqk]
    exact Nat.div_mul_le_self (squareRootEndpoint R) q
  have hpq : p * q ≤ squareRootEndpoint R := by
    exact (Nat.mul_le_mul_right q hpk).trans hkq
  have hpCube : p ^ 3 ≤ squareRootEndpoint R := by
    calc
      p ^ 3 = p * p ^ 2 := by ring
      _ ≤ p * q := Nat.mul_le_mul_left p hpSqQ
      _ ≤ squareRootEndpoint R := hpq
  have hXlt : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hsqpos : 0 < R ^ 2 := by positivity
    omega
  exact hpCube.trans_lt hXlt

/-- Contrapositive form of the two-thirds support law. -/
theorem no_reciprocalMiddle_composite_survivor_of_square_le_predCube
    {R p k q : ℕ}
    (hR : 2 ≤ R) (hp : 1 ≤ p) (hRq : R < q)
    (hqk : squareRootEndpoint R / q = k)
    (hpk : p ≤ k) (hqPrime : ¬ q.Prime)
    (hpMin : p ≤ q.minFac) (hcube : R ^ 2 ≤ p ^ 3) :
    False := by
  exact (Nat.not_lt_of_ge hcube)
    (reciprocalMiddle_composite_survivor_forces_predCube_lt_square
      hR hp hRq hqk hpk hqPrime hpMin)

/-- The already-formalized exact middle corridor, displayed in reciprocal
coordinates. The quotient label `k` is the only surviving large-prime label
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
