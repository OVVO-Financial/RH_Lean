import Mathlib
import «research.ZERO_TARGET_CRITICAL_CLIPPED_EDGE_BOUNDARY_SPLIT»
import «research.RECIPROCAL_COVARIANCE_PAIR_AMPLITUDE_CONTRACTION»

/-!
# Critical clipped-owner energy contracts on the literal recursive owner graph

The critical physical Mellin split isolates the only genuinely one-dimensional
boundary at owner `p` with amplitude coefficient

  (1/p) * (1 - 1/p).

The factor `1/p` is exactly the reciprocal fresh-owner descent of the physical
pair amplitude.  Therefore, after squaring, the clipped boundary is an ordinary
recursive child energy multiplied only by `(1 - 1/p)^2 <= 1`.

This file makes that statement literal on the existing fixed-owner child fibres
and inherits the already-compiled `79/81` outgoing-energy contraction.  No
independence assumption or new analytic estimate is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The companion-clipped owner factor.  The geometric predicate is exactly the
one-dimensional case from the critical Mellin edge split, expressed on the
ordered parent `(a,b)`. -/
def postRootCovarianceCriticalClippedOwnerFactor
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) : ℝ :=
  if W < p * parent.2 then (1 - 1 / (p : ℝ)) ^ 2 else 0

/-- Total recursive child energy carried by the genuinely clipped companion
owners, including the residual `(1-1/p)^2` edge factor. -/
def postRootCovarianceCriticalClippedOutgoingEnergy
    (W : ℕ) (parent : ℕ × ℕ) : ℝ :=
  ∑ p ∈ primesUpTo W,
    postRootCovarianceCriticalClippedOwnerFactor W parent p *
      (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        postRootCovarianceReciprocalPairEnergy mn)

/-- Pointwise currency conversion: the square of the critical clipped-boundary
amplitude coefficient against parent energy is exactly `(1-1/p)^2` times the
literal child reciprocal energy. -/
theorem criticalClippedBoundary_sq_mul_parentEnergy_eq_childEnergy
    {W p : ℕ} {parent mn : ℕ × ℕ}
    (hmn : mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p) :
    ((1 / (p : ℝ)) * (1 - 1 / (p : ℝ))) ^ 2 *
        postRootCovarianceReciprocalPairEnergy parent =
      (1 - 1 / (p : ℝ)) ^ 2 *
        postRootCovarianceReciprocalPairEnergy mn := by
  rw [postRootCovarianceFixedOwnerChild_energy_eq hmn]
  ring

/-- On every prime owner the residual edge multiplier has square at most one. -/
theorem criticalClippedOwnerFactor_le_one
    {W p : ℕ} {parent : ℕ × ℕ} (hp : p ∈ primesUpTo W) :
    postRootCovarianceCriticalClippedOwnerFactor W parent p ≤ 1 := by
  have hpPrime : p.Prime := prime_of_mem_primesUpTo hp
  have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hpOne : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.one_le
  have hx0 : 0 ≤ (1 : ℝ) / (p : ℝ) := by positivity
  have hx1 : (1 : ℝ) / (p : ℝ) ≤ 1 := by
    exact (div_le_one hpPos).2 hpOne
  have hprod : 0 ≤ ((1 : ℝ) / (p : ℝ)) *
      (1 - (1 : ℝ) / (p : ℝ)) :=
    mul_nonneg hx0 (sub_nonneg.mpr hx1)
  have hsq : (1 - (1 : ℝ) / (p : ℝ)) ^ 2 ≤ 1 := by
    nlinarith
  unfold postRootCovarianceCriticalClippedOwnerFactor
  split
  · exact hsq
  · norm_num

/-- The clipped boundary outgoing energy is a weighted sub-energy of the full
literal recursive outgoing energy. -/
theorem postRootCovarianceCriticalClippedOutgoingEnergy_le_outgoingEnergy
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootCovarianceCriticalClippedOutgoingEnergy W parent ≤
      postRootCovarianceReciprocalOutgoingEnergy W parent := by
  unfold postRootCovarianceCriticalClippedOutgoingEnergy
    postRootCovarianceReciprocalOutgoingEnergy
  apply Finset.sum_le_sum
  intro p hp
  let S : ℝ :=
    ∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
      postRootCovarianceReciprocalPairEnergy mn
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun mn _ =>
      postRootCovarianceReciprocalPairEnergy_nonneg mn
  have hfac := criticalClippedOwnerFactor_le_one
    (W := W) (p := p) (parent := parent) hp
  have hnon : 0 ≤
      (1 - postRootCovarianceCriticalClippedOwnerFactor W parent p) * S :=
    mul_nonneg (sub_nonneg.mpr hfac) hS0
  change postRootCovarianceCriticalClippedOwnerFactor W parent p * S ≤ S
  nlinarith

/-- **Strict clipped-boundary contraction.**  The only incomplete first-order
Mellin edge inherits the same `79/81` contraction as the full reciprocal owner
graph. -/
theorem postRootCovarianceCriticalClippedOutgoingEnergy_le_79_over_81
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootCovarianceCriticalClippedOutgoingEnergy W parent ≤
      (79 / 81 : ℝ) * postRootCovarianceReciprocalPairEnergy parent := by
  exact le_trans
    (postRootCovarianceCriticalClippedOutgoingEnergy_le_outgoingEnergy W parent)
    (postRootCovarianceReciprocalOutgoingEnergy_le_79_over_81 W parent)

end RHLean.Proof
