import Mathlib
import RHLean.Proof.PostRootCovarianceLcmBoundaryClosure
import «research.ZERO_TARGET_MELLIN_FRESH_PRIME_SQUARE»

/-!
# Mellin interpolation of the physically clipped LCM fresh-prime square

The complete zero-target fresh-prime square has covariance eigenvalue
`(1-r)^2`.  The actual endpoint carrier is clipped, so the complementary
corners need not all be present.  This file computes that clipping defect
exactly on the already-compiled physical super-LCM indicator.

Write the four physical indicator corners as

  I00, I10, I01, I11.

The Mellin-weighted signed stencil is

  I00 - r I10 - r I01 + r^2 I11.

Pure algebra gives

  weightedStencil
    = rawStencil + (1-r) * (I10 + I01 - (1+r) I11).

Thus physical clipping does not preserve the complete-square double zero: it
leaves one explicit first-order edge.  Substituting the compiled physical LCM
wall theorem gives

  weightedStencil
    = topEscape - firstCrossing + (1-r) * edge.

For an actual admitted mixed owner child, `p*a <= W`; hence top escape is
impossible.  The only surviving terms are the favorable first-LCM crossing and
the one-dimensional Mellin edge.  This is the exact interface for the next
step: feed that edge to the existing logarithmic fresh-prime/square-correction
telescope instead of estimating the clipped cube by support.

No norm, support count, RH assumption, or new analytic estimate appears.
-/

noncomputable section

namespace RHLean.Proof

/-- Raw four-corner physical LCM indicator stencil. -/
def physicalSuperLcmRawStencil
    (W p a b : ℕ) : ℝ :=
  physicalSuperLcmIndicator W a b -
    physicalSuperLcmIndicator W (p * a) b -
    physicalSuperLcmIndicator W a (p * b) +
    physicalSuperLcmIndicator W (p * a) (p * b)

/-- Mellin-weighted physical LCM stencil with one-coordinate amplitude ratio
`r`; the double corner has ratio `r^2`. -/
def physicalSuperLcmMellinStencil
    (W p : ℕ) (r : ℝ) (a b : ℕ) : ℝ :=
  physicalSuperLcmIndicator W a b -
    r * physicalSuperLcmIndicator W (p * a) b -
    r * physicalSuperLcmIndicator W a (p * b) +
    r ^ 2 * physicalSuperLcmIndicator W (p * a) (p * b)

/-- The one-dimensional edge left when the complete-square double zero is
clipped by the physical endpoint. -/
def physicalSuperLcmMellinEdge
    (W p : ℕ) (r : ℝ) (a b : ℕ) : ℝ :=
  physicalSuperLcmIndicator W (p * a) b +
    physicalSuperLcmIndicator W a (p * b) -
    (1 + r) * physicalSuperLcmIndicator W (p * a) (p * b)

/-- **Exact clipping decomposition.**  This is pure four-corner algebra and is
valid without any primality/freshness hypothesis. -/
theorem physicalSuperLcmMellinStencil_eq_raw_add_edge
    (W p : ℕ) (r : ℝ) (a b : ℕ) :
    physicalSuperLcmMellinStencil W p r a b =
      physicalSuperLcmRawStencil W p a b +
        (1 - r) * physicalSuperLcmMellinEdge W p r a b := by
  unfold physicalSuperLcmMellinStencil physicalSuperLcmRawStencil
    physicalSuperLcmMellinEdge
  ring

/-- Substitute the already-compiled physical LCM wall classification into the
Mellin clipping identity. -/
theorem physicalSuperLcmMellinStencil_eq_walls_add_edge
    {W p a b : ℕ} (r : ℝ)
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hab : a ≤ b) (hbW : b ≤ W) :
    physicalSuperLcmMellinStencil W p r a b =
      (if W < Nat.lcm a b ∧ W < p * a then 1 else 0) -
        (if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b ∧ p * a ≤ W
          then 1 else 0) +
        (1 - r) * physicalSuperLcmMellinEdge W p r a b := by
  rw [physicalSuperLcmMellinStencil_eq_raw_add_edge]
  unfold physicalSuperLcmRawStencil
  rw [physicalSuperLcmIndicator_fourCorner_eq_walls hp hpa hpb hab hbW]

/-- **Actual admitted-owner form.**  Once the smaller mixed corner `p*a` is
inside the physical endpoint, positive top escape is impossible.  The clipped
Mellin square is therefore one negative first-crossing term plus one explicit
first-order edge. -/
theorem physicalSuperLcmMellinStencil_eq_neg_firstCrossing_add_edge_of_mul_le
    {W p a b : ℕ} (r : ℝ)
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hab : a ≤ b) (hbW : b ≤ W) (hpaW : p * a ≤ W) :
    physicalSuperLcmMellinStencil W p r a b =
      -(if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b ∧ p * a ≤ W
          then 1 else 0) +
        (1 - r) * physicalSuperLcmMellinEdge W p r a b := by
  rw [physicalSuperLcmMellinStencil_eq_walls_add_edge r hp hpa hpb hab hbW]
  have hnotTop : ¬ W < p * a := Nat.not_lt.mpr hpaW
  simp [hnotTop]

/-- The target-zero signed pair excess is the old Möbius pair weight, so the
same physical Mellin stencil is literally the NNS `co_0-div_0` carrier after
fresh-prime sector exchange. -/
def zeroTargetMellinPhysicalSuperLcmFourCorner
    (W p : ℕ) (r : ℝ) (a b : ℕ) : ℝ :=
  postRootZeroTargetPairExcess (a, b) *
    physicalSuperLcmMellinStencil W p r a b

/-- Display the preceding definition directly in the four zero-target corner
weights. -/
theorem zeroTargetMellinPhysicalSuperLcmFourCorner_eq_weighted_excess_corners
    {W p a b : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    zeroTargetMellinPhysicalSuperLcmFourCorner W p r a b =
      postRootZeroTargetPairExcess (a, b) * physicalSuperLcmIndicator W a b +
      zeroTargetPairExcess (-(r * realMoebiusStep a)) (realMoebiusStep b) *
        physicalSuperLcmIndicator W (p * a) b +
      zeroTargetPairExcess (realMoebiusStep a) (-(r * realMoebiusStep b)) *
        physicalSuperLcmIndicator W a (p * b) +
      zeroTargetPairExcess (-(r * realMoebiusStep a))
          (-(r * realMoebiusStep b)) *
        physicalSuperLcmIndicator W (p * a) (p * b) := by
  unfold zeroTargetMellinPhysicalSuperLcmFourCorner
    physicalSuperLcmMellinStencil
  simp only [postRootZeroTargetPairExcess_eq_weight,
    zeroTargetPairExcess_eq_mul]
  rw [realMoebiusStep_mul_prime_eq_neg hp hpa,
    realMoebiusStep_mul_prime_eq_neg hp hpb]
  ring

/-- Weighted zero-target version of the admitted-owner clipping theorem. -/
theorem zeroTargetMellinPhysicalSuperLcmFourCorner_eq_neg_firstCrossing_add_edge_of_mul_le
    {W p a b : ℕ} {r : ℝ} (_hr : 0 ≤ r)
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hab : a ≤ b) (hbW : b ≤ W) (hpaW : p * a ≤ W) :
    zeroTargetMellinPhysicalSuperLcmFourCorner W p r a b =
      -postRootZeroTargetPairExcess (a, b) *
          (if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b ∧ p * a ≤ W
            then 1 else 0) +
        (1 - r) * postRootZeroTargetPairExcess (a, b) *
          physicalSuperLcmMellinEdge W p r a b := by
  unfold zeroTargetMellinPhysicalSuperLcmFourCorner
  rw [physicalSuperLcmMellinStencil_eq_neg_firstCrossing_add_edge_of_mul_le
    r hp hpa hpb hab hbW hpaW]
  ring

end RHLean.Proof
