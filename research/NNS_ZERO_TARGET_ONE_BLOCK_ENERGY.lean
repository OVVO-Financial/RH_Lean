import Mathlib
import RHLean.Proof.SquareRootLowPrimeOneBlockTerminalBudget
import RHLean.Proof.RealSquareBlockIncrements
import «research.GLOBAL_RETURNED_CORE_ONE_AMPLITUDE»
import «research.NNS_ZERO_TARGET_NORMALIZED_STOKES»

/-!
# NNS zero-target normalization of the literal one-block correlation step

PR #877 proves the exact root-to-root hard-correlation update

  Corr_(R+1) - Corr_R = mu(R) - Delta_R,

where Delta_R is the signed Mobius mass of the single square block
[R^2,(R+1)^2).

This file places the *actual cross term* in that energy update into Fred's
target-zero NNS covariance currency.  The old correlation is represented by
the literal Mobius tail [R,R^2-1].  The current update is split into its root
atom +mu(R) and its one-block contribution -mu(m).

Thus no new proxy or endpoint criterion is introduced: the NNS co/divergent
masses below are exactly the two physical factors already present in the #877
energy step.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The physical old-tail carrier whose signed sum is the real form of Corr_R. -/
def nnsOneBlockOldTailCarrier (R : ℕ) : Finset ℕ :=
  Finset.Icc R (squareRootEndpoint R)

/-- Orient the old tail so that its real sum casts to +Corr_R. -/
def nnsOneBlockOldTailEvent (n : ℕ) : ℝ :=
  -realMoebiusStep n

/-- The signed root atom in the one-block update. -/
def nnsOneBlockRootUpdateEvent (R : ℕ) : ℝ :=
  realMoebiusStep R

/-- The signed square-block atoms in the one-block update. -/
def nnsOneBlockSquareUpdateEvent (m : ℕ) : ℝ :=
  -realCanonicalMoebiusWeight m

def nnsOneBlockOldTailMass (R : ℕ) : ℝ :=
  ∑ n ∈ nnsOneBlockOldTailCarrier R, nnsOneBlockOldTailEvent n

def nnsOneBlockUpdateMass (R : ℕ) : ℝ :=
  nnsOneBlockRootUpdateEvent R - realCanonicalTotalIncrement R

/-- Same-sign target-zero mass between the old tail and the literal current
root-plus-square-block update. -/
def nnsOneBlockCoMass (R : ℕ) : ℝ :=
  (∑ n ∈ nnsOneBlockOldTailCarrier R,
      zeroTargetCoPartialPair
        (nnsOneBlockOldTailEvent n)
        (nnsOneBlockRootUpdateEvent R)) +
    ∑ n ∈ nnsOneBlockOldTailCarrier R,
      ∑ m ∈ canonicalSquareBlock R,
        zeroTargetCoPartialPair
          (nnsOneBlockOldTailEvent n)
          (nnsOneBlockSquareUpdateEvent m)

/-- Opposite-sign target-zero mass on exactly the same rectangular carrier. -/
def nnsOneBlockDivergentMass (R : ℕ) : ℝ :=
  (∑ n ∈ nnsOneBlockOldTailCarrier R,
      zeroTargetDivergentPair
        (nnsOneBlockOldTailEvent n)
        (nnsOneBlockRootUpdateEvent R)) +
    ∑ n ∈ nnsOneBlockOldTailCarrier R,
      ∑ m ∈ canonicalSquareBlock R,
        zeroTargetDivergentPair
          (nnsOneBlockOldTailEvent n)
          (nnsOneBlockSquareUpdateEvent m)

/-- Raw signed NNS excess on the same carrier. -/
def nnsOneBlockCrossExcess (R : ℕ) : ℝ :=
  (∑ n ∈ nnsOneBlockOldTailCarrier R,
      zeroTargetPairExcess
        (nnsOneBlockOldTailEvent n)
        (nnsOneBlockRootUpdateEvent R)) +
    ∑ n ∈ nnsOneBlockOldTailCarrier R,
      ∑ m ∈ canonicalSquareBlock R,
        zeroTargetPairExcess
          (nnsOneBlockOldTailEvent n)
          (nnsOneBlockSquareUpdateEvent m)

def nnsOneBlockTotalPairMass (R : ℕ) : ℝ :=
  nnsOneBlockCoMass R + nnsOneBlockDivergentMass R

/-- Squarefree mass of the historical tail.  Since Mobius is in {-1,0,1},
this is exactly Fred's `Q_R^-`. -/
def nnsOneBlockOldSquarefreeMass (R : ℕ) : ℝ :=
  ∑ n ∈ nnsOneBlockOldTailCarrier R, (realMoebiusStep n) ^ 2

/-- Squarefree mass of the root atom plus the new square block.  This is
exactly Fred's `Q_R^+`. -/
def nnsOneBlockUpdateSquarefreeMass (R : ℕ) : ℝ :=
  (realMoebiusStep R) ^ 2 +
    ∑ m ∈ canonicalSquareBlock R, (realCanonicalMoebiusWeight m) ^ 2

/-- Dimensionless historical signed bias `alpha_R = C_R / Q_R^-`, with the
same zero-denominator convention as the NNS normalization. -/
def nnsOneBlockAlpha (R : ℕ) : ℝ :=
  if nnsOneBlockOldSquarefreeMass R = 0 then 0
  else nnsOneBlockOldTailMass R / nnsOneBlockOldSquarefreeMass R

/-- Dimensionless inherited-block signed bias `beta_R = U_R / Q_R^+`. -/
def nnsOneBlockBeta (R : ℕ) : ℝ :=
  if nnsOneBlockUpdateSquarefreeMass R = 0 then 0
  else nnsOneBlockUpdateMass R / nnsOneBlockUpdateSquarefreeMass R

def nnsOneBlockNormalizedCovariance (R : ℕ) : ℝ :=
  nnsZeroTargetNormalizedCovariance
    (nnsOneBlockCoMass R) (nnsOneBlockDivergentMass R)

theorem nnsOneBlockCoMass_nonneg (R : ℕ) :
    0 ≤ nnsOneBlockCoMass R := by
  unfold nnsOneBlockCoMass
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro n _hn
    exact zeroTargetCoPartialPair_nonneg _ _
  · apply Finset.sum_nonneg
    intro n _hn
    apply Finset.sum_nonneg
    intro m _hm
    exact zeroTargetCoPartialPair_nonneg _ _

theorem nnsOneBlockDivergentMass_nonneg (R : ℕ) :
    0 ≤ nnsOneBlockDivergentMass R := by
  unfold nnsOneBlockDivergentMass
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro n _hn
    exact zeroTargetDivergentPair_nonneg _ _
  · apply Finset.sum_nonneg
    intro n _hn
    apply Finset.sum_nonneg
    intro m _hm
    exact zeroTargetDivergentPair_nonneg _ _

theorem nnsOneBlockNormalizedCovariance_bounds (R : ℕ) :
    -1 ≤ nnsOneBlockNormalizedCovariance R ∧
      nnsOneBlockNormalizedCovariance R ≤ 1 := by
  apply nnsZeroTargetNormalizedCovariance_bounds
  · exact nnsOneBlockCoMass_nonneg R
  · exact nnsOneBlockDivergentMass_nonneg R

/-- Co-minus-divergent mass is exactly the raw target-zero excess on this
literal one-block carrier. -/
theorem nnsOneBlockCo_sub_div_eq_crossExcess (R : ℕ) :
    nnsOneBlockCoMass R - nnsOneBlockDivergentMass R =
      nnsOneBlockCrossExcess R := by
  unfold nnsOneBlockCoMass nnsOneBlockDivergentMass
    nnsOneBlockCrossExcess
  have hroot :
      (∑ n ∈ nnsOneBlockOldTailCarrier R,
          zeroTargetCoPartialPair
            (nnsOneBlockOldTailEvent n)
            (nnsOneBlockRootUpdateEvent R)) -
        (∑ n ∈ nnsOneBlockOldTailCarrier R,
          zeroTargetDivergentPair
            (nnsOneBlockOldTailEvent n)
            (nnsOneBlockRootUpdateEvent R)) =
      ∑ n ∈ nnsOneBlockOldTailCarrier R,
        zeroTargetPairExcess
          (nnsOneBlockOldTailEvent n)
          (nnsOneBlockRootUpdateEvent R) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    unfold zeroTargetPairExcess
    rfl
  have hblock :
      (∑ n ∈ nnsOneBlockOldTailCarrier R,
          ∑ m ∈ canonicalSquareBlock R,
            zeroTargetCoPartialPair
              (nnsOneBlockOldTailEvent n)
              (nnsOneBlockSquareUpdateEvent m)) -
        (∑ n ∈ nnsOneBlockOldTailCarrier R,
          ∑ m ∈ canonicalSquareBlock R,
            zeroTargetDivergentPair
              (nnsOneBlockOldTailEvent n)
              (nnsOneBlockSquareUpdateEvent m)) =
      ∑ n ∈ nnsOneBlockOldTailCarrier R,
        ∑ m ∈ canonicalSquareBlock R,
          zeroTargetPairExcess
            (nnsOneBlockOldTailEvent n)
            (nnsOneBlockSquareUpdateEvent m) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _hm
    unfold zeroTargetPairExcess
    rfl
  rw [show
    ((∑ n ∈ nnsOneBlockOldTailCarrier R,
        zeroTargetCoPartialPair
          (nnsOneBlockOldTailEvent n)
          (nnsOneBlockRootUpdateEvent R)) +
      ∑ n ∈ nnsOneBlockOldTailCarrier R,
        ∑ m ∈ canonicalSquareBlock R,
          zeroTargetCoPartialPair
            (nnsOneBlockOldTailEvent n)
            (nnsOneBlockSquareUpdateEvent m)) -
    ((∑ n ∈ nnsOneBlockOldTailCarrier R,
        zeroTargetDivergentPair
          (nnsOneBlockOldTailEvent n)
          (nnsOneBlockRootUpdateEvent R)) +
      ∑ n ∈ nnsOneBlockOldTailCarrier R,
        ∑ m ∈ canonicalSquareBlock R,
          zeroTargetDivergentPair
            (nnsOneBlockOldTailEvent n)
            (nnsOneBlockSquareUpdateEvent m)) =
    ((∑ n ∈ nnsOneBlockOldTailCarrier R,
        zeroTargetCoPartialPair
          (nnsOneBlockOldTailEvent n)
          (nnsOneBlockRootUpdateEvent R)) -
      ∑ n ∈ nnsOneBlockOldTailCarrier R,
        zeroTargetDivergentPair
          (nnsOneBlockOldTailEvent n)
          (nnsOneBlockRootUpdateEvent R)) +
    ((∑ n ∈ nnsOneBlockOldTailCarrier R,
        ∑ m ∈ canonicalSquareBlock R,
          zeroTargetCoPartialPair
            (nnsOneBlockOldTailEvent n)
            (nnsOneBlockSquareUpdateEvent m)) -
      ∑ n ∈ nnsOneBlockOldTailCarrier R,
        ∑ m ∈ canonicalSquareBlock R,
          zeroTargetDivergentPair
            (nnsOneBlockOldTailEvent n)
            (nnsOneBlockSquareUpdateEvent m)) by ring]
  rw [hroot, hblock]

/-- The raw NNS excess is exactly old-correlation mass times current one-block
update mass. -/
theorem nnsOneBlockCrossExcess_eq_tail_mul_update (R : ℕ) :
    nnsOneBlockCrossExcess R =
      nnsOneBlockOldTailMass R * nnsOneBlockUpdateMass R := by
  unfold nnsOneBlockCrossExcess nnsOneBlockOldTailMass
    nnsOneBlockUpdateMass nnsOneBlockRootUpdateEvent
    nnsOneBlockSquareUpdateEvent
  simp_rw [zeroTargetPairExcess_eq_mul]
  have hroot :
      (∑ n ∈ nnsOneBlockOldTailCarrier R,
          nnsOneBlockOldTailEvent n * realMoebiusStep R) =
        (∑ n ∈ nnsOneBlockOldTailCarrier R,
          nnsOneBlockOldTailEvent n) * realMoebiusStep R := by
    rw [Finset.sum_mul]
  have hblock :
      (∑ n ∈ nnsOneBlockOldTailCarrier R,
          ∑ m ∈ canonicalSquareBlock R,
            nnsOneBlockOldTailEvent n * (-realCanonicalMoebiusWeight m)) =
        (∑ n ∈ nnsOneBlockOldTailCarrier R,
          nnsOneBlockOldTailEvent n) * (-realCanonicalTotalIncrement R) := by
    calc
      (∑ n ∈ nnsOneBlockOldTailCarrier R,
          ∑ m ∈ canonicalSquareBlock R,
            nnsOneBlockOldTailEvent n * (-realCanonicalMoebiusWeight m)) =
        ∑ n ∈ nnsOneBlockOldTailCarrier R,
          nnsOneBlockOldTailEvent n *
            (∑ m ∈ canonicalSquareBlock R, -realCanonicalMoebiusWeight m) := by
              apply Finset.sum_congr rfl
              intro n _hn
              rw [Finset.mul_sum]
      _ = (∑ n ∈ nnsOneBlockOldTailCarrier R,
            nnsOneBlockOldTailEvent n) *
          (∑ m ∈ canonicalSquareBlock R, -realCanonicalMoebiusWeight m) := by
              rw [Finset.sum_mul]
      _ = (∑ n ∈ nnsOneBlockOldTailCarrier R,
            nnsOneBlockOldTailEvent n) * (-realCanonicalTotalIncrement R) := by
              simp [realCanonicalTotalIncrement]
  rw [hroot, hblock]
  ring

theorem nnsOneBlockNormalizedCovariance_mul_total (R : ℕ) :
    nnsOneBlockNormalizedCovariance R *
        nnsOneBlockTotalPairMass R =
      nnsOneBlockCrossExcess R := by
  unfold nnsOneBlockNormalizedCovariance nnsOneBlockTotalPairMass
  rw [nnsZeroTargetNormalizedCovariance_mul_total
    (nnsOneBlockCoMass_nonneg R) (nnsOneBlockDivergentMass_nonneg R)]
  exact nnsOneBlockCo_sub_div_eq_crossExcess R

private theorem abs_realMoebiusStep_eq_sq_nnsOneBlock (n : ℕ) :
    |realMoebiusStep n| = (realMoebiusStep n) ^ 2 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h]

private theorem abs_nnsOneBlockOldTailEvent_eq_sq (n : ℕ) :
    |nnsOneBlockOldTailEvent n| = (realMoebiusStep n) ^ 2 := by
  unfold nnsOneBlockOldTailEvent
  rw [abs_neg, abs_realMoebiusStep_eq_sq_nnsOneBlock]

private theorem abs_nnsOneBlockRootUpdateEvent_eq_sq (R : ℕ) :
    |nnsOneBlockRootUpdateEvent R| = (realMoebiusStep R) ^ 2 := by
  unfold nnsOneBlockRootUpdateEvent
  exact abs_realMoebiusStep_eq_sq_nnsOneBlock R

private theorem abs_nnsOneBlockSquareUpdateEvent_eq_sq (m : ℕ) :
    |nnsOneBlockSquareUpdateEvent m| =
      (realCanonicalMoebiusWeight m) ^ 2 := by
  unfold nnsOneBlockSquareUpdateEvent
  rw [abs_neg]
  simpa [realCanonicalMoebiusWeight, realMoebiusStep] using
    abs_realMoebiusStep_eq_sq_nnsOneBlock m

/-- **Closed denominator formula.**  The total target-zero NNS mass of the
literal old-tail x current-update rectangle factors exactly as
`Q_R^- * Q_R^+`. -/
theorem nnsOneBlockTotalPairMass_eq_squarefreeMass_mul (R : ℕ) :
    nnsOneBlockTotalPairMass R =
      nnsOneBlockOldSquarefreeMass R *
        nnsOneBlockUpdateSquarefreeMass R := by
  have hroot :
      (∑ n ∈ nnsOneBlockOldTailCarrier R,
          zeroTargetCoPartialPair
            (nnsOneBlockOldTailEvent n)
            (nnsOneBlockRootUpdateEvent R)) +
        (∑ n ∈ nnsOneBlockOldTailCarrier R,
          zeroTargetDivergentPair
            (nnsOneBlockOldTailEvent n)
            (nnsOneBlockRootUpdateEvent R)) =
      nnsOneBlockOldSquarefreeMass R * (realMoebiusStep R) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ n ∈ nnsOneBlockOldTailCarrier R,
          (zeroTargetCoPartialPair
              (nnsOneBlockOldTailEvent n)
              (nnsOneBlockRootUpdateEvent R) +
            zeroTargetDivergentPair
              (nnsOneBlockOldTailEvent n)
              (nnsOneBlockRootUpdateEvent R))) =
        ∑ n ∈ nnsOneBlockOldTailCarrier R,
          |nnsOneBlockOldTailEvent n| *
            |nnsOneBlockRootUpdateEvent R| := by
              apply Finset.sum_congr rfl
              intro n _hn
              exact zeroTargetCoPartial_add_divergent_eq_abs_mul_abs _ _
      _ = ∑ n ∈ nnsOneBlockOldTailCarrier R,
          (realMoebiusStep n) ^ 2 * (realMoebiusStep R) ^ 2 := by
              apply Finset.sum_congr rfl
              intro n _hn
              rw [abs_nnsOneBlockOldTailEvent_eq_sq,
                abs_nnsOneBlockRootUpdateEvent_eq_sq]
      _ = nnsOneBlockOldSquarefreeMass R *
          (realMoebiusStep R) ^ 2 := by
              unfold nnsOneBlockOldSquarefreeMass
              rw [Finset.sum_mul]
  have hblock :
      (∑ n ∈ nnsOneBlockOldTailCarrier R,
          ∑ m ∈ canonicalSquareBlock R,
            zeroTargetCoPartialPair
              (nnsOneBlockOldTailEvent n)
              (nnsOneBlockSquareUpdateEvent m)) +
        (∑ n ∈ nnsOneBlockOldTailCarrier R,
          ∑ m ∈ canonicalSquareBlock R,
            zeroTargetDivergentPair
              (nnsOneBlockOldTailEvent n)
              (nnsOneBlockSquareUpdateEvent m)) =
      nnsOneBlockOldSquarefreeMass R *
        (∑ m ∈ canonicalSquareBlock R,
          (realCanonicalMoebiusWeight m) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ n ∈ nnsOneBlockOldTailCarrier R,
          ((∑ m ∈ canonicalSquareBlock R,
              zeroTargetCoPartialPair
                (nnsOneBlockOldTailEvent n)
                (nnsOneBlockSquareUpdateEvent m)) +
            ∑ m ∈ canonicalSquareBlock R,
              zeroTargetDivergentPair
                (nnsOneBlockOldTailEvent n)
                (nnsOneBlockSquareUpdateEvent m))) =
        ∑ n ∈ nnsOneBlockOldTailCarrier R,
          ∑ m ∈ canonicalSquareBlock R,
            (zeroTargetCoPartialPair
                (nnsOneBlockOldTailEvent n)
                (nnsOneBlockSquareUpdateEvent m) +
              zeroTargetDivergentPair
                (nnsOneBlockOldTailEvent n)
                (nnsOneBlockSquareUpdateEvent m)) := by
              apply Finset.sum_congr rfl
              intro n _hn
              rw [Finset.sum_add_distrib]
      _ = ∑ n ∈ nnsOneBlockOldTailCarrier R,
          ∑ m ∈ canonicalSquareBlock R,
            |nnsOneBlockOldTailEvent n| *
              |nnsOneBlockSquareUpdateEvent m| := by
              apply Finset.sum_congr rfl
              intro n _hn
              apply Finset.sum_congr rfl
              intro m _hm
              exact zeroTargetCoPartial_add_divergent_eq_abs_mul_abs _ _
      _ = ∑ n ∈ nnsOneBlockOldTailCarrier R,
          ∑ m ∈ canonicalSquareBlock R,
            (realMoebiusStep n) ^ 2 *
              (realCanonicalMoebiusWeight m) ^ 2 := by
              apply Finset.sum_congr rfl
              intro n _hn
              apply Finset.sum_congr rfl
              intro m _hm
              rw [abs_nnsOneBlockOldTailEvent_eq_sq,
                abs_nnsOneBlockSquareUpdateEvent_eq_sq]
      _ = ∑ n ∈ nnsOneBlockOldTailCarrier R,
          (realMoebiusStep n) ^ 2 *
            (∑ m ∈ canonicalSquareBlock R,
              (realCanonicalMoebiusWeight m) ^ 2) := by
              apply Finset.sum_congr rfl
              intro n _hn
              rw [Finset.mul_sum]
      _ = nnsOneBlockOldSquarefreeMass R *
          (∑ m ∈ canonicalSquareBlock R,
            (realCanonicalMoebiusWeight m) ^ 2) := by
              unfold nnsOneBlockOldSquarefreeMass
              rw [Finset.sum_mul]
  unfold nnsOneBlockTotalPairMass nnsOneBlockCoMass
    nnsOneBlockDivergentMass nnsOneBlockUpdateSquarefreeMass
  calc
    _ =
      ((∑ n ∈ nnsOneBlockOldTailCarrier R,
          zeroTargetCoPartialPair
            (nnsOneBlockOldTailEvent n)
            (nnsOneBlockRootUpdateEvent R)) +
        (∑ n ∈ nnsOneBlockOldTailCarrier R,
          zeroTargetDivergentPair
            (nnsOneBlockOldTailEvent n)
            (nnsOneBlockRootUpdateEvent R))) +
      ((∑ n ∈ nnsOneBlockOldTailCarrier R,
          ∑ m ∈ canonicalSquareBlock R,
            zeroTargetCoPartialPair
              (nnsOneBlockOldTailEvent n)
              (nnsOneBlockSquareUpdateEvent m)) +
        (∑ n ∈ nnsOneBlockOldTailCarrier R,
          ∑ m ∈ canonicalSquareBlock R,
            zeroTargetDivergentPair
              (nnsOneBlockOldTailEvent n)
              (nnsOneBlockSquareUpdateEvent m))) := by ring
    _ = nnsOneBlockOldSquarefreeMass R * (realMoebiusStep R) ^ 2 +
        nnsOneBlockOldSquarefreeMass R *
          (∑ m ∈ canonicalSquareBlock R,
            (realCanonicalMoebiusWeight m) ^ 2) := by
          rw [hroot, hblock]
    _ = nnsOneBlockOldSquarefreeMass R *
        ((realMoebiusStep R) ^ 2 +
          ∑ m ∈ canonicalSquareBlock R,
            (realCanonicalMoebiusWeight m) ^ 2) := by ring

/-- **The global closed form.**  The literal target-zero NNS covariance is
exactly the product of the normalized historical and inherited-block biases:
`rho_R = alpha_R * beta_R`.  No statistical or asymptotic assumption enters. -/
theorem nnsOneBlockNormalizedCovariance_eq_alpha_mul_beta (R : ℕ) :
    nnsOneBlockNormalizedCovariance R =
      nnsOneBlockAlpha R * nnsOneBlockBeta R := by
  unfold nnsOneBlockNormalizedCovariance nnsZeroTargetNormalizedCovariance
  rw [show nnsOneBlockCoMass R + nnsOneBlockDivergentMass R =
      nnsOneBlockTotalPairMass R by rfl,
    nnsOneBlockTotalPairMass_eq_squarefreeMass_mul,
    nnsOneBlockCo_sub_div_eq_crossExcess,
    nnsOneBlockCrossExcess_eq_tail_mul_update]
  by_cases hOld : nnsOneBlockOldSquarefreeMass R = 0
  · simp [nnsOneBlockAlpha, nnsOneBlockBeta, hOld]
  · by_cases hNew : nnsOneBlockUpdateSquarefreeMass R = 0
    · simp [nnsOneBlockAlpha, nnsOneBlockBeta, hNew]
    · have hprod :
          nnsOneBlockOldSquarefreeMass R *
              nnsOneBlockUpdateSquarefreeMass R ≠ 0 :=
        mul_ne_zero hOld hNew
      rw [if_neg hprod]
      simp only [nnsOneBlockAlpha, nnsOneBlockBeta, hOld, hNew, if_false]
      field_simp
      ring

/-- The oriented real old-tail sum casts exactly to the repository's hard
rough correlation. -/
theorem nnsOneBlockOldTailMass_cast_eq_correlation
    (R : ℕ) (hR : 2 ≤ R) :
    ((nnsOneBlockOldTailMass R : ℝ) : ℂ) =
      squareRootCanonicalRoughCorrelation R := by
  unfold nnsOneBlockOldTailMass nnsOneBlockOldTailCarrier
    nnsOneBlockOldTailEvent
  have htail := lowOwnerFarTailAmplitudeReal_eq_Icc R hR
  have hcorr := lowOwnerFarTailAmplitudeReal_cast_eq_neg_correlation R hR
  calc
    ((∑ n ∈ Finset.Icc R (squareRootEndpoint R),
        -realMoebiusStep n : ℝ) : ℂ) =
      -((∑ n ∈ Finset.Icc R (squareRootEndpoint R),
          realMoebiusStep n : ℝ) : ℂ) := by
            push_cast
            ring
    _ = -(lowOwnerFarTailAmplitudeReal R : ℂ) := by rw [htail]
    _ = squareRootCanonicalRoughCorrelation R := by rw [hcorr]; ring

/-- The real current-block update casts exactly to the update in #877. -/
theorem nnsOneBlockUpdateMass_cast_eq_update (R : ℕ) :
    ((nnsOneBlockUpdateMass R : ℝ) : ℂ) =
      canonicalMoebiusWeight R - canonicalTotalIncrement R := by
  unfold nnsOneBlockUpdateMass nnsOneBlockRootUpdateEvent realMoebiusStep
  push_cast
  rw [realCanonicalTotalIncrement_cast]
  rfl

/-! ## Same-parent sector: exact divergent feedback -/

/-- A current square-block child carries the positive sign of its canonical old
parent after the #877 update sign is applied. -/
theorem nnsOneBlockSquareUpdateEvent_eq_parent
    {R c m : ℕ} (hR : 3 ≤ R)
    (hm : m ∈ canonicalParentFiber R c) :
    nnsOneBlockSquareUpdateEvent m = realMoebiusStep c := by
  rw [canonicalParentFiber, Finset.mem_filter] at hm
  have hmBlock := hm.1
  have hsq := hm.2.1
  have hparent := hm.2.2
  have hmBounds : R ^ 2 ≤ m ∧ m < (R + 1) ^ 2 := by
    simpa [squareBlockInterval, Finset.mem_Ico] using hmBlock
  have hm1 : 1 < m := by
    have h9 : 9 ≤ R ^ 2 := by nlinarith
    omega
  have hmu := canonicalSignedParent_moebius hsq hm1
  unfold nnsOneBlockSquareUpdateEvent realCanonicalMoebiusWeight
    realMoebiusStep
  rw [hmu, hparent]
  push_cast
  ring

/-- **Same-parent co-partial mass vanishes exactly.**

The old-tail event at parent c is -mu(c), while every current-block child in
that fibre has update event +mu(c). -/
theorem nnsOneBlockSameParentCo_eq_zero
    {R c m : ℕ} (hR : 3 ≤ R)
    (hm : m ∈ canonicalParentFiber R c) :
    zeroTargetCoPartialPair
        (nnsOneBlockOldTailEvent c)
        (nnsOneBlockSquareUpdateEvent m) = 0 := by
  rw [nnsOneBlockSquareUpdateEvent_eq_parent hR hm]
  unfold nnsOneBlockOldTailEvent
  simp

/-- **Same-parent divergent mass is exactly the parent square.** -/
theorem nnsOneBlockSameParentDiv_eq_sq
    {R c m : ℕ} (hR : 3 ≤ R)
    (hm : m ∈ canonicalParentFiber R c) :
    zeroTargetDivergentPair
        (nnsOneBlockOldTailEvent c)
        (nnsOneBlockSquareUpdateEvent m) =
      (realMoebiusStep c) ^ 2 := by
  rw [nnsOneBlockSquareUpdateEvent_eq_parent hR hm]
  unfold nnsOneBlockOldTailEvent
  simp

/-- The root atom is itself a same-coordinate opposite-sign update. -/
@[simp] theorem nnsOneBlockRootSelfCo_eq_zero (R : ℕ) :
    zeroTargetCoPartialPair
        (nnsOneBlockOldTailEvent R)
        (nnsOneBlockRootUpdateEvent R) = 0 := by
  unfold nnsOneBlockOldTailEvent nnsOneBlockRootUpdateEvent
  simp

@[simp] theorem nnsOneBlockRootSelfDiv_eq_sq (R : ℕ) :
    zeroTargetDivergentPair
        (nnsOneBlockOldTailEvent R)
        (nnsOneBlockRootUpdateEvent R) =
      (realMoebiusStep R) ^ 2 := by
  unfold nnsOneBlockOldTailEvent nnsOneBlockRootUpdateEvent
  simp

theorem nnsOneBlockRootSelfExcess_eq_neg_sq (R : ℕ) :
    zeroTargetPairExcess
        (nnsOneBlockOldTailEvent R)
        (nnsOneBlockRootUpdateEvent R) =
      -(realMoebiusStep R) ^ 2 := by
  unfold zeroTargetPairExcess
  rw [nnsOneBlockRootSelfCo_eq_zero, nnsOneBlockRootSelfDiv_eq_sq]
  ring

/-- Parents that are themselves visible on the old-tail clock. -/
def nnsOneBlockMatchedParentSet (R : ℕ) : Finset ℕ :=
  Finset.Icc R (oldParentCutoff R)

/-- Same-parent target-zero excess after summing every visible canonical
parent fibre. -/
def nnsOneBlockSameParentExcess (R : ℕ) : ℝ :=
  ∑ c ∈ nnsOneBlockMatchedParentSet R,
    ∑ m ∈ canonicalParentFiber R c,
      zeroTargetPairExcess
        (nnsOneBlockOldTailEvent c)
        (nnsOneBlockSquareUpdateEvent m)

/-- **The matched parent diagonal is a negative squarefree energy.**

This is the first genuinely dissipative component of the normalized one-block
covariance: every visible parent-child fibre contributes only divergent mass. -/
theorem nnsOneBlockSameParentExcess_eq_neg_diagonal
    (R : ℕ) (hR : 3 ≤ R) :
    nnsOneBlockSameParentExcess R =
      - ∑ c ∈ nnsOneBlockMatchedParentSet R,
          ((canonicalParentFiber R c).card : ℝ) *
            (realMoebiusStep c) ^ 2 := by
  unfold nnsOneBlockSameParentExcess
  calc
    (∑ c ∈ nnsOneBlockMatchedParentSet R,
      ∑ m ∈ canonicalParentFiber R c,
        zeroTargetPairExcess
          (nnsOneBlockOldTailEvent c)
          (nnsOneBlockSquareUpdateEvent m)) =
      ∑ c ∈ nnsOneBlockMatchedParentSet R,
        ∑ _m ∈ canonicalParentFiber R c,
          -(realMoebiusStep c) ^ 2 := by
            apply Finset.sum_congr rfl
            intro c _hc
            apply Finset.sum_congr rfl
            intro m hm
            unfold zeroTargetPairExcess
            rw [nnsOneBlockSameParentCo_eq_zero hR hm,
              nnsOneBlockSameParentDiv_eq_sq hR hm]
            ring
    _ = - ∑ c ∈ nnsOneBlockMatchedParentSet R,
          ((canonicalParentFiber R c).card : ℝ) *
            (realMoebiusStep c) ^ 2 := by
            simp [mul_comm]
            ring

/-- Root self-pair plus all visible canonical parent diagonals: the complete
identified diagonal sector is purely dissipative. -/
def nnsOneBlockIdentifiedDiagonalExcess (R : ℕ) : ℝ :=
  zeroTargetPairExcess
      (nnsOneBlockOldTailEvent R)
      (nnsOneBlockRootUpdateEvent R) +
    nnsOneBlockSameParentExcess R

theorem nnsOneBlockIdentifiedDiagonalExcess_eq_neg_energy
    (R : ℕ) (hR : 3 ≤ R) :
    nnsOneBlockIdentifiedDiagonalExcess R =
      -((realMoebiusStep R) ^ 2 +
        ∑ c ∈ nnsOneBlockMatchedParentSet R,
          ((canonicalParentFiber R c).card : ℝ) *
            (realMoebiusStep c) ^ 2) := by
  unfold nnsOneBlockIdentifiedDiagonalExcess
  rw [nnsOneBlockRootSelfExcess_eq_neg_sq,
    nnsOneBlockSameParentExcess_eq_neg_diagonal R hR]
  ring

theorem nnsOneBlockIdentifiedDiagonalExcess_nonpos
    (R : ℕ) (hR : 3 ≤ R) :
    nnsOneBlockIdentifiedDiagonalExcess R ≤ 0 := by
  rw [nnsOneBlockIdentifiedDiagonalExcess_eq_neg_energy R hR]
  apply neg_nonpos.mpr
  apply add_nonneg
  · exact sq_nonneg _
  · apply Finset.sum_nonneg
    intro c _hc
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem nnsOneBlockSameParentExcess_nonpos
    (R : ℕ) (hR : 3 ≤ R) :
    nnsOneBlockSameParentExcess R ≤ 0 := by
  rw [nnsOneBlockSameParentExcess_eq_neg_diagonal R hR]
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro c _hc
  exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)


/-! ## Exact unresolved cross-parent remainder -/

/-- After removing the root self-pair and every visible same-parent fibre, this
is the only cross term left in the literal #877 one-block NNS carrier. -/
def nnsOneBlockUnresolvedCrossParentRemainder (R : ℕ) : ℝ :=
  nnsOneBlockCrossExcess R - nnsOneBlockIdentifiedDiagonalExcess R

/-- **Exact one-block cross-parent zero-target dictionary.**

After the literal #877 cross term is grouped by the canonical parent of each
new square-block atom, the unresolved sector is exactly the negative
zero-target pairing of the old tail with the root parent and every frozen
canonical parent, plus the two diagonal terms already extracted above.

This is an equality of the actual one-block carrier.  No absolute value,
reciprocal reweighting, or new analytic estimate is introduced. -/
theorem nnsOneBlockUnresolvedCrossParentRemainder_eq_zeroTargetParentLedger
    (R : ℕ) (hR : 3 ≤ R) :
    nnsOneBlockUnresolvedCrossParentRemainder R =
      -(∑ n ∈ nnsOneBlockOldTailCarrier R,
          postRootZeroTargetPairExcess (n, R)) -
        ∑ c ∈ Finset.Icc 1 (oldParentCutoff R),
          ((canonicalParentFiber R c).card : ℝ) *
            (∑ n ∈ nnsOneBlockOldTailCarrier R,
              postRootZeroTargetPairExcess (n, c)) +
        (realMoebiusStep R) ^ 2 +
        ∑ c ∈ nnsOneBlockMatchedParentSet R,
          ((canonicalParentFiber R c).card : ℝ) *
            (realMoebiusStep c) ^ 2 := by
  have hprefComplex :
      ((realCanonicalTotalIncrement R : ℝ) : ℂ) =
        (((canonicalPrefixPopulationMass R : ℤ) : ℝ) : ℂ) := by
    rw [realCanonicalTotalIncrement_cast,
      canonicalTotalIncrement_eq_prefixPopulationMass_cast R hR]
  have hprefReal :
      realCanonicalTotalIncrement R =
        ((canonicalPrefixPopulationMass R : ℤ) : ℝ) := by
    have h := congrArg Complex.re hprefComplex
    simpa using h
  have hparentInt :=
    canonicalPrefixPopulationMass_eq_sum_neg_mobius_mul_parentFiberCard R hR
  have hparentReal :=
    congrArg (fun z : ℤ => (z : ℝ)) hparentInt
  push_cast at hparentReal
  have hblock :
      realCanonicalTotalIncrement R =
        ∑ c ∈ Finset.Icc 1 (oldParentCutoff R),
          -realMoebiusStep c *
            ((canonicalParentFiber R c).card : ℝ) := by
    rw [hprefReal]
    simpa [realMoebiusStep] using hparentReal
  have htail :
      nnsOneBlockOldTailMass R =
        -(∑ n ∈ nnsOneBlockOldTailCarrier R, realMoebiusStep n) := by
    unfold nnsOneBlockOldTailMass nnsOneBlockOldTailEvent
    rw [Finset.sum_neg_distrib]
  have hneg :
      (∑ c ∈ Finset.Icc 1 (oldParentCutoff R),
        -realMoebiusStep c *
          ((canonicalParentFiber R c).card : ℝ)) =
        -(∑ c ∈ Finset.Icc 1 (oldParentCutoff R),
          ((canonicalParentFiber R c).card : ℝ) *
            realMoebiusStep c) := by
    calc
      (∑ c ∈ Finset.Icc 1 (oldParentCutoff R),
        -realMoebiusStep c *
          ((canonicalParentFiber R c).card : ℝ)) =
        ∑ c ∈ Finset.Icc 1 (oldParentCutoff R),
          -(((canonicalParentFiber R c).card : ℝ) *
            realMoebiusStep c) := by
              apply Finset.sum_congr rfl
              intro c _hc
              ring
      _ = -(∑ c ∈ Finset.Icc 1 (oldParentCutoff R),
          ((canonicalParentFiber R c).card : ℝ) *
            realMoebiusStep c) := by
              rw [Finset.sum_neg_distrib]
  have hupdate :
      nnsOneBlockUpdateMass R =
        realMoebiusStep R +
          ∑ c ∈ Finset.Icc 1 (oldParentCutoff R),
            ((canonicalParentFiber R c).card : ℝ) *
              realMoebiusStep c := by
    unfold nnsOneBlockUpdateMass nnsOneBlockRootUpdateEvent
    rw [hblock, hneg]
    ring
  have hroot :
      (∑ n ∈ nnsOneBlockOldTailCarrier R,
        postRootZeroTargetPairExcess (n, R)) =
        (∑ n ∈ nnsOneBlockOldTailCarrier R, realMoebiusStep n) *
          realMoebiusStep R := by
    simp_rw [postRootZeroTargetPairExcess_eq_weight]
    rw [Finset.sum_mul]
  have hparent : ∀ c : ℕ,
      (∑ n ∈ nnsOneBlockOldTailCarrier R,
        postRootZeroTargetPairExcess (n, c)) =
        (∑ n ∈ nnsOneBlockOldTailCarrier R, realMoebiusStep n) *
          realMoebiusStep c := by
    intro c
    simp_rw [postRootZeroTargetPairExcess_eq_weight]
    rw [Finset.sum_mul]
  have hparents :
      (∑ c ∈ Finset.Icc 1 (oldParentCutoff R),
        ((canonicalParentFiber R c).card : ℝ) *
          (∑ n ∈ nnsOneBlockOldTailCarrier R,
            postRootZeroTargetPairExcess (n, c))) =
        (∑ n ∈ nnsOneBlockOldTailCarrier R, realMoebiusStep n) *
          (∑ c ∈ Finset.Icc 1 (oldParentCutoff R),
            ((canonicalParentFiber R c).card : ℝ) *
              realMoebiusStep c) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _hc
    rw [hparent c]
    ring
  rw [nnsOneBlockUnresolvedCrossParentRemainder,
    nnsOneBlockCrossExcess_eq_tail_mul_update,
    htail, hupdate,
    nnsOneBlockIdentifiedDiagonalExcess_eq_neg_energy R hR,
    hroot, hparents]
  ring

theorem nnsOneBlockCrossExcess_eq_diagonal_add_unresolved
    (R : ℕ) :
    nnsOneBlockCrossExcess R =
      nnsOneBlockIdentifiedDiagonalExcess R +
        nnsOneBlockUnresolvedCrossParentRemainder R := by
  unfold nnsOneBlockUnresolvedCrossParentRemainder
  ring

private theorem abs_realMoebiusStep_le_one_nnsOneBlock (n : ℕ) :
    |realMoebiusStep n| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h]

/-- The literal root-plus-current-block update is elementary root scale. -/
theorem abs_nnsOneBlockUpdateMass_le_three_root
    (R : ℕ) (hR : 2 ≤ R) :
    |nnsOneBlockUpdateMass R| ≤ 3 * (R : ℝ) := by
  unfold nnsOneBlockUpdateMass nnsOneBlockRootUpdateEvent
  have hmu := abs_realMoebiusStep_le_one_nnsOneBlock R
  have hblock := abs_realCanonicalTotalIncrement_le R
  have htri :
      |realMoebiusStep R - realCanonicalTotalIncrement R| ≤
        |realMoebiusStep R| + |realCanonicalTotalIncrement R| :=
    abs_sub _ _
  have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hblock' :
      |realCanonicalTotalIncrement R| ≤ 2 * (R : ℝ) + 1 := by
    simpa [Nat.cast_add, Nat.cast_mul] using hblock
  linarith

/-- Hence the positive diagonal update energy in #877 costs only 9 R^2. -/
theorem norm_sq_oneBlockUpdate_le_nine_root_sq
    (R : ℕ) (hR : 2 ≤ R) :
    ‖canonicalMoebiusWeight R - canonicalTotalIncrement R‖ ^ 2 ≤
      9 * (R : ℝ) ^ 2 := by
  rw [← nnsOneBlockUpdateMass_cast_eq_update R,
    Complex.norm_real, Real.norm_eq_abs]
  have habs := abs_nnsOneBlockUpdateMass_le_three_root R hR
  have habs0 : 0 ≤ |nnsOneBlockUpdateMass R| := abs_nonneg _
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  nlinarith

/-- **The actual #877 cross term is exactly the NNS target-zero excess.** -/
theorem oneBlockCorrelationInner_eq_nnsCrossExcess
    (R : ℕ) (hR : 2 ≤ R) :
    RCLike.re
        (inner ℂ (squareRootCanonicalRoughCorrelation R)
          (canonicalMoebiusWeight R - canonicalTotalIncrement R)) =
      nnsOneBlockCrossExcess R := by
  rw [← nnsOneBlockOldTailMass_cast_eq_correlation R hR,
    ← nnsOneBlockUpdateMass_cast_eq_update R]
  rw [RCLike.inner_apply']
  change nnsOneBlockOldTailMass R * nnsOneBlockUpdateMass R =
    nnsOneBlockCrossExcess R
  exact (nnsOneBlockCrossExcess_eq_tail_mul_update R).symm

/-- **Exact #877 energy step after extracting the physical dissipative
diagonal.**  The only unsolved signed object is now the cross-parent remainder. -/
theorem squareRootCanonicalRoughCorrelation_energy_step_oneBlock_diagonal_remainder
    (R : ℕ) (hR : 3 ≤ R) :
    ‖squareRootCanonicalRoughCorrelation (R + 1)‖ ^ 2 -
        ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 =
      ‖canonicalMoebiusWeight R - canonicalTotalIncrement R‖ ^ 2 +
        2 * nnsOneBlockIdentifiedDiagonalExcess R +
        2 * nnsOneBlockUnresolvedCrossParentRemainder R := by
  rw [squareRootCanonicalRoughCorrelation_energy_step_oneBlock
      R (by omega),
    oneBlockCorrelationInner_eq_nnsCrossExcess R (by omega),
    nnsOneBlockCrossExcess_eq_diagonal_add_unresolved]
  ring

/-- **All non-RH-strength pieces removed.**  The negative identified diagonal
can be dropped and the current-block self energy costs at most 9 R^2.  Any
remaining positive energy growth is therefore carried by the unresolved
cross-parent NNS remainder. -/
theorem squareRootCanonicalRoughCorrelation_energy_step_le_unresolved
    (R : ℕ) (hR : 3 ≤ R) :
    ‖squareRootCanonicalRoughCorrelation (R + 1)‖ ^ 2 -
        ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 ≤
      9 * (R : ℝ) ^ 2 +
        2 * nnsOneBlockUnresolvedCrossParentRemainder R := by
  have hexact :=
    squareRootCanonicalRoughCorrelation_energy_step_oneBlock_diagonal_remainder
      R hR
  have hdiag := nnsOneBlockIdentifiedDiagonalExcess_nonpos R hR
  have hupd := norm_sq_oneBlockUpdate_le_nine_root_sq R (by omega)
  linarith


/-- **Normalized NNS form of the exact #877 one-block energy step.**

This is the target requested by the covariance-normalization attack: the only
off-diagonal term is the dimensionless target-zero NNS coefficient multiplied
by the total physical co/divergent pair mass. -/
theorem squareRootCanonicalRoughCorrelation_energy_step_oneBlock_nns
    (R : ℕ) (hR : 2 ≤ R) :
    ‖squareRootCanonicalRoughCorrelation (R + 1)‖ ^ 2 -
        ‖squareRootCanonicalRoughCorrelation R‖ ^ 2 =
      ‖canonicalMoebiusWeight R - canonicalTotalIncrement R‖ ^ 2 +
        2 * nnsOneBlockNormalizedCovariance R *
          nnsOneBlockTotalPairMass R := by
  rw [squareRootCanonicalRoughCorrelation_energy_step_oneBlock R hR,
    oneBlockCorrelationInner_eq_nnsCrossExcess R hR,
    ← nnsOneBlockNormalizedCovariance_mul_total R]
  ring

end RHLean.Proof
