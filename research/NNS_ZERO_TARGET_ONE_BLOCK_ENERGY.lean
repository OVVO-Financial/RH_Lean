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
  simp only [map_real, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  exact (nnsOneBlockCrossExcess_eq_tail_mul_update R).symm

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
