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
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
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
