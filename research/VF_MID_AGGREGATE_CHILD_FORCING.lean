import Mathlib
import «research.VF_MID_RECURSIVE_REMAINDER_BOUND»
import RHLean.Analysis.PartialMomentSchurTarget

/-!
# Aggregate-to-child forcing for the native VF recursive descent

PR #854 proves that recursive VF scale transport is well founded, but explicitly
does not prove that a large aggregate parent excursion selects a lower-scale
child. PR #855 supplies the exact signed child packets, their disjoint physical
partition, and the O(R) transfer remainder.

This file isolates the remaining logical/arithmetic seam without assuming it:

* keep the signed native child packets scalar until after reassembly;
* expose their full off-diagonal Gram term exactly;
* fold the #855 full descent remainder into one exact Gram remainder;
* prove the abstract aggregate-to-child forcing implication once a true energy
  budget is supplied;
* record separately the still-missing packet-to-full-scale inheritance step.

No independence, PNT-rate estimate, Li approximation, or RH input is used.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Squared scalar energy of the actual signed native child packets from #855. -/
def vfMidRecursiveNativeChildEnergy (R : ℕ) : ℝ :=
  ∑ S ∈ Finset.Ico 2 R,
    (vfMidRecursiveNativeChargeInBlock R S) ^ 2

/-- The exact off-diagonal scalar Gram term between distinct native child scales.

Disjoint physical child carriers do not make these scalar amplitudes
orthogonal. This is the cross term which must be controlled rather than
silently discarded. -/
def vfMidRecursiveNativeCrossGram (R : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 2 R,
    ∑ i ∈ Finset.Ico 2 j,
      vfMidRecursiveNativeChargeInBlock R i *
        vfMidRecursiveNativeChargeInBlock R j

/-- Same-sign zero-target pair product in the stable NNS arbitrary-target
partial-moment API. -/
def vfMidZeroTargetCoPartialPair (x y : ℝ) : ℝ :=
  partialLower x 0 * partialLower y 0 +
    partialUpper x 0 * partialUpper y 0

/-- Opposite-sign zero-target pair product in the same API. -/
def vfMidZeroTargetDivergentPair (x y : ℝ) : ℝ :=
  partialLower x 0 * partialUpper y 0 +
    partialUpper x 0 * partialLower y 0

/-- At target zero the NNS four-sector decomposition is exactly the raw scalar
cross product. -/
theorem vfMidZeroTargetCoPartial_sub_divergent_eq_mul (x y : ℝ) :
    vfMidZeroTargetCoPartialPair x y -
        vfMidZeroTargetDivergentPair x y = x * y := by
  have h := deviation_product_eq_partial_reassembly x y 0 0
  norm_num at h
  unfold vfMidZeroTargetCoPartialPair vfMidZeroTargetDivergentPair
  linarith

/-- Same-sign zero-target partial-moment mass on the exact off-diagonal
lower-scale pair carrier used by `vfMidRecursiveNativeCrossGram`.

At target zero no centering/rank-one correction is introduced: this is the
literal NNS co-partial sector on the native child packet amplitudes. -/
def vfMidRecursiveNativeZeroTargetCoPartialCross (R : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 2 R,
    ∑ i ∈ Finset.Ico 2 j,
      vfMidZeroTargetCoPartialPair
        (vfMidRecursiveNativeChargeInBlock R i)
        (vfMidRecursiveNativeChargeInBlock R j)

/-- Opposite-sign zero-target partial-moment mass on the same off-diagonal
lower-scale pair carrier. -/
def vfMidRecursiveNativeZeroTargetDivergentCross (R : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 2 R,
    ∑ i ∈ Finset.Ico 2 j,
      vfMidZeroTargetDivergentPair
        (vfMidRecursiveNativeChargeInBlock R i)
        (vfMidRecursiveNativeChargeInBlock R j)

/-- **NNS zero-target decomposition of the remaining off-diagonal VF Gram.**

The scalar cross Gram is exactly same-sign co-partial mass minus opposite-sign
divergent mass on the native lower-scale packets.  Thus target zero isolates
the sign-coherence problem without a mean-centering or rank-one correction. -/
theorem vfMidRecursiveNativeCrossGram_eq_zeroTargetCoPartial_sub_divergent
    (R : ℕ) :
    vfMidRecursiveNativeCrossGram R =
      vfMidRecursiveNativeZeroTargetCoPartialCross R -
        vfMidRecursiveNativeZeroTargetDivergentCross R := by
  unfold vfMidRecursiveNativeCrossGram
    vfMidRecursiveNativeZeroTargetCoPartialCross
    vfMidRecursiveNativeZeroTargetDivergentCross
  calc
    (∑ j ∈ Finset.Ico 2 R,
      ∑ i ∈ Finset.Ico 2 j,
        vfMidRecursiveNativeChargeInBlock R i *
          vfMidRecursiveNativeChargeInBlock R j) =
        ∑ j ∈ Finset.Ico 2 R,
          ∑ i ∈ Finset.Ico 2 j,
            (vfMidZeroTargetCoPartialPair
                (vfMidRecursiveNativeChargeInBlock R i)
                (vfMidRecursiveNativeChargeInBlock R j) -
              vfMidZeroTargetDivergentPair
                (vfMidRecursiveNativeChargeInBlock R i)
                (vfMidRecursiveNativeChargeInBlock R j)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro i _hi
      exact
        (vfMidZeroTargetCoPartial_sub_divergent_eq_mul
          (vfMidRecursiveNativeChargeInBlock R i)
          (vfMidRecursiveNativeChargeInBlock R j)).symm
    _ = ∑ j ∈ Finset.Ico 2 R,
          ((∑ i ∈ Finset.Ico 2 j,
              vfMidZeroTargetCoPartialPair
                (vfMidRecursiveNativeChargeInBlock R i)
                (vfMidRecursiveNativeChargeInBlock R j)) -
            ∑ i ∈ Finset.Ico 2 j,
              vfMidZeroTargetDivergentPair
                (vfMidRecursiveNativeChargeInBlock R i)
                (vfMidRecursiveNativeChargeInBlock R j)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_sub_distrib]
    _ = (∑ j ∈ Finset.Ico 2 R,
            ∑ i ∈ Finset.Ico 2 j,
              vfMidZeroTargetCoPartialPair
                (vfMidRecursiveNativeChargeInBlock R i)
                (vfMidRecursiveNativeChargeInBlock R j)) -
          ∑ j ∈ Finset.Ico 2 R,
            ∑ i ∈ Finset.Ico 2 j,
              vfMidZeroTargetDivergentPair
                (vfMidRecursiveNativeChargeInBlock R i)
                (vfMidRecursiveNativeChargeInBlock R j) := by
      rw [Finset.sum_sub_distrib]

/-- Scalar specialization of the finite signed Gram expansion on an interval. -/
private theorem sum_Ico_sq_eq_diagonal_add_two_cross
    (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ i ∈ Finset.Ico a b, f i) ^ 2 =
      (∑ i ∈ Finset.Ico a b, (f i) ^ 2) +
        2 * ∑ j ∈ Finset.Ico a b,
          ∑ i ∈ Finset.Ico a j, f i * f j := by
  induction b, hab using Nat.le_induction with
  | base =>
      simp
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab]
      rw [Finset.sum_Ico_succ_top hab]
      rw [Finset.sum_Ico_succ_top hab]
      rw [← Finset.sum_mul]
      nlinarith [ih]

/-- Exact native-child Gram identity.

The square of the signed aggregate is the diagonal child energy plus every
off-diagonal scalar cross term. #850/#855 disjointness is already built into
which seats belong to each packet; it does not remove this cross term. -/
theorem vfMidRecursiveAggregateNativeCharge_sq_eq_childEnergy_add_crossGram
    (R : ℕ) (hR : 2 ≤ R) :
    (vfMidRecursiveAggregateNativeCharge R) ^ 2 =
      vfMidRecursiveNativeChildEnergy R +
        2 * vfMidRecursiveNativeCrossGram R := by
  unfold vfMidRecursiveAggregateNativeCharge
    vfMidRecursiveNativeChildEnergy
    vfMidRecursiveNativeCrossGram
  exact
    sum_Ico_sq_eq_diagonal_add_two_cross
      (fun S => vfMidRecursiveNativeChargeInBlock R S) hR

/-- Zero-target NNS form of the aggregate native-child square.

The diagonal child energy is kept separate; every genuine off-diagonal pair is
then classified exactly as co-partial (same sign) or divergent (opposite sign).
This is the target-zero form suggested by the NNS covariance decomposition. -/
theorem vfMidRecursiveAggregateNativeCharge_sq_eq_childEnergy_add_zeroTargetCross
    (R : ℕ) (hR : 2 ≤ R) :
    (vfMidRecursiveAggregateNativeCharge R) ^ 2 =
      vfMidRecursiveNativeChildEnergy R +
        2 * (vfMidRecursiveNativeZeroTargetCoPartialCross R -
          vfMidRecursiveNativeZeroTargetDivergentCross R) := by
  rw [vfMidRecursiveAggregateNativeCharge_sq_eq_childEnergy_add_crossGram R hR]
  rw [vfMidRecursiveNativeCrossGram_eq_zeroTargetCoPartial_sub_divergent R]

/-- Full signed Gram/remainder correction between the #855 parent defect square
and the diagonal native-child energy.

The first term is genuine cross-scale scalar coherence. The last two terms
are the exact interaction with the already-reassembled #855 descent remainder;
no absolute value is taken before this identity. -/
def vfMidNativeDescentGramRemainder (R : ℕ) : ℝ :=
  2 * vfMidRecursiveNativeCrossGram R +
    2 * vfMidRecursiveAggregateNativeCharge R *
      vfMidNativeDescentRemainder R +
    (vfMidNativeDescentRemainder R) ^ 2

/-- Exact parent-square decomposition on the real signed packets.

This is the precise energy seam after #855:

G_R^2 = sum_S V_{R,S}^2 + GramRem_R.

Thus a Bessel/Gram contraction is exactly an upper bound for
vfMidNativeDescentGramRemainder; population disjointness alone is not such a
bound. -/
theorem vfMidOddCompositeTrackingDefect_sq_eq_childEnergy_add_gramRemainder
    (R : ℕ) (hR : 7 ≤ R) :
    (vfMidOddCompositeTrackingDefect R) ^ 2 =
      vfMidRecursiveNativeChildEnergy R +
        vfMidNativeDescentGramRemainder R := by
  have hdesc :=
    vfMidOddCompositeTrackingDefect_eq_nativeCharge_add_descentRemainder
      R hR
  have hgram :=
    vfMidRecursiveAggregateNativeCharge_sq_eq_childEnergy_add_crossGram
      R (by omega)
  rw [hdesc]
  calc
    (vfMidRecursiveAggregateNativeCharge R +
        vfMidNativeDescentRemainder R) ^ 2 =
      (vfMidRecursiveAggregateNativeCharge R) ^ 2 +
        2 * vfMidRecursiveAggregateNativeCharge R *
          vfMidNativeDescentRemainder R +
        (vfMidNativeDescentRemainder R) ^ 2 := by ring
    _ =
      (vfMidRecursiveNativeChildEnergy R +
          2 * vfMidRecursiveNativeCrossGram R) +
        2 * vfMidRecursiveAggregateNativeCharge R *
          vfMidNativeDescentRemainder R +
        (vfMidNativeDescentRemainder R) ^ 2 := by rw [hgram]
    _ =
      vfMidRecursiveNativeChildEnergy R +
        vfMidNativeDescentGramRemainder R := by
          unfold vfMidNativeDescentGramRemainder
          ring

/-- Abstract aggregate-to-child kill switch.

If the parent square is bounded by diagonal child energy plus an allowance, and
the sum of all child thresholds plus that allowance fits under the parent
threshold, then a supercritical parent forces a supercritical child packet.

This is the exact pigeonhole/Bessel implication needed before well-founded
descent can be used. -/
theorem supercriticalParent_forces_supercriticalChildPacket
    (I : Finset ℕ) (V threshold : ℕ → ℝ)
    (parentThreshold allowance parent : ℝ)
    (hbudget :
      (∑ i ∈ I, threshold i) + allowance ≤ parentThreshold)
    (henergy :
      parent ^ 2 ≤ (∑ i ∈ I, (V i) ^ 2) + allowance)
    (hsuper : parentThreshold < parent ^ 2) :
    ∃ i ∈ I, threshold i < (V i) ^ 2 := by
  by_contra hchild
  have hterm :
      ∀ i ∈ I, (V i) ^ 2 ≤ threshold i := by
    intro i hi
    exact le_of_not_gt (fun hgt => hchild ⟨i, hi, hgt⟩)
  have hsum :
      (∑ i ∈ I, (V i) ^ 2) ≤ ∑ i ∈ I, threshold i := by
    exact Finset.sum_le_sum hterm
  linarith

/-- The same forcing statement in the common K * B budget currency.

A positive remainder allowance must be paid by actual slack in the parent
budget; sum B_S ≤ B_R with equality is not by itself enough to absorb it. -/
theorem supercriticalParent_forces_supercriticalChildPacket_of_K_budget
    (I : Finset ℕ) (V B : ℕ → ℝ)
    (K parentBudget allowance parent : ℝ)
    (hK : 0 ≤ K)
    (hbudget :
      (∑ i ∈ I, B i) ≤ parentBudget)
    (hallowance :
      K * (∑ i ∈ I, B i) + allowance ≤ K * parentBudget)
    (henergy :
      parent ^ 2 ≤ (∑ i ∈ I, (V i) ^ 2) + allowance)
    (hsuper : K * parentBudget < parent ^ 2) :
    ∃ i ∈ I, K * B i < (V i) ^ 2 := by
  have _hscaled :
      K * (∑ i ∈ I, B i) ≤ K * parentBudget :=
    mul_le_mul_of_nonneg_left hbudget hK
  apply
    supercriticalParent_forces_supercriticalChildPacket
      I V (fun i => K * B i)
      (K * parentBudget) allowance parent
  · rw [← Finset.mul_sum]
    exact hallowance
  · exact henergy
  · exact hsuper

/-- #855 instantiated into the abstract kill switch.

Once the exact signed Gram remainder is bounded by allowance, any parent
threshold which dominates the summed child thresholds plus that allowance
forces one actual native child packet above its threshold. -/
theorem vfMidSupercriticalParent_forces_nativeChildPacket
    (R : ℕ) (hR : 7 ≤ R)
    (threshold : ℕ → ℝ) (parentThreshold allowance : ℝ)
    (hgram :
      vfMidNativeDescentGramRemainder R ≤ allowance)
    (hbudget :
      (∑ S ∈ Finset.Ico 2 R, threshold S) + allowance ≤
        parentThreshold)
    (hsuper :
      parentThreshold < (vfMidOddCompositeTrackingDefect R) ^ 2) :
    ∃ S ∈ Finset.Ico 2 R,
      threshold S <
        (vfMidRecursiveNativeChargeInBlock R S) ^ 2 := by
  have hexact :=
    vfMidOddCompositeTrackingDefect_sq_eq_childEnergy_add_gramRemainder
      R hR
  have henergy :
      (vfMidOddCompositeTrackingDefect R) ^ 2 ≤
        (∑ S ∈ Finset.Ico 2 R,
          (vfMidRecursiveNativeChargeInBlock R S) ^ 2) +
        allowance := by
    unfold vfMidRecursiveNativeChildEnergy at hexact
    linarith
  exact
    supercriticalParent_forces_supercriticalChildPacket
      (Finset.Ico 2 R)
      (fun S => vfMidRecursiveNativeChargeInBlock R S)
      threshold parentThreshold allowance
      (vfMidOddCompositeTrackingDefect R)
      hbudget henergy hsuper

/-- The second inheritance seam must be stated separately: a large subset
packet V_{R,S} is not definitionally the full signed block discrepancy G_S.

This proposition is deliberately not asserted as a theorem. It names exactly
the additional arithmetic statement needed to turn packet selection into a
well-founded scale contradiction. -/
def VFMidNativePacketToScaleInheritanceStatement
    (threshold : ℕ → ℝ) : Prop :=
  ∀ R S : ℕ, 7 ≤ R → S ∈ Finset.Ico 2 R →
    threshold S <
        (vfMidRecursiveNativeChargeInBlock R S) ^ 2 →
      threshold S < (vfMidOddCompositeTrackingDefect S) ^ 2

/-- Conditional complete descent logic.

Given:
1. an upper bound for the exact signed Gram remainder;
2. enough threshold-budget slack to absorb that allowance;
3. packet-to-full-scale inheritance; and
4. the finite base range,

no supercritical scale can exist. The only unproved content in this theorem is
present explicitly as hypotheses; the descent contradiction itself is now
kernel-checkable. -/
theorem vfMidNoSupercriticalScale_of_aggregateChildForcing
    (threshold allowance : ℕ → ℝ)
    (hsmall :
      ∀ R : ℕ, R < 7 →
        (vfMidOddCompositeTrackingDefect R) ^ 2 ≤ threshold R)
    (hgram :
      ∀ R : ℕ, 7 ≤ R →
        vfMidNativeDescentGramRemainder R ≤ allowance R)
    (hbudget :
      ∀ R : ℕ, 7 ≤ R →
        (∑ S ∈ Finset.Ico 2 R, threshold S) + allowance R ≤
          threshold R)
    (hinherit :
      VFMidNativePacketToScaleInheritanceStatement threshold) :
    ∀ R : ℕ,
      (vfMidOddCompositeTrackingDefect R) ^ 2 ≤ threshold R := by
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
      by_cases hR7 : R < 7
      · exact hsmall R hR7
      · have hR : 7 ≤ R := by omega
        by_contra hsuperNot
        have hsuper :
            threshold R < (vfMidOddCompositeTrackingDefect R) ^ 2 :=
          lt_of_not_ge hsuperNot
        obtain ⟨S, hS, hpacket⟩ :=
          vfMidSupercriticalParent_forces_nativeChildPacket
            R hR threshold (threshold R) (allowance R)
            (hgram R hR) (hbudget R hR) hsuper
        have hSlt : S < R := (Finset.mem_Ico.mp hS).2
        have hscale :
            threshold S < (vfMidOddCompositeTrackingDefect S) ^ 2 :=
          hinherit R S hR hS hpacket
        have hih := ih S hSlt
        linarith

end RHLean.Analysis
