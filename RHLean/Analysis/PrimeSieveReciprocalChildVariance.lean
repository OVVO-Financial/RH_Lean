import Mathlib
import RHLean.Analysis.PrimeSieveBaseEightShallowAttack

/-!
# Reciprocal child-interval variance route for the base-eight shallow packet

PR #331 identifies the remaining base-eight shallow packet with a finite
low-frequency square function of signed reciprocal prime-minus-Li sibling
contrasts.  This module removes one more layer of cancellation from the analytic
input.

For a midpoint node `[a,b)` with split `m`, write

`L = sum_[a,m) Delta_d`, `R = sum_[m,b) Delta_d`.

The signed packet residual is

`((b-a)^-1) * ((m-a) R - (b-m) L)`.

Its node energy is dominated, completely deterministically, by twice the
sign-blind child interval variance

`(b-a) * (||L||^2 + ||R||^2)`.

The same estimate iterates down the midpoint tree.  Hence a critical bound for
the sign-blind reciprocal child-interval variance square function implies the
entire successor-shallow packet estimate needed by #330 and #331.  The child
masses also telescope exactly to differences of the clipped classical
prime discrepancy `pi - Li`, so this is a genuine local prime-variance target,
not a reformulation involving the packet residual itself.

No prime-variance estimate is asserted unconditionally here.  The contribution
of this module is the exact deterministic reduction from that classical local
variance coordinate to the complete low-frequency packet square function.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-! ## One-node sign-blind variance -/

/-- Sign-blind squared mass of the two reciprocal-discrepancy children of one
midpoint node, weighted by the parent width. -/
def primeSieveReciprocalChildIntervalVariance
    (y x a m b : ℕ) : ℝ :=
  ((b - a : ℕ) : ℝ) *
    (‖∑ d ∈ Finset.Ico a m,
        primeSieveReciprocalPrimeDiscrepancy y x d‖ ^ 2 +
      ‖∑ d ∈ Finset.Ico m b,
        primeSieveReciprocalPrimeDiscrepancy y x d‖ ^ 2)

private theorem normalizedWeightedSibling_norm_le
    {l r w : ℕ} (hw : w = l + r) (hwpos : 0 < w) (u v : ℂ) :
    ‖(((w : ℕ) : ℂ)⁻¹ *
        ((((l : ℕ) : ℂ) * u) - (((r : ℕ) : ℂ) * v)))‖ ≤
      ‖u‖ + ‖v‖ := by
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hwpos
  have hlwNat : l ≤ w := by omega
  have hrwNat : r ≤ w := by omega
  have hlw : (l : ℝ) ≤ (w : ℝ) := by exact_mod_cast hlwNat
  have hrw : (r : ℝ) ≤ (w : ℝ) := by exact_mod_cast hrwNat
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
  have hsum :
      (l : ℝ) * ‖u‖ + (r : ℝ) * ‖v‖ ≤
        (w : ℝ) * (‖u‖ + ‖v‖) := by
    have hlu := mul_le_mul_of_nonneg_right hlw hu0
    have hrv := mul_le_mul_of_nonneg_right hrw hv0
    nlinarith
  calc
    ‖(((w : ℕ) : ℂ)⁻¹ *
        ((((l : ℕ) : ℂ) * u) - (((r : ℕ) : ℂ) * v)))‖ =
        ((w : ℝ)⁻¹) *
          ‖((((l : ℕ) : ℂ) * u) - (((r : ℕ) : ℂ) * v))‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ ((w : ℝ)⁻¹) *
        (‖(((l : ℕ) : ℂ) * u)‖ + ‖(((r : ℕ) : ℂ) * v)‖) := by
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ = ((w : ℝ)⁻¹) *
        ((l : ℝ) * ‖u‖ + (r : ℝ) * ‖v‖) := by
      simp
    _ ≤ ((w : ℝ)⁻¹) *
        ((w : ℝ) * (‖u‖ + ‖v‖)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖u‖ + ‖v‖ := by
      field_simp [ne_of_gt hwR]

private theorem norm_add_sq_le_two_sq_sum (u v : ℂ) :
    (‖u‖ + ‖v‖) ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- One signed sibling node is controlled by twice the sign-blind variance of
its two child interval discrepancy masses. -/
theorem primeSieveSignedSiblingNodeEnergy_le_two_childIntervalVariance
    {y x a m b : ℕ}
    (ha : 1 ≤ a) (ham : a ≤ m) (hmb : m ≤ b) (hab : a < b)
    (hb : b ≤ x / (y + 1) + 1) :
    ((b - a : ℕ) : ℝ) *
        ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ^ 2 ≤
      2 * primeSieveReciprocalChildIntervalVariance y x a m b := by
  let L : ℂ :=
    ∑ d ∈ Finset.Ico a m, primeSieveReciprocalPrimeDiscrepancy y x d
  let R : ℂ :=
    ∑ d ∈ Finset.Ico m b, primeSieveReciprocalPrimeDiscrepancy y x d
  have hwidth : b - a = (m - a) + (b - m) := by omega
  have hwidthPos : 0 < b - a := Nat.sub_pos_of_lt hab
  have hres :
      ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ≤ ‖R‖ + ‖L‖ := by
    rw [primeSieveSignedSiblingPacketResidual_eq_reciprocalSiblingContrast
      ha ham hmb hb]
    unfold primeSieveReciprocalSiblingContrast
    simpa [L, R] using
      (normalizedWeightedSibling_norm_le
        (l := m - a) (r := b - m) (w := b - a)
        hwidth hwidthPos R L)
  have hsq :
      ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ^ 2 ≤
        2 * (‖L‖ ^ 2 + ‖R‖ ^ 2) := by
    have hnonneg :
        0 ≤ ‖primeSieveSignedSiblingPacketResidual y x a m b‖ := norm_nonneg _
    have hsum0 : 0 ≤ ‖R‖ + ‖L‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq0 :
        ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ^ 2 ≤
          (‖R‖ + ‖L‖) ^ 2 := by
      nlinarith
    have htwo := norm_add_sq_le_two_sq_sum R L
    nlinarith
  have hwidth0 : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := by positivity
  unfold primeSieveReciprocalChildIntervalVariance
  dsimp [L, R] at hsq ⊢
  calc
    ((b - a : ℕ) : ℝ) *
        ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ^ 2 ≤
      ((b - a : ℕ) : ℝ) *
        (2 *
          (‖∑ d ∈ Finset.Ico a m,
              primeSieveReciprocalPrimeDiscrepancy y x d‖ ^ 2 +
            ‖∑ d ∈ Finset.Ico m b,
              primeSieveReciprocalPrimeDiscrepancy y x d‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hsq hwidth0
    _ = 2 *
        (((b - a : ℕ) : ℝ) *
          (‖∑ d ∈ Finset.Ico a m,
              primeSieveReciprocalPrimeDiscrepancy y x d‖ ^ 2 +
            ‖∑ d ∈ Finset.Ico m b,
              primeSieveReciprocalPrimeDiscrepancy y x d‖ ^ 2)) := by ring

/-- The sign-blind child variance is exactly a pair of squared increments of
the clipped classical discrepancy `pi - Li`. -/
theorem primeSieveReciprocalChildIntervalVariance_eq_clippedDiscrepancyDrops
    {y x a m b : ℕ}
    (ha : 1 ≤ a) (ham : a ≤ m) (hmb : m ≤ b)
    (hb : b ≤ x / (y + 1) + 1) :
    primeSieveReciprocalChildIntervalVariance y x a m b =
      ((b - a : ℕ) : ℝ) *
        (‖primeSieveDyadicClippedDiscrepancy y x a -
            primeSieveDyadicClippedDiscrepancy y x m‖ ^ 2 +
          ‖primeSieveDyadicClippedDiscrepancy y x m -
            primeSieveDyadicClippedDiscrepancy y x b‖ ^ 2) := by
  have hm1 : 1 ≤ m := ha.trans ham
  unfold primeSieveReciprocalChildIntervalVariance
  rw [sum_primeSieveReciprocalPrimeDiscrepancy_Ico_eq
      (y := y) (x := x) ha ham (hmb.trans hb),
    sum_primeSieveReciprocalPrimeDiscrepancy_Ico_eq
      (y := y) (x := x) hm1 hmb hb]

/-! ## Recursive sign-blind variance tree -/

/-- Recursive sign-blind child-interval variance over the same midpoint tree as
the shallow signed packet. -/
def primeSieveReciprocalLowFrequencyChildIntervalVariance
    (y x : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0, _a, _b => 0
  | depth + 1, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        primeSieveReciprocalChildIntervalVariance y x a m b +
          primeSieveReciprocalLowFrequencyChildIntervalVariance y x depth a m +
          primeSieveReciprocalLowFrequencyChildIntervalVariance y x depth m b
      else 0

/-- The recursive sign-blind variance is nonnegative. -/
theorem primeSieveReciprocalLowFrequencyChildIntervalVariance_nonneg
    (y x depth a b : ℕ) :
    0 ≤ primeSieveReciprocalLowFrequencyChildIntervalVariance y x depth a b := by
  induction depth generalizing a b with
  | zero => simp [primeSieveReciprocalLowFrequencyChildIntervalVariance]
  | succ depth ih =>
      by_cases hsplit : a + 1 < b
      · simp only [primeSieveReciprocalLowFrequencyChildIntervalVariance,
          hsplit, if_true]
        have hnode :
            0 ≤ primeSieveReciprocalChildIntervalVariance y x a
              (dyadicPacketMidpoint a b) b := by
          unfold primeSieveReciprocalChildIntervalVariance
          positivity
        exact add_nonneg (add_nonneg hnode (ih a (dyadicPacketMidpoint a b)))
          (ih (dyadicPacketMidpoint a b) b)
      · simp [primeSieveReciprocalLowFrequencyChildIntervalVariance, hsplit]

/-- Deterministic recursive domination: the entire signed midpoint packet tree
through a fixed depth is bounded by twice the sign-blind child-interval variance
tree. -/
theorem primeSieveDyadicPacketIntervalTreeEnergy_le_two_childIntervalVariance
    (y x depth a b : ℕ)
    (ha : 1 ≤ a)
    (hb : b ≤ x / (y + 1) + 1) :
    primeSieveDyadicPacketIntervalTreeEnergy y x depth a b ≤
      2 * primeSieveReciprocalLowFrequencyChildIntervalVariance
        y x depth a b := by
  induction depth generalizing a b with
  | zero =>
      simp [primeSieveDyadicPacketIntervalTreeEnergy_zero,
        primeSieveReciprocalLowFrequencyChildIntervalVariance]
  | succ depth ih =>
      rw [primeSieveDyadicPacketIntervalTreeEnergy_succ]
      by_cases hsplit : a + 1 < b
      · let m := dyadicPacketMidpoint a b
        have hm : a < m ∧ m < b := by
          dsimp [m, dyadicPacketMidpoint]
          omega
        have hm1 : 1 ≤ m := ha.trans hm.1.le
        have hmB : m ≤ x / (y + 1) + 1 := hm.2.le.trans hb
        have hab : a < b := hm.1.trans hm.2
        have hnode :=
          primeSieveSignedSiblingNodeEnergy_le_two_childIntervalVariance
            (y := y) (x := x) (a := a) (m := m) (b := b)
            ha hm.1.le hm.2.le hab hb
        have hleft := ih a m ha hmB
        have hright := ih m b hm1 hb
        simp only [primeSieveReciprocalLowFrequencyChildIntervalVariance,
          hsplit, if_true, m]
        calc
          ((b - a : ℕ) : ℝ) *
                ‖primeSieveSignedSiblingPacketResidual y x a m b‖ ^ 2 +
              primeSieveDyadicPacketIntervalTreeEnergy y x depth a m +
              primeSieveDyadicPacketIntervalTreeEnergy y x depth m b ≤
            2 * primeSieveReciprocalChildIntervalVariance y x a m b +
              2 * primeSieveReciprocalLowFrequencyChildIntervalVariance
                y x depth a m +
              2 * primeSieveReciprocalLowFrequencyChildIntervalVariance
                y x depth m b := by
            linarith
          _ = 2 *
              (primeSieveReciprocalChildIntervalVariance y x a m b +
                primeSieveReciprocalLowFrequencyChildIntervalVariance
                  y x depth a m +
                primeSieveReciprocalLowFrequencyChildIntervalVariance
                  y x depth m b) := by ring
      · simp [primeSieveReciprocalLowFrequencyChildIntervalVariance, hsplit]

/-- Global sign-blind child-interval variance square function through depth `J`
on every occupied reciprocal dyadic block. -/
def primeSieveReciprocalLowFrequencyChildIntervalVarianceSquareFunction
    (y x J : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    primeSieveReciprocalLowFrequencyChildIntervalVariance y x (min J j)
      (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1)

/-- Global deterministic domination of the signed low-frequency square
function by the sign-blind child-interval variance square function. -/
theorem primeSieveReciprocalLowFrequencySquareFunction_le_two_childIntervalVariance
    (y x J : ℕ) :
    primeSieveReciprocalLowFrequencySquareFunction y x J ≤
      2 * primeSieveReciprocalLowFrequencyChildIntervalVarianceSquareFunction
        y x J := by
  unfold primeSieveReciprocalLowFrequencySquareFunction
    primeSieveReciprocalLowFrequencyChildIntervalVarianceSquareFunction
  calc
    (∑ j ∈ primeSieveDyadicBlockIndices y x,
        primeSieveReciprocalLowFrequencyIntervalEnergy y x (min J j)
          (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight y x j + 1)) ≤
      ∑ j ∈ primeSieveDyadicBlockIndices y x,
        2 * primeSieveReciprocalLowFrequencyChildIntervalVariance y x (min J j)
          (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight y x j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hleft1 : 1 ≤ primeSieveDyadicBlockLeft j := by
        simpa [primeSieveDyadicBlockLeft] using (Nat.one_le_pow' j 1)
      have hright :
          primeSieveDyadicBlockRight y x j + 1 ≤ x / (y + 1) + 1 := by
        unfold primeSieveDyadicBlockRight
        exact Nat.add_le_add_right
          (min_le_left (x / (y + 1)) (2 ^ (j + 1) - 1)) 1
      have htree :=
        primeSieveDyadicPacketIntervalTreeEnergy_le_two_childIntervalVariance
          y x (min J j) (primeSieveDyadicBlockLeft j)
            (primeSieveDyadicBlockRight y x j + 1) hleft1 hright
      rw [primeSieveDyadicPacketIntervalTreeEnergy_eq_reciprocalLowFrequencyIntervalEnergy
        y x (min J j) (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight y x j + 1) hleft1 hright] at htree
      exact htree
    _ = 2 *
      (∑ j ∈ primeSieveDyadicBlockIndices y x,
        primeSieveReciprocalLowFrequencyChildIntervalVariance y x (min J j)
          (primeSieveDyadicBlockLeft j)
          (primeSieveDyadicBlockRight y x j + 1)) := by
      rw [Finset.mul_sum]

/-! ## Root and base-eight analytic routes -/

/-- Sign-blind child-interval variance at the root sibling layer. -/
def primeSieveReciprocalRootChildIntervalVariance (y x : ℕ) : ℝ :=
  primeSieveReciprocalLowFrequencyChildIntervalVarianceSquareFunction y x 1

/-- The level-zero sibling obstruction isolated in #331 is deterministically
controlled by the corresponding sign-blind child-interval variance. -/
theorem primeSieveReciprocalRootSiblingSquareFunction_le_two_childIntervalVariance
    (y x : ℕ) :
    primeSieveReciprocalRootSiblingSquareFunction y x ≤
      2 * primeSieveReciprocalRootChildIntervalVariance y x := by
  simpa [primeSieveReciprocalRootSiblingSquareFunction,
    primeSieveReciprocalRootChildIntervalVariance] using
    primeSieveReciprocalLowFrequencySquareFunction_le_two_childIntervalVariance
      y x 1

/-- Base-eight successor sign-blind child-interval variance. -/
def primeSieveBaseEightChildIntervalVarianceSquareFunction
    (k x : ℕ) : ℝ :=
  primeSieveReciprocalLowFrequencyChildIntervalVarianceSquareFunction
    (primorialPNTPrimeSieveCutoff k) x
    (dyadicPacketBaseEightCutoff k x + 1)

/-- The complete base-eight signed shallow square function is controlled by the
base-eight sign-blind child-interval variance square function. -/
theorem primeSieveBaseEightShallowSquareFunction_le_two_childIntervalVariance
    (k x : ℕ) :
    primeSieveBaseEightShallowSquareFunction k x ≤
      2 * primeSieveBaseEightChildIntervalVarianceSquareFunction k x := by
  simpa [primeSieveBaseEightShallowSquareFunction,
    primeSieveBaseEightChildIntervalVarianceSquareFunction] using
    primeSieveReciprocalLowFrequencySquareFunction_le_two_childIntervalVariance
      (primorialPNTPrimeSieveCutoff k) x
      (dyadicPacketBaseEightCutoff k x + 1)

/-- Critical root-level sign-blind reciprocal prime-variance premise. -/
def DyadicPrimeReciprocalRootChildIntervalVarianceBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveReciprocalRootChildIntervalVariance
            (primorialPNTPrimeSieveCutoff k) x ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- A root child-interval variance estimate resolves the first necessary
low-frequency obstruction isolated by #331. -/
theorem dyadicPrimeReciprocalRootChildIntervalVarianceBlockBounded_implies_rootSibling
    (h : DyadicPrimeReciprocalRootChildIntervalVarianceBlockBoundedStatement) :
    DyadicPrimeReciprocalRootSiblingBlockBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hCb⟩ := h ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro k x hk hlow hup
  have hvar := hCb k x hk hlow hup
  have hdom :=
    primeSieveReciprocalRootSiblingSquareFunction_le_two_childIntervalVariance
      (primorialPNTPrimeSieveCutoff k) x
  calc
    primeSieveReciprocalRootSiblingSquareFunction
        (primorialPNTPrimeSieveCutoff k) x ≤
      2 * primeSieveReciprocalRootChildIntervalVariance
        (primorialPNTPrimeSieveCutoff k) x := hdom
    _ ≤ 2 * (C * Real.rpow ((x : ℝ) + 1) (1 + ε)) :=
      mul_le_mul_of_nonneg_left hvar (by norm_num)
    _ = (2 * C) * Real.rpow ((x : ℝ) + 1) (1 + ε) := by ring

/-- Critical all-level sign-blind reciprocal prime-variance premise.  Unlike the
signed shallow statement, it asks only for squared masses of the two child
prime-minus-Li intervals at each low-frequency midpoint node. -/
def DyadicPrimeReciprocalLowFrequencyChildIntervalVarianceBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveBaseEightChildIntervalVarianceSquareFunction k x ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- The sign-blind child-interval variance premise implies the exact signed
low-frequency square-function premise of #331. -/
theorem dyadicPrimeReciprocalChildIntervalVarianceBlockBounded_implies_lowFrequency
    (h : DyadicPrimeReciprocalLowFrequencyChildIntervalVarianceBlockBoundedStatement) :
    DyadicPrimeReciprocalLowFrequencySquareFunctionBlockBoundedStatement := by
  intro ε hε
  obtain ⟨C, hC, hCb⟩ := h ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro k x hk hlow hup
  have hvar := hCb k x hk hlow hup
  have hdom :=
    primeSieveBaseEightShallowSquareFunction_le_two_childIntervalVariance k x
  calc
    primeSieveBaseEightShallowSquareFunction k x ≤
      2 * primeSieveBaseEightChildIntervalVarianceSquareFunction k x := hdom
    _ ≤ 2 * (C * Real.rpow ((x : ℝ) + 1) (1 + ε)) :=
      mul_le_mul_of_nonneg_left hvar (by norm_num)
    _ = (2 * C) * Real.rpow ((x : ℝ) + 1) (1 + ε) := by ring

/-- RH package with the packet-side shallow input replaced by a sign-blind local
prime-variance estimate on the reciprocal midpoint tree. -/
theorem riemannHypothesis_of_baseEightReciprocalChildIntervalVariancePackage
    (hC : DyadicCoherentChannelRHScale)
    (hV : DyadicPrimeReciprocalLowFrequencyChildIntervalVarianceBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement := by
  apply riemannHypothesis_of_baseEightReciprocalLowFrequencyPackage hC
  · exact dyadicPrimeReciprocalChildIntervalVarianceBlockBounded_implies_lowFrequency hV
  · exact hD

end RHLean.Analysis
