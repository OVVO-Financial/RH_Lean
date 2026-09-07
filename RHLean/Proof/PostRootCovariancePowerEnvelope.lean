import Mathlib
import RHLean.Proof.EndpointCubeAnalyticClosure
import RHLean.Proof.PostRootCovarianceLcmInteriorPacking

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

/-- The nonnegative normalized seat value for the signed post-root remainder.
Seats below the protected bootstrap onset `W = 2` are set to zero. -/
def postRootCovariancePowerSeat (ε : ℝ) (W : ℕ) : ℝ :=
  if 2 ≤ W then
    max 0
      (postRootCovarianceRemainder W /
        Real.rpow (W : ℝ) (1 + ε))
  else 0

/-- The running finite-horizon envelope of normalized signed remainders.
This is the explicit tether for the power-remainder seam: it is finite at every
horizon, monotone in the horizon, and contains every earlier normalized seat. -/
def postRootCovariancePowerEnvelope (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | N + 1 =>
      max (postRootCovariancePowerEnvelope ε N)
        (postRootCovariancePowerSeat ε (N + 1))

theorem postRootCovariancePowerSeat_nonneg (ε : ℝ) (W : ℕ) :
    0 ≤ postRootCovariancePowerSeat ε W := by
  unfold postRootCovariancePowerSeat
  by_cases hW : 2 ≤ W
  · rw [if_pos hW]
    exact le_max_left _ _
  · rw [if_neg hW]

theorem postRootCovariancePowerEnvelope_nonneg (ε : ℝ) (N : ℕ) :
    0 ≤ postRootCovariancePowerEnvelope ε N := by
  induction N with
  | zero => simp [postRootCovariancePowerEnvelope]
  | succ N ih =>
      rw [postRootCovariancePowerEnvelope]
      exact ih.trans (le_max_left _ _)

theorem postRootCovariancePowerEnvelope_le_succ (ε : ℝ) (N : ℕ) :
    postRootCovariancePowerEnvelope ε N ≤
      postRootCovariancePowerEnvelope ε (N + 1) := by
  rw [postRootCovariancePowerEnvelope]
  exact le_max_left _ _

theorem postRootCovariancePowerEnvelope_mono
    (ε : ℝ) {N M : ℕ} (hNM : N ≤ M) :
    postRootCovariancePowerEnvelope ε N ≤
      postRootCovariancePowerEnvelope ε M := by
  induction M, hNM using Nat.le_induction with
  | base => exact le_rfl
  | succ M hNM ih =>
      exact ih.trans (postRootCovariancePowerEnvelope_le_succ ε M)

theorem postRootCovariancePowerSeat_le_selfEnvelope
    (ε : ℝ) (W : ℕ) :
    postRootCovariancePowerSeat ε W ≤
      postRootCovariancePowerEnvelope ε W := by
  cases W with
  | zero => simp [postRootCovariancePowerSeat, postRootCovariancePowerEnvelope]
  | succ N =>
      rw [postRootCovariancePowerEnvelope]
      exact le_max_right _ _

theorem postRootCovariancePowerSeat_le_envelope
    (ε : ℝ) {W N : ℕ} (hWN : W ≤ N) :
    postRootCovariancePowerSeat ε W ≤
      postRootCovariancePowerEnvelope ε N :=
  (postRootCovariancePowerSeat_le_selfEnvelope ε W).trans
    (postRootCovariancePowerEnvelope_mono ε hWN)

/-- The positive amount by which the next normalized remainder seat sets a new
record above the previous finite-horizon envelope.  Non-record seats cost zero. -/
def postRootCovariancePowerRecordExcess (ε : ℝ) (N : ℕ) : ℝ :=
  max 0
    (postRootCovariancePowerSeat ε (N + 1) -
      postRootCovariancePowerEnvelope ε N)

theorem postRootCovariancePowerRecordExcess_nonneg (ε : ℝ) (N : ℕ) :
    0 ≤ postRootCovariancePowerRecordExcess ε N := by
  unfold postRootCovariancePowerRecordExcess
  exact le_max_left _ _

/-- The running envelope advances by exactly the positive new-record excess. -/
theorem postRootCovariancePowerEnvelope_succ_eq_add_recordExcess
    (ε : ℝ) (N : ℕ) :
    postRootCovariancePowerEnvelope ε (N + 1) =
      postRootCovariancePowerEnvelope ε N +
        postRootCovariancePowerRecordExcess ε N := by
  rw [postRootCovariancePowerEnvelope]
  unfold postRootCovariancePowerRecordExcess
  by_cases h :
      postRootCovariancePowerSeat ε (N + 1) ≤
        postRootCovariancePowerEnvelope ε N
  · have hdiff :
        postRootCovariancePowerSeat ε (N + 1) -
            postRootCovariancePowerEnvelope ε N ≤ 0 :=
      sub_nonpos.mpr h
    rw [max_eq_left h, max_eq_left hdiff]
    ring
  · have hlt :
        postRootCovariancePowerEnvelope ε N <
          postRootCovariancePowerSeat ε (N + 1) :=
      lt_of_not_ge h
    have hrev :
        postRootCovariancePowerEnvelope ε N ≤
          postRootCovariancePowerSeat ε (N + 1) := hlt.le
    have hdiff :
        0 ≤ postRootCovariancePowerSeat ε (N + 1) -
          postRootCovariancePowerEnvelope ε N :=
      sub_nonneg.mpr hrev
    rw [max_eq_right hrev, max_eq_right hdiff]
    ring

/-- **Record-excess telescope.**  The whole finite-horizon envelope is exactly
the cumulative mass of its positive record-breaking increments.  This is the
string to tighten: local sequential inequalities only need to control new
records, not re-bound every old seat. -/
theorem postRootCovariancePowerEnvelope_eq_sum_recordExcess
    (ε : ℝ) (N : ℕ) :
    postRootCovariancePowerEnvelope ε N =
      ∑ j ∈ Finset.range N, postRootCovariancePowerRecordExcess ε j := by
  induction N with
  | zero => simp [postRootCovariancePowerEnvelope]
  | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      simpa only [Nat.succ_eq_add_one] using
        postRootCovariancePowerEnvelope_succ_eq_add_recordExcess ε N

/-- **Anchored tail form of the tether.**  Any verified finite prefix can be
frozen permanently; only the record excesses after the anchor remain to be
tightened. -/
theorem postRootCovariancePowerEnvelope_eq_anchor_add_tailRecordExcess
    (ε : ℝ) {A N : ℕ} (hAN : A ≤ N) :
    postRootCovariancePowerEnvelope ε N =
      postRootCovariancePowerEnvelope ε A +
        ∑ j ∈ Finset.Ico A N, postRootCovariancePowerRecordExcess ε j := by
  induction N, hAN using Nat.le_induction with
  | base => simp
  | succ N hAN ih =>
      rw [postRootCovariancePowerEnvelope_succ_eq_add_recordExcess, ih,
        Finset.sum_Ico_succ_top hAN]
      ring

/-- Any summable finite majorant for the record excesses bounds the running
envelope.  This is the plug-in interface for later Euler, LCM-wall, covariance,
or square-wheel inequalities. -/
theorem postRootCovariancePowerEnvelope_le_of_recordExcess_majorant
    (ε : ℝ) (g : ℕ → ℝ) {D : ℝ}
    (hexcess : ∀ j : ℕ, postRootCovariancePowerRecordExcess ε j ≤ g j)
    (hpartial : ∀ N : ℕ, (∑ j ∈ Finset.range N, g j) ≤ D) :
    ∀ N : ℕ, postRootCovariancePowerEnvelope ε N ≤ D := by
  intro N
  rw [postRootCovariancePowerEnvelope_eq_sum_recordExcess]
  calc
    (∑ j ∈ Finset.range N, postRootCovariancePowerRecordExcess ε j) ≤
        ∑ j ∈ Finset.range N, g j :=
      Finset.sum_le_sum fun j _hj => hexcess j
    _ ≤ D := hpartial N

/-- Every real Möbius pair weight is at most one. -/
private theorem realMoebiusPairWeight_le_one (m n : ℕ) :
    realMoebiusStep m * realMoebiusStep n ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or m with hm | hm | hm <;>
    rcases ArithmeticFunction.moebius_eq_or n with hn | hn | hn <;>
      simp [realMoebiusStep, hm, hn]

/-- The exact physical remainder carrier is contained in the full endpoint
square. -/
private theorem postRootCovarianceRemainderPhysicalPairCarrier_subset_endpointSquare
    (W : ℕ) :
    postRootCovarianceRemainderPhysicalPairCarrier W ⊆
      (Finset.Icc 1 W).product (Finset.Icc 1 W) := by
  intro mn hmn
  have hphysical :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hmn).1
  rcases mem_mertensPositivePhysicalPairCarrier.mp hphysical with
    ⟨hm1, hmW, hn1, hnW, _hmn⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hm1, hmW⟩,
      Finset.mem_Icc.mpr ⟨hn1, hnW⟩⟩

/-- **Coarse unconditional attachment point.**  Before using any cancellation,
the signed post-root remainder is bounded by the cardinality of its physical
pair carrier, hence by the endpoint square.  This is deliberately weak but
fully unconditional: later work only tightens this same tether. -/
theorem postRootCovarianceRemainder_le_endpoint_sq (W : ℕ) :
    postRootCovarianceRemainder W ≤ (W : ℝ) ^ 2 := by
  have hsubset :=
    postRootCovarianceRemainderPhysicalPairCarrier_subset_endpointSquare W
  have hcard :
      (postRootCovarianceRemainderPhysicalPairCarrier W).card ≤ W * W := by
    have h := Finset.card_le_card hsubset
    simpa [Nat.card_Icc] using h
  rw [postRootCovarianceRemainder_eq_physicalPairCarrier]
  calc
    (∑ mn ∈ postRootCovarianceRemainderPhysicalPairCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) ≤
      ∑ _mn ∈ postRootCovarianceRemainderPhysicalPairCarrier W, (1 : ℝ) :=
        Finset.sum_le_sum fun mn _hmn => realMoebiusPairWeight_le_one mn.1 mn.2
    _ = ((postRootCovarianceRemainderPhysicalPairCarrier W).card : ℝ) := by simp
    _ ≤ ((W * W : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (W : ℝ) ^ 2 := by push_cast; ring

/-- For every positive power loss, the normalized seat is already bounded by
one physical endpoint.  The remaining task is to replace this growing ceiling
by a uniform one. -/
theorem postRootCovariancePowerSeat_le_endpoint
    (ε : ℝ) (hε : 0 < ε) (W : ℕ) :
    postRootCovariancePowerSeat ε W ≤ (W : ℝ) := by
  unfold postRootCovariancePowerSeat
  by_cases hW : 2 ≤ W
  · rw [if_pos hW]
    apply max_le
    · positivity
    · have hWpos : (0 : ℝ) < (W : ℝ) := by
        exact_mod_cast (show 0 < W by omega)
      have hbase : (1 : ℝ) ≤ (W : ℝ) := by
        exact_mod_cast (show 1 ≤ W by omega)
      have hpow :
          (W : ℝ) ≤ Real.rpow (W : ℝ) (1 + ε) := by
        have h := Real.rpow_le_rpow_of_exponent_le hbase
          (by linarith : (1 : ℝ) ≤ 1 + ε)
        simpa only [Real.rpow_one] using h
      have hpowpos : 0 < Real.rpow (W : ℝ) (1 + ε) :=
        Real.rpow_pos_of_pos hWpos _
      apply (div_le_iff₀ hpowpos).2
      calc
        postRootCovarianceRemainder W ≤ (W : ℝ) ^ 2 :=
          postRootCovarianceRemainder_le_endpoint_sq W
        _ = (W : ℝ) * (W : ℝ) := by ring
        _ ≤ (W : ℝ) * Real.rpow (W : ℝ) (1 + ε) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  · rw [if_neg hW]
    positivity

/-- The explicit running envelope therefore has an unconditional linear
finite-horizon ceiling.  This is the initial string: all later synthesis can be
measured as an improvement from `N` toward a constant. -/
theorem postRootCovariancePowerEnvelope_le_endpoint
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    postRootCovariancePowerEnvelope ε N ≤ (N : ℝ) := by
  induction N with
  | zero => simp [postRootCovariancePowerEnvelope]
  | succ N ih =>
      rw [postRootCovariancePowerEnvelope]
      apply max_le
      · have hcast : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ N
        exact ih.trans hcast
      · simpa only [Nat.succ_eq_add_one] using
          postRootCovariancePowerSeat_le_endpoint ε hε (N + 1)

/-- **Finite-horizon tether.** Every signed remainder up to `N` is bounded by
the explicit running envelope times the target power. No arithmetic estimate is
used here; the theorem only packages the exact finite obstruction into a single
monotone scalar. -/
theorem postRootCovarianceRemainder_le_powerEnvelope
    (ε : ℝ) {W N : ℕ} (hW : 2 ≤ W) (hWN : W ≤ N) :
    postRootCovarianceRemainder W ≤
      postRootCovariancePowerEnvelope ε N *
        Real.rpow (W : ℝ) (1 + ε) := by
  have hWpos : (0 : ℝ) < (W : ℝ) := by
    exact_mod_cast (show 0 < W by omega)
  have hpowpos : 0 < Real.rpow (W : ℝ) (1 + ε) :=
    Real.rpow_pos_of_pos hWpos _
  have hseat := postRootCovariancePowerSeat_le_envelope ε hWN
  have hratioSeat :
      postRootCovarianceRemainder W /
          Real.rpow (W : ℝ) (1 + ε) ≤
        postRootCovariancePowerSeat ε W := by
    unfold postRootCovariancePowerSeat
    rw [if_pos hW]
    exact le_max_right _ _
  have hratio :
      postRootCovarianceRemainder W /
          Real.rpow (W : ℝ) (1 + ε) ≤
        postRootCovariancePowerEnvelope ε N :=
    hratioSeat.trans hseat
  exact (div_le_iff₀ hpowpos).1 hratio

/-- Uniform boundedness of the concrete finite-horizon envelope. This is the
same arithmetic content as the positive-power remainder hypothesis, but now in
a form that can be tightened by any later coordinate-wise inequality. -/
def PostRootCovariancePowerEnvelopeBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ N : ℕ, postRootCovariancePowerEnvelope ε N ≤ D

/-- Uniform boundedness of the cumulative positive record excesses. -/
def PostRootCovariancePowerRecordExcessBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ N : ℕ,
        (∑ j ∈ Finset.range N, postRootCovariancePowerRecordExcess ε j) ≤ D

/-- The abstract power-remainder hypothesis bounds the explicit running
envelope. -/
theorem postRootCovariancePowerEnvelopeBounded_of_powerRemainder
    (hpower : PostRootCovariancePowerRemainderStatement) :
    PostRootCovariancePowerEnvelopeBoundedStatement := by
  intro ε hε
  rcases hpower ε hε with ⟨D, hD, hrem⟩
  refine ⟨D, hD, ?_⟩
  intro N
  induction N with
  | zero => simpa [postRootCovariancePowerEnvelope] using hD
  | succ N ih =>
      rw [postRootCovariancePowerEnvelope]
      apply max_le ih
      unfold postRootCovariancePowerSeat
      by_cases hW : 2 ≤ N + 1
      · rw [if_pos hW]
        apply max_le hD
        have hWpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < N + 1 by omega)
        have hpowpos :
            0 < Real.rpow ((N + 1 : ℕ) : ℝ) (1 + ε) :=
          Real.rpow_pos_of_pos hWpos _
        exact (div_le_iff₀ hpowpos).2 (hrem (N + 1) hW)
      · rw [if_neg hW]
        exact hD

/-- Conversely, a uniform bound on the concrete running envelope supplies the
power-remainder hypothesis with exactly the same constant. -/
theorem postRootCovariancePowerRemainder_of_powerEnvelopeBounded
    (henv : PostRootCovariancePowerEnvelopeBoundedStatement) :
    PostRootCovariancePowerRemainderStatement := by
  intro ε hε
  rcases henv ε hε with ⟨D, hD, hbound⟩
  refine ⟨D, hD, ?_⟩
  intro W hW
  have htether :=
    postRootCovarianceRemainder_le_powerEnvelope ε hW (le_refl W)
  have hWpos : (0 : ℝ) < (W : ℝ) := by
    exact_mod_cast (show 0 < W by omega)
  have hpow_nonneg :
      0 ≤ Real.rpow (W : ℝ) (1 + ε) :=
    (Real.rpow_pos_of_pos hWpos _).le
  exact htether.trans
    (mul_le_mul_of_nonneg_right (hbound W) hpow_nonneg)

/-- The record-excess partial sums and the running envelope are exactly the same
quantity, so boundedness of either formulation is equivalent. -/
theorem postRootCovariancePowerRecordExcessBounded_iff_powerEnvelopeBounded :
    PostRootCovariancePowerRecordExcessBoundedStatement ↔
      PostRootCovariancePowerEnvelopeBoundedStatement := by
  constructor
  · intro hexcess
    intro ε hε
    rcases hexcess ε hε with ⟨D, hD, hbound⟩
    refine ⟨D, hD, ?_⟩
    intro N
    rw [postRootCovariancePowerEnvelope_eq_sum_recordExcess]
    exact hbound N
  · intro henv
    intro ε hε
    rcases henv ε hε with ⟨D, hD, hbound⟩
    refine ⟨D, hD, ?_⟩
    intro N
    rw [← postRootCovariancePowerEnvelope_eq_sum_recordExcess]
    exact hbound N

/-- **Exact tether equivalence.** The new running envelope is not a stronger
assumption and not a heuristic replacement: its uniform boundedness is exactly
the positive-power signed remainder seam from #599. -/
theorem postRootCovariancePowerEnvelopeBounded_iff_powerRemainder :
    PostRootCovariancePowerEnvelopeBoundedStatement ↔
      PostRootCovariancePowerRemainderStatement :=
  ⟨postRootCovariancePowerRemainder_of_powerEnvelopeBounded,
    postRootCovariancePowerEnvelopeBounded_of_powerRemainder⟩

/-- The same terminal seam in record-excess form: bounding only the cumulative
new-record increments is already sufficient for the power remainder. -/
theorem postRootCovariancePowerRecordExcessBounded_iff_powerRemainder :
    PostRootCovariancePowerRecordExcessBoundedStatement ↔
      PostRootCovariancePowerRemainderStatement := by
  rw [postRootCovariancePowerRecordExcessBounded_iff_powerEnvelopeBounded,
    postRootCovariancePowerEnvelopeBounded_iff_powerRemainder]

/-- The exact scalar post-root Euler finite difference from the complete LCM
boundary, written as the falling-factorial Mertens field `M(M-1)`. -/
def postRootFallingEnergyFiniteDifference (W : ℕ) : ℝ :=
  (realMertensLength (W + 1) ^ 2 - realMertensLength (W + 1)) -
    ∑ p ∈ postRootPrimeFamilySet W,
      (realMertensLength (W / p + 1) ^ 2 -
        realMertensLength (W / p + 1))

/-- The scalar falling-energy finite difference is exactly twice the literal
post-root super-endpoint LCM-boundary mass. -/
theorem postRootFallingEnergyFiniteDifference_eq_two_mul_boundaryLcmMass
    (W : ℕ) :
    postRootFallingEnergyFiniteDifference W =
      2 * (∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) := by
  unfold postRootFallingEnergyFiniteDifference
  exact
    (two_mul_sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_lengthFiniteDifference W).symm

/-- Positive power scale dominates one endpoint unit. -/
theorem endpoint_le_postRootPowerScale
    {ε : ℝ} (hε : 0 < ε) {W : ℕ} (hW : 2 ≤ W) :
    (W : ℝ) ≤ Real.rpow (W : ℝ) (1 + ε) := by
  have hbase : (1 : ℝ) ≤ (W : ℝ) := by
    exact_mod_cast (show 1 ≤ W by omega)
  have h := Real.rpow_le_rpow_of_exponent_le hbase
    (by linarith : (1 : ℝ) ≤ 1 + ε)
  simpa only [Real.rpow_one] using h

/-- Positive-power control of the exact scalar falling-energy finite difference.
This is the #597 boundary seam with the weaker exponent needed by #599. -/
def PostRootFallingEnergyFiniteDifferencePowerStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ W : ℕ, 2 ≤ W →
        postRootFallingEnergyFiniteDifference W ≤
          D * Real.rpow (W : ℝ) (1 + ε)

/-- A positive-power bound on the scalar falling-energy finite difference gives
the post-root covariance power remainder.  The only loss is one endpoint unit
from the already-packed complete-LCM interior. -/
theorem postRootCovariancePowerRemainder_of_fallingEnergyFiniteDifferencePower
    (hfall : PostRootFallingEnergyFiniteDifferencePowerStatement) :
    PostRootCovariancePowerRemainderStatement := by
  intro ε hε
  rcases hfall ε hε with ⟨D, hD, hfallBound⟩
  refine ⟨D / 2 + 1, by positivity, ?_⟩
  intro W hW
  have hf := hfallBound W hW
  have hboundary :=
    postRootFallingEnergyFiniteDifference_eq_two_mul_boundaryLcmMass W
  have hinterior :=
    sum_postRootCovarianceRemainderInteriorLcmCarrier_le_endpoint W
  have hsplit :=
    postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm W
  have hscale := endpoint_le_postRootPowerScale hε hW
  nlinarith

/-- Conversely, the post-root covariance power remainder controls the scalar
falling-energy finite difference.  The lower complete-LCM interior bound costs
one endpoint unit, and the scalar boundary identity contributes the factor two. -/
theorem postRootFallingEnergyFiniteDifferencePower_of_powerRemainder
    (hpower : PostRootCovariancePowerRemainderStatement) :
    PostRootFallingEnergyFiniteDifferencePowerStatement := by
  intro ε hε
  rcases hpower ε hε with ⟨D, hD, hrem⟩
  refine ⟨2 * (D + 1), by positivity, ?_⟩
  intro W hW
  have hr := hrem W hW
  have hboundary :=
    postRootFallingEnergyFiniteDifference_eq_two_mul_boundaryLcmMass W
  have hinterior :=
    neg_endpoint_le_sum_postRootCovarianceRemainderInteriorLcmCarrier W
  have hsplit :=
    postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm W
  have hscale := endpoint_le_postRootPowerScale hε hW
  nlinarith

/-- **Exact scalar tether equivalence.**  Up to the already-proved linear
complete-LCM interior, the positive-power covariance seam and the falling-energy
Euler finite-difference seam are the same quantitative problem. -/
theorem postRootFallingEnergyFiniteDifferencePower_iff_powerRemainder :
    PostRootFallingEnergyFiniteDifferencePowerStatement ↔
      PostRootCovariancePowerRemainderStatement :=
  ⟨postRootCovariancePowerRemainder_of_fallingEnergyFiniteDifferencePower,
    postRootFallingEnergyFiniteDifferencePower_of_powerRemainder⟩

/-- The finite-horizon running envelope is uniformly bounded exactly when the
scalar falling-energy finite difference has the target positive-power bound. -/
theorem postRootCovariancePowerEnvelopeBounded_iff_fallingEnergyFiniteDifferencePower :
    PostRootCovariancePowerEnvelopeBoundedStatement ↔
      PostRootFallingEnergyFiniteDifferencePowerStatement := by
  rw [postRootCovariancePowerEnvelopeBounded_iff_powerRemainder,
    ← postRootFallingEnergyFiniteDifferencePower_iff_powerRemainder]

/-- **Arrow/string endpoint.**  Bounded cumulative new-record excesses are
exactly equivalent to positive-power control of the explicit scalar
falling-energy finite difference.  Future inequalities may therefore tighten
the record-excess tail or the scalar finite difference interchangeably. -/
theorem postRootCovariancePowerRecordExcessBounded_iff_fallingEnergyFiniteDifferencePower :
    PostRootCovariancePowerRecordExcessBoundedStatement ↔
      PostRootFallingEnergyFiniteDifferencePowerStatement := by
  rw [postRootCovariancePowerRecordExcessBounded_iff_powerRemainder,
    ← postRootFallingEnergyFiniteDifferencePower_iff_powerRemainder]

/-- Bounding the explicit running envelope therefore reaches the protected
Mertens energy criterion through the #599 bootstrap. -/
theorem mertensEnergyBounded_of_postRootCovariancePowerEnvelopeBounded
    (henv : PostRootCovariancePowerEnvelopeBoundedStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_postRootCovariancePowerRemainder
    (postRootCovariancePowerRemainder_of_powerEnvelopeBounded henv)

/-- A bounded cumulative record-excess majorant therefore reaches the protected
Mertens energy criterion as well. -/
theorem mertensEnergyBounded_of_postRootCovariancePowerRecordExcessBounded
    (hexcess : PostRootCovariancePowerRecordExcessBoundedStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_postRootCovariancePowerEnvelopeBounded
    (postRootCovariancePowerRecordExcessBounded_iff_powerEnvelopeBounded.mp hexcess)

/-- Positive-power control of the explicit falling-energy finite difference
therefore feeds the protected Mertens-energy criterion through #599. -/
theorem mertensEnergyBounded_of_postRootFallingEnergyFiniteDifferencePower
    (hfall : PostRootFallingEnergyFiniteDifferencePowerStatement) :
    MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_postRootCovariancePowerRemainder
    (postRootCovariancePowerRemainder_of_fallingEnergyFiniteDifferencePower hfall)

end RHLean.Proof
