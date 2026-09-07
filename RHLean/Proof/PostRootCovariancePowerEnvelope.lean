import Mathlib
import RHLean.Proof.EndpointCubeAnalyticClosure

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

end RHLean.Proof
