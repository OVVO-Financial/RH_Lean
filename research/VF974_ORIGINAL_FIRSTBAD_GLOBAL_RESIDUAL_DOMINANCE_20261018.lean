import Mathlib
import «research.VF974_FIRST_BAD_BOUNDARY_DESCENT_OBSTRUCTION_20261018»

/-!
# The original #915 non-cell anchor is positive under dominant history

The original active residual G is *not* a disposable edge term. It contains
the fully compressed historical D_R anchor. This module derives an exact
scalar formula for G and an elementary lower bound from the original source
and absolute masses. No probabilistic or Möbius-decay input is used.

The positive-global-residual conclusion is a NECESSARY first-bad conditional,
not a contradiction, a new power saving, a sign for the surviving clipped
boundary, or an unconditional RH proof.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Signed squarefree-active one-block source in ORIGINAL VF charge currency. -/
def vf974ActiveSource (R : ℕ) : ℝ :=
  vfMidOneBlockPrimeSeatCharge R +
    vfMidOneBlockProcessedSquarefreeCharge R

/-- Original active absolute block mass. -/
def vf974ActiveAbs (R : ℕ) : ℝ :=
  vfMidOneBlockUpperActiveAbsMass R

/-- Original squareful restoring block mass, never carried by the Möbius tree. -/
def vf974RestoringMass (R : ℕ) : ℝ :=
  vfMidOneBlockProcessedSquarefulCharge R

/-- The COMPLETE original one-block absolute mass, no history decompression. -/
def vf974CurrentAbs (R : ℕ) : ℝ :=
  vf974ActiveAbs R + vf974RestoringMass R

/-- The full global non-cell residual expressed on its exact five scalar
coordinates. This is an algebraic formula, NOT an estimate. -/
def vf974AnchorModel (D X t q diag : ℝ) : ℝ :=
  2 * (D ^ 2 - 2 * D * X) +
    2 * diag - 2 * q * (2 * (D - X - q) + q) -
    (D ^ 2 + 2 * |D| * t + diag +
      q * (2 * (|D| + t) + q))

/-- The full original active source never exceeds its own original absolute
mass; this uses the TRUE squarefree active seat carrier, no artificial signed
parent. -/
theorem vf974_abs_activeSource_le_activeAbs (R : ℕ) :
    |vf974ActiveSource R| ≤ vf974ActiveAbs R := by
  have h :=
    Finset.abs_sum_le_sum_abs
      (s := lowOwnerNonzeroMobiusCarrier (R + 1))
      (f := vfMidOneBlockActivePhysicalSite R)
  rw [vfMidOneBlockActivePhysicalSite_sum_eq_activeSource,
    vfMidOneBlockActivePhysicalSite_absSum_eq] at h
  exact h

/-- Native current signed source = active source + squareful restoring,
and exactly subtracts from the next endpoint discrepancy. -/
theorem vf974_originalDefect_succ_eq_sub_threeStream
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidActualPrimeEndpointDefect (R + 1) =
      vfMidActualPrimeEndpointDefect R -
        vf974ActiveSource R - vf974RestoringMass R := by
  have hthree :=
    vfMidTwoSectorOwnerCharge_succ_eq_prime_add_squarefree_add_squareful hR
  have hrun :=
    vfMidOddRunSeatMass_eq_frozenSurvivor_add_processedOwnerCharge
      hR (by omega : R + 1 ≤ 2 * R)
  have htel :=
    vfMidOddRunSeatMass_eq_neg_endpointError_increment
      R (R + 1) (by omega : 2 ≤ R) (by omega)
  have hD0 :=
    vfMidActualPrimeEndpointDefect_eq_squareEndpointError
      (R := R) (by omega : 2 ≤ R)
  have hD1 :=
    vfMidActualPrimeEndpointDefect_eq_squareEndpointError
      (R := R + 1) (by omega : 2 ≤ R + 1)
  change
    vfMidDyadicFrozenSurvivorSeatCharge R (R + 1) +
      vfMidDyadicProcessedOwnerSeatCharge R (R + 1) =
        vfMidOneBlockPrimeSeatCharge R +
          vfMidOneBlockProcessedSquarefreeCharge R +
          vfMidOneBlockProcessedSquarefulCharge R at hthree
  dsimp [vf974ActiveSource, vf974RestoringMass]
  rw [hD0, hD1]
  linarith

/-- The ORIGINAL one-block absolute mass is exactly active+squareful. -/
theorem vf974_originalCurrentAbs_eq_literalSource (R : ℕ) (hR : 3 ≤ R) :
    vf974CurrentAbs R =
      ∑ n ∈ vfMidOddCandidateSeats R, |vfMidOddSignedSeatCharge R n| := by
  unfold vf974CurrentAbs vf974ActiveAbs vf974RestoringMass
  rw [vfMidOddSeatAbsMass_eq_active_add_omitted hR,
      vfMidWeightedOmittedSeatAbsMass_eq_squarefulCharge hR]

/-- One-block physical charge cannot displace the original defect by more
than its original current absolute mass. -/
theorem vf974_abs_originalDefect_step_le_currentAbs
    {R : ℕ} (hR : 3 ≤ R) :
    |vfMidActualPrimeEndpointDefect (R + 1) -
        vfMidActualPrimeEndpointDefect R| ≤ vf974CurrentAbs R := by
  rw [vf974_originalDefect_succ_eq_sub_threeStream hR]
  have hX := vf974_abs_activeSource_le_activeAbs R
  have hq : 0 ≤ vf974RestoringMass R :=
    vfMidOneBlockProcessedSquarefulCharge_nonneg R (by omega : 2 ≤ R)
  have htri := abs_add_le (vf974ActiveSource R) (vf974RestoringMass R)
  rw [abs_of_nonneg hq] at htri
  unfold vf974CurrentAbs
  have heq :
      vfMidActualPrimeEndpointDefect R -
          vf974ActiveSource R - vf974RestoringMass R -
          vfMidActualPrimeEndpointDefect R =
        -(vf974ActiveSource R + vf974RestoringMass R) := by ring
  rw [heq, abs_neg]
  linarith

/-- The exact original full active residual G equals the five-variable
anchored model; in particular every omitted-squareful/anchor correction
survives the conversion. -/
theorem vf974_globalResidual_eq_exactAnchorModel
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidActiveGlobalResidualExcess R =
      vf974AnchorModel
        (vfMidActualPrimeEndpointDefect R)
        (vf974ActiveSource R)
        (vf974ActiveAbs R)
        (vf974RestoringMass R)
        (vfMidActivePhysicalDiagonalMass R) := by
  unfold vfMidActiveGlobalResidualExcess
    vfMidActiveDemandResidual vfMidActiveCapacityResidual
    vfMidActiveIdentityAnchorGate
    vf974AnchorModel vf974ActiveSource vf974ActiveAbs vf974RestoringMass
  rw [vfMidWeightedOmittedSeatAbsMass_eq_squarefulCharge hR,
      vf974_originalDefect_succ_eq_sub_threeStream hR]
  dsimp [vf974ActiveSource, vf974RestoringMass]

/-- NEW nontrivial sharp-angle obstruction: G is forced large and positive
when the compressed D anchor overwhelms the original one-block source.
No relative prime-density estimate or pairwise independence is assumed. -/
theorem vf974_anchoredModel_ge_history_minus_budget
    (D X t q diag : ℝ)
    (_ht : 0 ≤ t) (hq : 0 ≤ q) (hd : 0 ≤ diag)
    (hX : |X| ≤ t) :
    |D| ^ 2 - 6 * |D| * (t + q) - 6 * (t + q) ^ 2 ≤
      vf974AnchorModel D X t q diag := by
  have hDX : D * X ≤ |D| * t := by
    calc
      D * X ≤ |D * X| := le_abs_self _
      _ = |D| * |X| := abs_mul D X
      _ ≤ |D| * t :=
        mul_le_mul_of_nonneg_left hX (abs_nonneg D)
  have hDq : D * q ≤ |D| * q :=
    mul_le_mul_of_nonneg_right (le_abs_self D) hq
  have hXq : -(t * q) ≤ X * q := by
    have hXlower : -t ≤ X := by
      have habs := neg_le_abs X
      linarith
    simpa only [neg_mul] using!
      (mul_le_mul_of_nonneg_right hXlower hq)
  have hqt : t * q ≤ (t + q) ^ 2 := by
    nlinarith [sq_nonneg (t + q / 2), sq_nonneg q]
  have hDsq : D ^ 2 = |D| ^ 2 := (sq_abs D).symm
  unfold vf974AnchorModel
  nlinarith [hDX, hDq, hXq, hqt, hDsq, sq_nonneg q]

/-- In particular the original G is positive as soon as |D| > 7 beta. -/
theorem vf974_anchoredModel_pos_of_history_gt_seven_budget
    (D X t q diag : ℝ)
    (ht : 0 ≤ t) (hq : 0 ≤ q) (hd : 0 ≤ diag)
    (hX : |X| ≤ t)
    (hdominates : 7 * (t + q) < |D|) :
    0 < vf974AnchorModel D X t q diag := by
  have hbound :=
    vf974_anchoredModel_ge_history_minus_budget
      D X t q diag ht hq hd hX
  have hT : 0 ≤ t + q := add_nonneg ht hq
  have hD : 0 < |D| := by linarith
  have h1 : 0 < |D| * (|D| - 7 * (t + q)) :=
    mul_pos hD (by linarith)
  have h2 : 0 ≤ (t + q) * (|D| - 6 * (t + q)) :=
    mul_nonneg hT (by linarith)
  nlinarith

/-- ORIGINAL #915 global G is positive under the exact original compressed
anchor/current-block dominance, with no assumption about boundary B or H. -/
theorem vf974_originalGlobalResidual_positive_of_anchor_gt_sevenAbs
    {R : ℕ} (hR : 3 ≤ R)
    (hdominates :
      7 * vf974CurrentAbs R < |vfMidActualPrimeEndpointDefect R|) :
    0 < vfMidActiveGlobalResidualExcess R := by
  rw [vf974_globalResidual_eq_exactAnchorModel hR]
  apply vf974_anchoredModel_pos_of_history_gt_seven_budget
  · exact vfMidOneBlockUpperActiveAbsMass_nonneg R
  · exact vfMidOneBlockProcessedSquarefulCharge_nonneg R
      (by omega : 2 ≤ R)
  · exact lowOwnerGlobalDiagonalPairMassWith_nonneg _ _
  · exact vf974_abs_activeSource_le_activeAbs R
  · exact hdominates

/-- A first bad after R>=64 has next error >8R since log(R+1)>4. -/
theorem vf974_firstBad_large_nextDefect_exceeds_eightRoot
    {R : ℕ} (hR : 64 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    8 * (R : ℝ) <
      |vfMidActualPrimeEndpointDefect (R + 1)| := by
  have hlog2 := Real.log_two_gt_d9
  have hlog64 : (4 : ℝ) < Real.log 64 := by
    have hlogeq : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      calc
        Real.log (64 : ℝ) = Real.log ((2 : ℝ) ^ 6) := by norm_num
        _ = (6 : ℕ) * Real.log 2 := by rw [Real.log_pow]
        _ = 6 * Real.log 2 := by norm_num
    rw [hlogeq]
    linarith
  have hle : (64 : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 64 ≤ R + 1 by omega)
  have hlog :
      (4 : ℝ) < Real.log (((R + 1 : ℕ) : ℝ)) :=
    hlog64.trans_le (Real.log_le_log (by norm_num) hle)
  have hRpos : (0 : ℝ) < ((R + 1 : ℕ) : ℝ) := by positivity
  have hbreach := hfirst.1
  unfold VFMidSyntheticBadAt vfMidSyntheticRadialScale at hbreach
  have hmul :
      4 * ((R + 1 : ℕ) : ℝ) <
        Real.log (((R + 1 : ℕ) : ℝ)) * ((R + 1 : ℕ) : ℝ) :=
    mul_lt_mul_of_pos_right hlog hRpos
  have hRcast : ((R + 1 : ℕ) : ℝ) = (R : ℝ) + 1 := by push_cast; ring
  rw [hRcast] at hmul hbreach
  nlinarith

/-- A hypothetical first bad at sufficiently large scale necessarily has a
dominant COMPRESSED historical anchor: over seven times the native current
absolute block mass. This is a quantitative NECESSARY condition. -/
theorem vf974_firstBad_large_anchor_dominates_sevenBlockAbs
    {R : ℕ} (hR : 64 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    7 * vf974CurrentAbs R < |vfMidActualPrimeEndpointDefect R| := by
  have hnext := vf974_firstBad_large_nextDefect_exceeds_eightRoot hR hfirst
  have hstep := vf974_abs_originalDefect_step_le_currentAbs
    (by omega : 3 ≤ R)
  have hblock :=
    vfMidOddSignedSeatCharge_absSum_le_root (R := R) (by omega : 3 ≤ R)
  rw [← vf974_originalCurrentAbs_eq_literalSource R (by omega : 3 ≤ R)] at hblock
  have htri : |vfMidActualPrimeEndpointDefect (R + 1)| ≤
      |vfMidActualPrimeEndpointDefect R| +
        |vfMidActualPrimeEndpointDefect (R + 1) -
            vfMidActualPrimeEndpointDefect R| := by
    have := abs_add_le (vfMidActualPrimeEndpointDefect R)
      (vfMidActualPrimeEndpointDefect (R + 1) -
        vfMidActualPrimeEndpointDefect R)
    convert this using 1; ring
  have hRreal : 0 ≤ (R : ℝ) := by positivity
  linarith

/-- FINAL rigorously forced consequence for every hypothetical first-bad
successor beyond R>=64: the ORIGINAL quarantined global anchor residual G
is strictly POSITIVE. A boundary-only nonpositive domination argument cannot
work. This does NOT give a sign of the boundary, nor rule out first bad. -/
theorem vf974_firstBad_large_forces_positive_globalResidual
    {R : ℕ} (hR : 64 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    0 < vfMidActiveGlobalResidualExcess R :=
  vf974_originalGlobalResidual_positive_of_anchor_gt_sevenAbs
    (by omega : 3 ≤ R)
    (vf974_firstBad_large_anchor_dominates_sevenBlockAbs hR hfirst)

end RHLean.Analysis

#print axioms RHLean.Analysis.vf974_anchoredModel_ge_history_minus_budget
#print axioms RHLean.Analysis.vf974_globalResidual_eq_exactAnchorModel
#print axioms RHLean.Analysis.vf974_firstBad_large_anchor_dominates_sevenBlockAbs
#print axioms RHLean.Analysis.vf974_firstBad_large_forces_positive_globalResidual
