import Mathlib
import «research.VF_CANONICAL_ALL_REAL_LI_O_ONE»
import «research.VF_MID_SQRT_TWO_VERTICAL_PNT_HORIZONTAL»
import «research.VF_MID_SQRT_TWO_LI_HORIZONTAL»
import «research.VF_MID_LI_PHASE_FAN»

/-!
# CANONICAL VF: original square-band midpoint path + FIXED vertical sqrt(2)

NEW AUTHORITATIVE USER-FACING VF COORDINATE, x>=4:
  VF(x) := vfMid(x) + sqrt(2).
  VF(R^2) = sum_(2<=r<R) (2r+1)/log(r^2+r+1/2) + sqrt(2).
  k_R := floor(VF(R^2)).
  D_R := pi(R^2) - VF(R^2).
  Li_2(x) := integral_2^x dt/log(t).

The additive phase NEVER changes the original midpoint band weights,
the prime wheel, the born/returned owner masks or their native incidence.
The historical x=9 exact anchor c0=4-F_3 is different from sqrt(2).
Integer floors and odd fractional seat staircases are not the real VF path.

The existing vfMid, vfMidAligned, vfMidSqrtTwo* names remain immutable
LEGACY INTERNAL COORDINATES so the thousands of existing proof declarations
do not become ill-typed. New proofs and docs refer to THIS canonical layer,
with an exact translation theorem for every old VF quantity. "Supersedes"
is a statement of naming and interface authority, NOT an attempt to
overwrite the historic definitions behind already-compiled theorems.

No actual pi-Li cancellation or RH claim is made in this file.
-/

noncomputable section

namespace RHLean.Analysis

/-- The ONLY canonical VF vertical adjustment. -/
def vfCanonicalPhase : ℝ := vfMidSqrtTwoVerticalPhase

@[simp] theorem vfCanonicalPhase_eq_sqrt_two :
    vfCanonicalPhase = Real.sqrt 2 := rfl

theorem vfCanonicalPhase_nonneg : 0 ≤ vfCanonicalPhase := by
  exact vfMidSqrtTwoVerticalPhase_nonneg

/-- The real canonical VF path. Restrict the prime-counting interpretation
to x>=4; the extension below 4 is merely a convenience for total functions. -/
def vfCanonical (x : ℝ) : ℝ :=
  vfMidAligned vfCanonicalPhase x

/-- At real x>=4, the canonical definition is literally a vertical shift,
not a new approximation family or a reweighting of any square-band seat. -/
theorem vfCanonical_eq_legacy_plus_sqrt_two (x : ℝ) :
    vfCanonical x = vfMid x + Real.sqrt 2 := rfl

/-- Exact correspondence to the old chosen sqrt-two aligned continuum. -/
theorem vfCanonical_eq_oldAligned (x : ℝ) :
    vfCanonical x = vfMidAligned vfMidSqrtTwoVerticalPhase x := rfl

/-- Real canonical square-block endpoint. -/
def vfCanonicalFinishedMass (R : ℕ) : ℝ :=
  vfMidAlignedMass vfCanonicalPhase R

/-- The integer step graph is an auxiliary rounding of the real canonical
endpoint, not a separate real VF construction. -/
def vfCanonicalIntegerLevel (R : ℕ) : ℕ :=
  vfMidSqrtTwoIntegerLevel R

theorem vfCanonicalIntegerLevel_eq_floor (R : ℕ) :
    vfCanonicalIntegerLevel R =
      ⌊vfCanonicalFinishedMass R⌋₊ := rfl

theorem vfCanonicalFinishedMass_eq_unshifted (R : ℕ) :
    vfCanonicalFinishedMass R =
      vfMidFinishedMass R + Real.sqrt 2 := rfl

/-- Canonical continuous path and real discrete completed square mass agree
exactly at every original square endpoint. -/
theorem vfCanonical_sq {R : ℕ} (hR : 2 ≤ R) :
    vfCanonical ((R : ℝ) ^ 2) = vfCanonicalFinishedMass R := by
  exact vfMidAligned_sq vfCanonicalPhase hR

/-- The sqrt-two adjustment CANCELS under forward differences, so it never
changes the original block mass, prefix wheel or weighted source. -/
theorem vfCanonicalFinishedMass_succ {R : ℕ} (hR : 2 ≤ R) :
    vfCanonicalFinishedMass (R + 1) =
      vfCanonicalFinishedMass R + vfMidBandMass R := by
  exact vfMidAlignedMass_succ vfCanonicalPhase hR

/-- The prime staircase remains the ACTUAL Nat.primeCounting. -/
def vfCanonicalPrimeError (x : ℝ) : ℝ :=
  vfMidPrimeCount x - vfCanonical x

/-- Canonical real VF / Li_2 error. -/
def vfCanonicalLiError (x : ℝ) : ℝ :=
  vfCanonical x - vfMidLogarithmicIntegralFromTwo x

/-- Original prime error shifts by exactly minus sqrt-two; no new arithmetic
involves the vertical alignment. -/
theorem vfCanonicalPrimeError_eq_legacy_sub_phase (x : ℝ) :
    vfCanonicalPrimeError x =
      vfMidPrimeError x - vfCanonicalPhase := by
  unfold vfCanonicalPrimeError vfCanonical vfMidAligned vfMidPrimeError
  ring

theorem vfCanonicalLiError_eq_legacy_add_phase (x : ℝ) :
    vfCanonicalLiError x =
      vfMidLiError x + vfCanonicalPhase := by
  unfold vfCanonicalLiError vfCanonical vfMidAligned vfMidLiError
  ring

/-- Every real cutoff x>=4 has an absolute UNIFORM canonical VF-Li_2 error
bound. This includes LIVE interiors of all square blocks, not just R^2. -/
def vfCanonicalLiAllRealUniformConstant : ℝ :=
  vfMidLiAllRealUniformConstant + vfCanonicalPhase

theorem vfCanonicalLiAllRealUniformConstant_nonneg :
    0 ≤ vfCanonicalLiAllRealUniformConstant := by
  unfold vfCanonicalLiAllRealUniformConstant
  exact add_nonneg vfMidLiAllRealUniformConstant_nonneg
    vfCanonicalPhase_nonneg

theorem abs_vfCanonicalLiError_le_uniform_allReal
    {x : ℝ} (hx : 4 ≤ x) :
    |vfCanonical x - vfMidLogarithmicIntegralFromTwo x| ≤
      vfCanonicalLiAllRealUniformConstant := by
  change |vfCanonicalLiError x| ≤ _
  rw [vfCanonicalLiError_eq_legacy_add_phase]
  calc
    |vfMidLiError x + vfCanonicalPhase|
      ≤ |vfMidLiError x| + |vfCanonicalPhase| := abs_add_le _ _
    _ = |vfMidLiError x| + vfCanonicalPhase := by
      rw [abs_of_nonneg vfCanonicalPhase_nonneg]
    _ ≤ vfMidLiAllRealUniformConstant + vfCanonicalPhase := by
      exact add_le_add_left (abs_vfMidLiError_le_uniform_allReal hx) _
    _ = vfCanonicalLiAllRealUniformConstant := rfl

/-- The tighter bound at all COMPLETE square endpoints has no live tile. -/
theorem abs_vfCanonicalLiError_sq_le_uniform
    {R : ℕ} (hR : 2 ≤ R) :
    |vfCanonical ((R : ℝ) ^ 2) -
        vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)| ≤
      vfMidLiSquareEndpointUniformConstant + vfCanonicalPhase := by
  change |vfCanonicalLiError ((R : ℝ)^2)| ≤ _
  rw [vfCanonicalLiError_eq_legacy_add_phase]
  calc
    |vfMidLiError ((R : ℝ)^2) + vfCanonicalPhase|
      ≤ |vfMidLiError ((R : ℝ)^2)| + |vfCanonicalPhase| :=
          abs_add_le _ _
    _ = |vfMidLiError ((R : ℝ)^2)| + vfCanonicalPhase := by
      rw [abs_of_nonneg vfCanonicalPhase_nonneg]
    _ ≤ vfMidLiSquareEndpointUniformConstant + vfCanonicalPhase := by
      exact add_le_add_left (abs_vfMidLiError_sq_le_uniform hR) _

/-- Genuine pi(R^2) minus REAL sqrt-two-shifted canonical VF. -/
def vfCanonicalSquareDefect (R : ℕ) : ℝ :=
  (Nat.primeCounting (R ^ 2) : ℝ) - vfCanonicalFinishedMass R

theorem vfCanonicalSquareDefect_eq_legacy_sub_phase (R : ℕ) :
    vfCanonicalSquareDefect R =
      vfMidDirectSquareEndpointError R - vfCanonicalPhase := by
  unfold vfCanonicalSquareDefect vfCanonicalFinishedMass
    vfMidAlignedMass vfMidDirectSquareEndpointError
  ring

theorem vfCanonicalSquareDefect_eq_sqrtTwoAlignedError (R : ℕ) :
    vfCanonicalSquareDefect R =
      vfMidAlignedSquareEndpointError vfMidSqrtTwoVerticalPhase R := rfl

/-- All real x>=4 and complete square endpoints share the same phase. -/
theorem vfCanonicalPrimeError_sq_eq_squareDefect
    {R : ℕ} (hR : 2 ≤ R) :
    vfCanonicalPrimeError ((R : ℝ) ^ 2) =
      vfCanonicalSquareDefect R := by
  rw [vfCanonicalPrimeError_eq_legacy_sub_phase,
    ← vfMidDirectSquareEndpointError_eq_vfMidPrimeError hR]
  exact (vfCanonicalSquareDefect_eq_legacy_sub_phase R).symm

/-- The fully original ACTUAL-prime block recurrence survives unchanged. -/
theorem vfCanonicalSquareDefect_succ
    (R : ℕ) (hR : 2 ≤ R) :
    vfCanonicalSquareDefect (R + 1) =
      vfCanonicalSquareDefect R + vfMidDirectBandError R := by
  rw [vfCanonicalSquareDefect_eq_legacy_sub_phase,
      vfCanonicalSquareDefect_eq_legacy_sub_phase,
      vfMidDirectSquareEndpointError_succ R hR]
  ring

/-- The unaltered real VF weights are the actual source. This is an exact
restatement, not a signed estimate or a negative-owner payment. -/
theorem vfCanonicalSquareDefect_succ_primeWheel
    (R : ℕ) (hR : 2 ≤ R) :
    vfCanonicalSquareDefect (R + 1) =
      vfCanonicalSquareDefect R +
        (vfMidDirectPrimeBandCount R - vfMidBandMass R) := by
  rw [vfCanonicalSquareDefect_succ R hR]
  rfl

/-- The true pi-minus-Li_2 discrepancy splits into genuine pi-minus-canonical
and uniformly bounded canonical-minus-Li_2, for every real cutoff. -/
theorem vfCanonicalPrimeLiError_eq_primeError_add_quadrature
    (x : ℝ) :
    vfMidPrimeLiError x =
      vfCanonicalPrimeError x + vfCanonicalLiError x := by
  unfold vfMidPrimeLiError vfCanonicalPrimeError vfCanonicalLiError
  ring

/-- No pointwise "canonical VF is always closer to primes" is claimed.
Even x=4 fails such a universal numerical claim. -/
theorem vfCanonicalPrimeError_abs_le_primeLi_abs_add_uniform
    {x : ℝ} (hx : 4 ≤ x) :
    |vfCanonicalPrimeError x| ≤
      |vfMidPrimeLiError x| + vfCanonicalLiAllRealUniformConstant := by
  have hrel := vfCanonicalPrimeLiError_eq_primeError_add_quadrature x
  have hbound := abs_vfCanonicalLiError_le_uniform_allReal hx
  change |vfCanonicalLiError x| ≤ _ at hbound
  have hident :
      vfCanonicalPrimeError x =
        vfMidPrimeLiError x - vfCanonicalLiError x := by
    linarith
  rw [hident]
  exact (abs_sub _ _).trans (add_le_add_right hbound _)

/-! ### Exact vertical phase correction to energy, historical return and floors -/

/-- Absolute wall, first-bad trigger and squared energy MUST use the
canonical translated value, not the unchanged raw endpoint. -/
theorem vfCanonicalSquareDefect_sq_eq_legacy_cross_corrected
    (R : ℕ) :
    (vfCanonicalSquareDefect R) ^ 2 =
      (vfMidDirectSquareEndpointError R) ^ 2 -
        2 * vfCanonicalPhase * vfMidDirectSquareEndpointError R + 2 := by
  rw [vfCanonicalSquareDefect_eq_legacy_sub_phase]
  have hsq : vfCanonicalPhase ^ 2 = 2 :=
    vfMidSqrtTwoVerticalPhase_sq
  calc
    (vfMidDirectSquareEndpointError R - vfCanonicalPhase) ^ 2 =
      (vfMidDirectSquareEndpointError R) ^ 2 -
        2 * vfCanonicalPhase * vfMidDirectSquareEndpointError R +
          vfCanonicalPhase ^ 2 := by ring
    _ = (vfMidDirectSquareEndpointError R) ^ 2 -
        2 * vfCanonicalPhase * vfMidDirectSquareEndpointError R + 2 := by
      rw [hsq]

/-- Subtracting TWO endpoint values cancels sqrt2; original signed
source / owner run telescoping is UNCHANGED. -/
theorem vfCanonicalSquareDefect_interval_eq_legacy
    (A R : ℕ) :
    vfCanonicalSquareDefect R - vfCanonicalSquareDefect A =
      vfMidDirectSquareEndpointError R -
        vfMidDirectSquareEndpointError A := by
  rw [vfCanonicalSquareDefect_eq_legacy_sub_phase,
    vfCanonicalSquareDefect_eq_legacy_sub_phase]
  ring

/-- The canonical noninteger fractional floor remainder is in [0,1);
it is a distinct object from the original signed arithmetic defect. -/
def vfCanonicalRoundingPhase (R : ℕ) : ℝ :=
  vfMidAlignedRoundingPhase vfCanonicalPhase R

theorem vfCanonicalRoundingPhase_bounds (R : ℕ) :
    0 ≤ vfCanonicalRoundingPhase R ∧
      vfCanonicalRoundingPhase R < 1 := by
  exact vfMidAlignedRoundingPhase_bounds
    vfCanonicalPhase vfCanonicalPhase_nonneg R

/-- The floor staircase has ONLY a bounded telescope correction, not
a new prime supply or reweighting of the original midpoint band. -/
theorem vfCanonicalIntegerLevel_succ_real
    {R : ℕ} (hR : 2 ≤ R) :
    (vfCanonicalIntegerLevel (R + 1) : ℝ) -
        (vfCanonicalIntegerLevel R : ℝ) =
      vfMidBandMass R + vfCanonicalRoundingPhase R -
        vfCanonicalRoundingPhase (R + 1) := by
  exact vfMidAlignedIntegerBlockLevel_succ_real
    vfCanonicalPhase hR

/-- Exact canonical integer-level backlog: besides the canonical
ACTUAL prime defect, there is only the bounded subunit rounding phase. -/
def vfCanonicalIntegerBacklog (R : ℕ) : ℝ :=
  (vfCanonicalIntegerLevel R : ℝ) -
    (Nat.primeCounting (R ^ 2) : ℝ)

theorem vfCanonicalIntegerBacklog_eq_neg_defect_sub_rounding
    (R : ℕ) :
    vfCanonicalIntegerBacklog R =
      -vfCanonicalSquareDefect R - vfCanonicalRoundingPhase R := by
  unfold vfCanonicalIntegerBacklog vfCanonicalIntegerLevel
    vfCanonicalRoundingPhase
  have h := vfMidSqrtTwoIntegerBacklog_eq_actualPrimeError R
  rw [h]
  rw [vfCanonicalSquareDefect_eq_legacy_sub_phase]
  simp only [vfCanonicalPhase]
  ring

/-! ### Distinct *proxy* and phase-fan coordinates -/

/-- Canonical phase chord: the REAL midpoint-to-midpoint chord, not the
within-block fractional odd seat staircase or the rounded integer level. -/
def vfCanonicalUpperLeftPhase (R : ℕ) (t : ℝ) : ℝ :=
  vfMidUpperLeftPhase R t + vfCanonicalPhase

theorem vfCanonicalUpperLeftPhase_eq_legacy (R : ℕ) (t : ℝ) :
    vfCanonicalUpperLeftPhase R t =
      vfMidUpperLeftPhase R t + Real.sqrt 2 := rfl

theorem vfCanonicalUpperLeftPhase_li_uniform
    (R : ℕ) (hR : 2 ≤ R) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |vfCanonicalUpperLeftPhase R t - vfMidLiUpperLeftPhase R t| ≤
      vfMidLiSquareEndpointUniformConstant + vfCanonicalPhase := by
  have hlegacy :=
    abs_vfMidUpperLeftPhase_sub_liUpperLeftPhase_le_uniform
      R hR t ht0 ht1
  have hid :
    vfCanonicalUpperLeftPhase R t - vfMidLiUpperLeftPhase R t =
      (vfMidUpperLeftPhase R t - vfMidLiUpperLeftPhase R t) +
        vfCanonicalPhase := by
    unfold vfCanonicalUpperLeftPhase
    ring
  rw [hid]
  calc
    |(vfMidUpperLeftPhase R t - vfMidLiUpperLeftPhase R t) +
        vfCanonicalPhase|
      ≤ |vfMidUpperLeftPhase R t - vfMidLiUpperLeftPhase R t| +
          |vfCanonicalPhase| := abs_add_le _ _
    _ ≤ vfMidLiSquareEndpointUniformConstant + vfCanonicalPhase := by
      rw [abs_of_nonneg vfCanonicalPhase_nonneg]
      exact add_le_add_left hlegacy _

end RHLean.Analysis
