import Mathlib
import «research.VF_MID_LI_UNIFORM_QUADRATURE»
import «research.VF_MID_CORNER_CHANNEL»

/-!
# Uniform VF / Li phase-fan correspondence

PR #870 proves that the square-endpoint midpoint quadrature error is uniformly
bounded:

  |vfMid(R^2) - Li_2(R^2)| <= C

with one fixed constant independent of R.

This file lifts that endpoint theorem to every affine corner phase used by the
multi-shift VF fan.  The key point is that an affine phase is a convex
combination of two neighboring square endpoints.  Therefore the same single
O(1) constant controls every phase, with no factor depending on the number of
forward or backward VF shifts.

Consequently the full O(log(R)^2)-shifted VF fan is uniformly O(1)-close,
wall by wall, to a phase-matched Li fan.  Its total width differs from the
Li-fan width by at most twice the endpoint constant.

No prime-distribution input occurs in this file.
-/

noncomputable section

open Set
open scoped BigOperators

namespace RHLean.Analysis

/-! ## Phase-matched Li chords -/

/-- Li chord joining the exact logarithmic-integral values at two consecutive
square endpoints. -/
def vfMidLiUpperLeftPhase (R : ℕ) (t : ℝ) : ℝ :=
  (1 - t) *
      vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2) +
    t *
      vfMidLogarithmicIntegralFromTwo
        ((((R + 1 : ℕ) : ℝ) ^ 2))

/-- Forward shift by k square blocks of the phase-matched Li chord. -/
def vfMidLiForwardShiftedUpperLeftPhase
    (R k : ℕ) (t : ℝ) : ℝ :=
  vfMidLiUpperLeftPhase (R + k) t

/-- Backward shift by k square blocks of the phase-matched Li chord. -/
def vfMidLiBackwardShiftedUpperLeftPhase
    (R k : ℕ) (t : ℝ) : ℝ :=
  vfMidLiUpperLeftPhase (R - k) t

@[simp] theorem vfMidLiForwardShiftedUpperLeftPhase_zero
    (R : ℕ) (t : ℝ) :
    vfMidLiForwardShiftedUpperLeftPhase R 0 t =
      vfMidLiUpperLeftPhase R t := by
  simp [vfMidLiForwardShiftedUpperLeftPhase]

@[simp] theorem vfMidLiBackwardShiftedUpperLeftPhase_zero
    (R : ℕ) (t : ℝ) :
    vfMidLiBackwardShiftedUpperLeftPhase R 0 t =
      vfMidLiUpperLeftPhase R t := by
  simp [vfMidLiBackwardShiftedUpperLeftPhase]

/-- Exact phase-error identity: the VF-minus-Li chord discrepancy is the same
convex combination of the two neighboring square-endpoint discrepancies. -/
theorem vfMidUpperLeftPhase_sub_liUpperLeftPhase
    (R : ℕ) (hR : 2 ≤ R) (t : ℝ) :
    vfMidUpperLeftPhase R t - vfMidLiUpperLeftPhase R t =
      (1 - t) * vfMidLiError ((R : ℝ) ^ 2) +
        t * vfMidLiError
          ((((R + 1 : ℕ) : ℝ) ^ 2)) := by
  unfold vfMidUpperLeftPhase vfMidLiUpperLeftPhase vfMidLiError
  rw [vfMid_sq hR,
    vfMid_sq (show 2 ≤ R + 1 by omega)]
  ring

/-- Every unshifted phase-matched VF/Li chord pair is controlled by the same
uniform endpoint constant. -/
theorem abs_vfMidUpperLeftPhase_sub_liUpperLeftPhase_le_uniform
    (R : ℕ) (hR : 2 ≤ R) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |vfMidUpperLeftPhase R t - vfMidLiUpperLeftPhase R t| ≤
      vfMidLiSquareEndpointUniformConstant := by
  rw [vfMidUpperLeftPhase_sub_liUpperLeftPhase R hR t]
  have hwt : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hR0 :=
    abs_vfMidLiError_sq_le_uniform (R := R) hR
  have hR1 :=
    abs_vfMidLiError_sq_le_uniform
      (R := R + 1) (by omega)
  calc
    |(1 - t) * vfMidLiError ((R : ℝ) ^ 2) +
        t * vfMidLiError ((((R + 1 : ℕ) : ℝ) ^ 2))|
        ≤
      |(1 - t) * vfMidLiError ((R : ℝ) ^ 2)| +
        |t * vfMidLiError ((((R + 1 : ℕ) : ℝ) ^ 2))| :=
      abs_add_le _ _
    _ =
      (1 - t) * |vfMidLiError ((R : ℝ) ^ 2)| +
        t * |vfMidLiError ((((R + 1 : ℕ) : ℝ) ^ 2))| := by
      rw [abs_mul, abs_of_nonneg hwt,
        abs_mul, abs_of_nonneg ht0]
    _ ≤
      (1 - t) * vfMidLiSquareEndpointUniformConstant +
        t * vfMidLiSquareEndpointUniformConstant := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hR0 hwt)
        (mul_le_mul_of_nonneg_left hR1 ht0)
    _ = vfMidLiSquareEndpointUniformConstant := by
      ring

/-! ## Arbitrary shifted phases -/

/-- A forward shift by any number of blocks inherits exactly the same O(1)
VF/Li phase bound.  There is no accumulation in k. -/
theorem abs_vfMidForwardShiftedPhase_sub_li_le_uniform
    (R k : ℕ) (hR : 2 ≤ R) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |vfMidForwardShiftedUpperLeftPhase R k t -
        vfMidLiForwardShiftedUpperLeftPhase R k t| ≤
      vfMidLiSquareEndpointUniformConstant := by
  unfold vfMidForwardShiftedUpperLeftPhase
    vfMidLiForwardShiftedUpperLeftPhase
  exact
    abs_vfMidUpperLeftPhase_sub_liUpperLeftPhase_le_uniform
      (R + k) (by omega) t ht0 ht1

/-- A backward shift inherits the same O(1) bound whenever the shifted base
index remains at least 2.  Again there is no accumulation in k. -/
theorem abs_vfMidBackwardShiftedPhase_sub_li_le_uniform
    (R k : ℕ) (hR : 2 ≤ R) (hk : k ≤ R - 2) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |vfMidBackwardShiftedUpperLeftPhase R k t -
        vfMidLiBackwardShiftedUpperLeftPhase R k t| ≤
      vfMidLiSquareEndpointUniformConstant := by
  have hbase : 2 ≤ R - k := by omega
  unfold vfMidBackwardShiftedUpperLeftPhase
    vfMidLiBackwardShiftedUpperLeftPhase
  exact
    abs_vfMidUpperLeftPhase_sub_liUpperLeftPhase_le_uniform
      (R - k) hbase t ht0 ht1

/-- The VF phase-fan width. -/
def vfMidShiftedPhaseFanWidth
    (R kminus kplus : ℕ) (t : ℝ) : ℝ :=
  vfMidForwardShiftedUpperLeftPhase R kplus t -
    vfMidBackwardShiftedUpperLeftPhase R kminus t

/-- The phase-matched Li fan width. -/
def vfMidLiShiftedPhaseFanWidth
    (R kminus kplus : ℕ) (t : ℝ) : ℝ :=
  vfMidLiForwardShiftedUpperLeftPhase R kplus t -
    vfMidLiBackwardShiftedUpperLeftPhase R kminus t

/-- The whole fan width is stable under VF -> Li replacement: its width changes
by at most twice the single endpoint constant, independently of either shift
count. -/
theorem abs_vfMidShiftedPhaseFanWidth_sub_li_le_two_uniform
    (R kminus kplus : ℕ) (hR : 2 ≤ R)
    (hkminus : kminus ≤ R - 2) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |vfMidShiftedPhaseFanWidth R kminus kplus t -
        vfMidLiShiftedPhaseFanWidth R kminus kplus t| ≤
      2 * vfMidLiSquareEndpointUniformConstant := by
  have hf :=
    abs_vfMidForwardShiftedPhase_sub_li_le_uniform
      R kplus hR t ht0 ht1
  have hb :=
    abs_vfMidBackwardShiftedPhase_sub_li_le_uniform
      R kminus hR hkminus t ht0 ht1
  unfold vfMidShiftedPhaseFanWidth vfMidLiShiftedPhaseFanWidth
  have hid :
      (vfMidForwardShiftedUpperLeftPhase R kplus t -
          vfMidBackwardShiftedUpperLeftPhase R kminus t) -
        (vfMidLiForwardShiftedUpperLeftPhase R kplus t -
          vfMidLiBackwardShiftedUpperLeftPhase R kminus t) =
      (vfMidForwardShiftedUpperLeftPhase R kplus t -
          vfMidLiForwardShiftedUpperLeftPhase R kplus t) -
        (vfMidBackwardShiftedUpperLeftPhase R kminus t -
          vfMidLiBackwardShiftedUpperLeftPhase R kminus t) := by
    ring
  rw [hid]
  calc
    |(vfMidForwardShiftedUpperLeftPhase R kplus t -
          vfMidLiForwardShiftedUpperLeftPhase R kplus t) -
        (vfMidBackwardShiftedUpperLeftPhase R kminus t -
          vfMidLiBackwardShiftedUpperLeftPhase R kminus t)|
        ≤
      |vfMidForwardShiftedUpperLeftPhase R kplus t -
          vfMidLiForwardShiftedUpperLeftPhase R kplus t| +
        |vfMidBackwardShiftedUpperLeftPhase R kminus t -
          vfMidLiBackwardShiftedUpperLeftPhase R kminus t| :=
      abs_sub _ _
    _ ≤
      vfMidLiSquareEndpointUniformConstant +
        vfMidLiSquareEndpointUniformConstant :=
      add_le_add hf hb
    _ = 2 * vfMidLiSquareEndpointUniformConstant := by ring

/-! ## Physical square-block channels -/

/-- Forward-shifted phase-matched Li chord drawn across the physical square
block R at the same normalized phase used by the VF corner fan. -/
def vfMidLiForwardShiftedCornerChannel
    (k R : ℕ) (x : ℝ) : ℝ :=
  vfMidLiForwardShiftedUpperLeftPhase R k
    (vfMidCornerParameter R x)

/-- Backward-shifted phase-matched Li chord drawn across the physical square
block R at the same normalized phase used by the VF corner fan. -/
def vfMidLiBackwardShiftedCornerChannel
    (k R : ℕ) (x : ℝ) : ℝ :=
  vfMidLiBackwardShiftedUpperLeftPhase R k
    (vfMidCornerParameter R x)

/-- Every forward physical VF fan member stays within the same O(1) constant
of its phase-matched Li member throughout the whole physical square block. -/
theorem abs_vfMidForwardShiftedCornerChannel_sub_li_le_uniform
    (R k : ℕ) (hR : 2 ≤ R) {x : ℝ}
    (hxl : (R : ℝ) ^ 2 ≤ x)
    (hxu : x ≤ (((R + 1 : ℕ) : ℝ) ^ 2)) :
    |vfMidForwardShiftedCornerChannel k R x -
        vfMidLiForwardShiftedCornerChannel k R x| ≤
      vfMidLiSquareEndpointUniformConstant := by
  rcases vfMidCornerParameter_mem_unit hxl hxu with
    ⟨ht0, ht1⟩
  unfold vfMidForwardShiftedCornerChannel
    vfMidLiForwardShiftedCornerChannel
  exact
    abs_vfMidForwardShiftedPhase_sub_li_le_uniform
      R k hR (vfMidCornerParameter R x) ht0 ht1

/-- Every backward physical VF fan member obeys the same pathwise O(1) bound. -/
theorem abs_vfMidBackwardShiftedCornerChannel_sub_li_le_uniform
    (R k : ℕ) (hR : 2 ≤ R) (hk : k ≤ R - 2) {x : ℝ}
    (hxl : (R : ℝ) ^ 2 ≤ x)
    (hxu : x ≤ (((R + 1 : ℕ) : ℝ) ^ 2)) :
    |vfMidBackwardShiftedCornerChannel k R x -
        vfMidLiBackwardShiftedCornerChannel k R x| ≤
      vfMidLiSquareEndpointUniformConstant := by
  rcases vfMidCornerParameter_mem_unit hxl hxu with
    ⟨ht0, ht1⟩
  unfold vfMidBackwardShiftedCornerChannel
    vfMidLiBackwardShiftedCornerChannel
  exact
    abs_vfMidBackwardShiftedPhase_sub_li_le_uniform
      R k hR hk (vfMidCornerParameter R x) ht0 ht1

/-! ## Full canonical O(log^2 R) fan -/

/-- Every pair of shifts inside the maximum canonical VF budget is uniformly
O(1)-matched to its Li fan pair.  The bound does not depend on A, R, or either
chosen shift. -/
theorem vfMidCanonicalPhaseFan_li_uniform
    (A : ℝ) (R kminus kplus : ℕ) (hR : 4 ≤ R)
    (hkminus :
      kminus ≤ vfMidCanonicalCornerOffset A R)
    (hkplus :
      kplus ≤ vfMidCanonicalCornerOffset A R)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |vfMidBackwardShiftedUpperLeftPhase R kminus t -
        vfMidLiBackwardShiftedUpperLeftPhase R kminus t| ≤
          vfMidLiSquareEndpointUniformConstant ∧
      |vfMidForwardShiftedUpperLeftPhase R kplus t -
        vfMidLiForwardShiftedUpperLeftPhase R kplus t| ≤
          vfMidLiSquareEndpointUniformConstant := by
  have hhalf :=
    vfMidCanonicalCornerOffset_two_mul_le (A := A) R
  have hkbase : kminus ≤ R - 2 := by
    omega
  constructor
  · exact
      abs_vfMidBackwardShiftedPhase_sub_li_le_uniform
        R kminus (by omega) hkbase t ht0 ht1
  · exact
      abs_vfMidForwardShiftedPhase_sub_li_le_uniform
        R kplus (by omega) t ht0 ht1

/-- Across the full canonical O(log^2 R) fan, replacing all VF phase members
by their phase-matched Li chords changes the total outer width by at most 2C.
This is the formal VF-fan = Li-fan + O(1) statement. -/
theorem abs_vfMidCanonicalPhaseFanWidth_sub_li_le_two_uniform
    (A : ℝ) (R kminus kplus : ℕ) (hR : 4 ≤ R)
    (hkminus :
      kminus ≤ vfMidCanonicalCornerOffset A R)
    (hkplus :
      kplus ≤ vfMidCanonicalCornerOffset A R)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |vfMidShiftedPhaseFanWidth R kminus kplus t -
        vfMidLiShiftedPhaseFanWidth R kminus kplus t| ≤
      2 * vfMidLiSquareEndpointUniformConstant := by
  have hhalf :=
    vfMidCanonicalCornerOffset_two_mul_le (A := A) R
  have hkbase : kminus ≤ R - 2 := by
    omega
  exact
    abs_vfMidShiftedPhaseFanWidth_sub_li_le_two_uniform
      R kminus kplus (by omega) hkbase t ht0 ht1

/-- Physical-block version for the full canonical fan. -/
theorem vfMidCanonicalCornerFan_li_uniform
    (A : ℝ) (R kminus kplus : ℕ) (hR : 4 ≤ R)
    (hkminus :
      kminus ≤ vfMidCanonicalCornerOffset A R)
    (hkplus :
      kplus ≤ vfMidCanonicalCornerOffset A R)
    {x : ℝ}
    (hxl : (R : ℝ) ^ 2 ≤ x)
    (hxu : x ≤ (((R + 1 : ℕ) : ℝ) ^ 2)) :
    |vfMidBackwardShiftedCornerChannel kminus R x -
        vfMidLiBackwardShiftedCornerChannel kminus R x| ≤
          vfMidLiSquareEndpointUniformConstant ∧
      |vfMidForwardShiftedCornerChannel kplus R x -
        vfMidLiForwardShiftedCornerChannel kplus R x| ≤
          vfMidLiSquareEndpointUniformConstant := by
  have hhalf :=
    vfMidCanonicalCornerOffset_two_mul_le (A := A) R
  have hkbase : kminus ≤ R - 2 := by
    omega
  constructor
  · exact
      abs_vfMidBackwardShiftedCornerChannel_sub_li_le_uniform
        R kminus (by omega) hkbase hxl hxu
  · exact
      abs_vfMidForwardShiftedCornerChannel_sub_li_le_uniform
        R kplus (by omega) hxl hxu

/-- Repository-facing statement: the entire canonical phase fan, up to the
maximum allowed O(log^2 R) VF shift budget, admits one universal VF/Li
correspondence constant. -/
def VFMidLiCanonicalPhaseFanUniformCorrespondenceStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A : ℝ) (R kminus kplus : ℕ),
      4 ≤ R →
      kminus ≤ vfMidCanonicalCornerOffset A R →
      kplus ≤ vfMidCanonicalCornerOffset A R →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        |vfMidBackwardShiftedUpperLeftPhase R kminus t -
            vfMidLiBackwardShiftedUpperLeftPhase R kminus t| ≤ C ∧
          |vfMidForwardShiftedUpperLeftPhase R kplus t -
            vfMidLiForwardShiftedUpperLeftPhase R kplus t| ≤ C

theorem vfMidLiCanonicalPhaseFanUniformCorrespondence :
    VFMidLiCanonicalPhaseFanUniformCorrespondenceStatement := by
  refine
    ⟨vfMidLiSquareEndpointUniformConstant,
      vfMidLiSquareEndpointUniformConstant_nonneg, ?_⟩
  intro A R kminus kplus hR hkminus hkplus t ht0 ht1
  exact
    vfMidCanonicalPhaseFan_li_uniform
      A R kminus kplus hR hkminus hkplus t ht0 ht1

end RHLean.Analysis
