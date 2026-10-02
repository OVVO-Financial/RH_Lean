import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»
import «research.VF_MID_FRACTIONAL_PRIME_CLUSTER»
import «research.VF_MID_MIDPOINT_LINEAR_ALL_X»

/-!
# Four fantasy prime-count closures

This file isolates four deterministic/counterfactual prime-count models and
proves that identifying the actual prime-count staircase with any one of them
supplies the repository's classical von-Koch/RH consumer.

The four models are:

1. continuous Li itself;
2. the integer-valued staircase floor(Li);
3. the exact VF-mid fractional prime cluster at square endpoints;
4. the literal midpoint-to-midpoint VF interpolation on all real x.

These are implication theorems.  They do not identify actual primes with any
fantasy model.  The only external analytic interface is the repository's
explicit `ClassicalVonKochRHCriterion`.
-/

noncomputable section

namespace RHLean.Analysis

/-! ## 1. Continuous Li fantasy -/

/-- Counterfactual identification of the actual prime count with continuous Li
on the range used by the von-Koch criterion. -/
def ContinuousLiFantasyIdentification : Prop :=
  ∀ x : ℝ, 4 ≤ x →
    vfMidPrimeCount x = vfMidLogarithmicIntegralFromTwo x

/-- Under exact continuous-Li identification, the classical prime-minus-Li
error vanishes identically. -/
theorem primeLiVonKochBounded_of_continuousLiFantasy
    (h : ContinuousLiFantasyIdentification) :
    PrimeLiVonKochBoundedStatement := by
  refine ⟨0, le_rfl, ?_⟩
  intro x hx
  have hid := h x hx
  simp [vfMidPrimeLiError, hid]

/-- Fantasy closure 1: exact continuous Li as the prime-count function closes
the repository's classical von-Koch/RH consumer. -/
theorem riemannHypothesis_of_continuousLiFantasy
    (criterion : ClassicalVonKochRHCriterion)
    (h : ContinuousLiFantasyIdentification) :
    VFMidRiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (primeLiVonKochBounded_of_continuousLiFantasy h)

/-! ## 2. Floored Li fantasy -/

/-- Integer-valued discretization obtained by flooring the continuous Li
value.  This discretizes the range while preserving the exact real cutoff. -/
def flooredLiFantasyPrimeCount (x : ℝ) : ℝ :=
  ((⌊vfMidLogarithmicIntegralFromTwo x⌋ : ℤ) : ℝ)

/-- The floored Li model is literally integer-valued. -/
theorem flooredLiFantasyPrimeCount_integer (x : ℝ) :
    ∃ z : ℤ, flooredLiFantasyPrimeCount x = (z : ℝ) := by
  exact ⟨⌊vfMidLogarithmicIntegralFromTwo x⌋, rfl⟩

/-- Flooring changes any real Li value by strictly less than one. -/
theorem abs_flooredLiFantasyPrimeCount_sub_li_lt_one (x : ℝ) :
    |flooredLiFantasyPrimeCount x - vfMidLogarithmicIntegralFromTwo x| < 1 := by
  have hfloor :
      flooredLiFantasyPrimeCount x ≤ vfMidLogarithmicIntegralFromTwo x := by
    change
      (((⌊vfMidLogarithmicIntegralFromTwo x⌋ : ℤ) : ℝ)) ≤
        vfMidLogarithmicIntegralFromTwo x
    exact Int.floor_le _
  have hnext :
      vfMidLogarithmicIntegralFromTwo x <
        flooredLiFantasyPrimeCount x + 1 := by
    change
      vfMidLogarithmicIntegralFromTwo x <
        (((⌊vfMidLogarithmicIntegralFromTwo x⌋ : ℤ) : ℝ)) + 1
    exact Int.lt_floor_add_one _
  rw [abs_lt]
  constructor <;> linarith

/-- Counterfactual identification of actual prime count with the floored-Li
integer-valued staircase. -/
def FlooredLiFantasyIdentification : Prop :=
  ∀ x : ℝ, 4 ≤ x →
    vfMidPrimeCount x = flooredLiFantasyPrimeCount x

/-- The floored-Li fantasy has O(1) prime-minus-Li error, hence automatically
satisfies the much weaker von-Koch scale. -/
theorem primeLiVonKochBounded_of_flooredLiFantasy
    (h : FlooredLiFantasyIdentification) :
    PrimeLiVonKochBoundedStatement := by
  let C : ℝ := 1 / Real.log 4
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro x hx
  have hid := h x hx
  have herr :
      |vfMidPrimeLiError x| < 1 := by
    unfold vfMidPrimeLiError
    rw [hid]
    exact abs_flooredLiFantasyPrimeCount_sub_li_lt_one x
  have hweight := two_log_four_le_sqrt_mul_log hx
  have htwo :
      (2 : ℝ) ≤ C * Real.sqrt x * Real.log x := by
    calc
      (2 : ℝ) = C * (2 * Real.log 4) := by
        dsimp [C]
        field_simp [hlog4.ne']
      _ ≤ C * (Real.sqrt x * Real.log x) :=
        mul_le_mul_of_nonneg_left hweight (by dsimp [C]; positivity)
      _ = C * Real.sqrt x * Real.log x := by ring
  exact (le_of_lt herr).trans (by linarith)

/-- Fantasy closure 2: flooring Li still closes the classical von-Koch/RH
consumer, with a uniform O(1) discrepancy from Li. -/
theorem riemannHypothesis_of_flooredLiFantasy
    (criterion : ClassicalVonKochRHCriterion)
    (h : FlooredLiFantasyIdentification) :
    VFMidRiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (primeLiVonKochBounded_of_flooredLiFantasy h)

/-! ## 3. VF-mid fractional cluster fantasy -/

/-- Counterfactual identification of the actual square-endpoint prime count
with the exact cumulative VF fractional-prime cluster. -/
def VFMidFractionalClusterFantasyIdentification : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    vfMidPrimeCount ((R : ℝ) ^ 2) =
      vfMidFractionalPrimeClusterMass R

/-- Under exact fractional-cluster identification, the square-endpoint
prime-minus-VF error is identically zero. -/
theorem vfMidSquareEndpointVonKochBounded_of_fractionalClusterFantasy
    (h : VFMidFractionalClusterFantasyIdentification) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  refine ⟨0, le_rfl, ?_⟩
  intro R hR
  have hid := h R hR
  unfold vfMidPrimeError
  rw [hid, vfMidFractionalPrimeClusterMass_eq_vfMid_sq R hR]
  simp

/-- Fantasy closure 3: the exact VF fractional-prime cluster at square
endpoints closes RH through the already-compiled square-endpoint bridge. -/
theorem riemannHypothesis_of_fractionalClusterFantasy
    (criterion : ClassicalVonKochRHCriterion)
    (h : VFMidFractionalClusterFantasyIdentification) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_fractionalClusterFantasy h)

/-! ## 4. Literal midpoint-linear VF fantasy -/

/-- Every completed VF band mass is nonnegative. -/
theorem vfMidBandMass_nonneg {R : ℕ} (hR : 2 ≤ R) :
    0 ≤ vfMidBandMass R := by
  unfold vfMidBandMass
  have hm : 1 < vfMidBandMidpoint R := by
    unfold vfMidBandMidpoint
    have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith
  exact div_nonneg (by positivity) (Real.log_pos hm).le

/-- Crude universal upper envelope for one VF band mass. -/
theorem vfMidBandMass_le_logFour {R : ℕ} (hR : 2 ≤ R) :
    vfMidBandMass R ≤
      (2 * (R : ℝ) + 1) / Real.log 4 := by
  unfold vfMidBandMass
  have hm4 : (4 : ℝ) ≤ vfMidBandMidpoint R := by
    unfold vfMidBandMidpoint
    have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith
  have hlog :
      Real.log 4 ≤ Real.log (vfMidBandMidpoint R) :=
    Real.log_le_log (by norm_num) hm4
  exact div_le_div_of_nonneg_left
    (by positivity) (Real.log_pos (by norm_num)) hlog

/-- At the square between two consecutive midpoint anchors, the affine segment
differs from the completed VF mass by only O(R). -/
theorem abs_vfMidMidpointLinearSegment_nextSquare_sub_finishedMass_le
    {S : ℕ} (hS : 2 ≤ S) :
    |vfMidMidpointLinearSegment S ((((S + 1 : ℕ) : ℝ) ^ 2)) -
        vfMidFinishedMass (S + 1)| ≤
      (4 / Real.log 4) * ((S + 1 : ℕ) : ℝ) := by
  let x : ℝ := (((S + 1 : ℕ) : ℝ) ^ 2)
  let t : ℝ :=
    (x - vfMidBandMidpoint S) /
      (vfMidBandMidpoint (S + 1) - vfMidBandMidpoint S)
  have hden : 0 <
      vfMidBandMidpoint (S + 1) - vfMidBandMidpoint S :=
    vfMidBandMidpoint_succ_sub_pos S
  have hleft : vfMidBandMidpoint S ≤ x := by
    dsimp [x]
    unfold vfMidBandMidpoint
    push_cast
    nlinarith
  have hright : x ≤ vfMidBandMidpoint (S + 1) := by
    dsimp [x]
    unfold vfMidBandMidpoint
    push_cast
    nlinarith
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (sub_nonneg.mpr hleft) hden.le
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ hden).2
    linarith
  have hVS0 : 0 ≤ vfMidBandMass S :=
    vfMidBandMass_nonneg hS
  have hVN0 : 0 ≤ vfMidBandMass (S + 1) :=
    vfMidBandMass_nonneg (by omega)
  have hlin :
      vfMidMidpointLinearSegment S x -
          vfMidFinishedMass (S + 1) =
        -vfMidBandMass S / 2 +
          t * ((vfMidBandMass S + vfMidBandMass (S + 1)) / 2) := by
    dsimp [t]
    unfold vfMidMidpointLinearSegment vfMidMidpointAnchor
    rw [vfMidFinishedMass_succ hS]
    ring
  have hhalfS : 0 ≤ vfMidBandMass S / 2 := by positivity
  have hhalfSum :
      0 ≤ (vfMidBandMass S + vfMidBandMass (S + 1)) / 2 := by
    positivity
  have hnegHalfS : -vfMidBandMass S / 2 ≤ 0 := by
    nlinarith
  have habsHalfS :
      |-vfMidBandMass S / 2| = vfMidBandMass S / 2 := by
    rw [abs_of_nonpos hnegHalfS]
    ring
  have hprod0 :
      0 ≤ t * ((vfMidBandMass S + vfMidBandMass (S + 1)) / 2) :=
    mul_nonneg ht0 hhalfSum
  have habsProd :
      |t * ((vfMidBandMass S + vfMidBandMass (S + 1)) / 2)| =
        t * ((vfMidBandMass S + vfMidBandMass (S + 1)) / 2) :=
    abs_of_nonneg hprod0
  have hVS := vfMidBandMass_le_logFour hS
  have hVN := vfMidBandMass_le_logFour (R := S + 1) (by omega)
  change
    |vfMidMidpointLinearSegment S x - vfMidFinishedMass (S + 1)| ≤ _
  rw [hlin]
  calc
    |-vfMidBandMass S / 2 +
        t * ((vfMidBandMass S + vfMidBandMass (S + 1)) / 2)|
        ≤ |-vfMidBandMass S / 2| +
            |t * ((vfMidBandMass S + vfMidBandMass (S + 1)) / 2)| :=
      abs_add_le _ _
    _ = vfMidBandMass S / 2 +
          t * ((vfMidBandMass S + vfMidBandMass (S + 1)) / 2) := by
      rw [habsHalfS, habsProd]
    _ ≤ vfMidBandMass S / 2 +
          ((vfMidBandMass S + vfMidBandMass (S + 1)) / 2) := by
      have hm :=
        mul_le_mul_of_nonneg_right ht1 hhalfSum
      nlinarith
    _ = vfMidBandMass S + vfMidBandMass (S + 1) / 2 := by ring
    _ ≤ vfMidBandMass S + vfMidBandMass (S + 1) := by
      linarith
    _ ≤ (2 * (S : ℝ) + 1) / Real.log 4 +
          (2 * ((S + 1 : ℕ) : ℝ) + 1) / Real.log 4 :=
      add_le_add hVS hVN
    _ = (4 / Real.log 4) * ((S + 1 : ℕ) : ℝ) := by
      push_cast
      ring

/-- At every square endpoint the literal midpoint-linear presentation differs
from the original VF-mid path by at most a fixed linear-in-R budget. -/
theorem abs_vfMidMidpointLinear_sq_sub_vfMid_le
    (R : ℕ) (hR : 2 ≤ R) :
    |vfMidMidpointLinear ((R : ℝ) ^ 2) -
        vfMid ((R : ℝ) ^ 2)| ≤
      (4 / Real.log 4) * (R : ℝ) := by
  by_cases hR2 : R = 2
  · subst R
    have hlt : (4 : ℝ) < vfMidBandMidpoint 2 := by
      norm_num [vfMidBandMidpoint]
    have hsquare : (((2 : ℕ) : ℝ) ^ 2) = 4 := by
      norm_num
    rw [hsquare, vfMidMidpointLinear_eq_vfMid_of_lt_firstMidpoint hlt]
    positivity
  · have hR3 : 3 ≤ R := by omega
    have hfirst :
        vfMidBandMidpoint 2 ≤ (R : ℝ) ^ 2 := by
      unfold vfMidBandMidpoint
      have hRreal : (3 : ℝ) ≤ R := by exact_mod_cast hR3
      norm_num
      nlinarith
    have hbefore :
        (R : ℝ) ^ 2 <
          vfMidBandMidpoint (vfMidSquareRootIndex ((R : ℝ) ^ 2)) := by
      rw [vfMidSquareRootIndex_sq]
      unfold vfMidBandMidpoint
      have hRnonneg : (0 : ℝ) ≤ R := by positivity
      nlinarith
    rw [vfMidMidpointLinear_eq_leftSegment hfirst hbefore,
      vfMidSquareRootIndex_sq, vfMid_sq hR]
    have hS : 2 ≤ R - 1 := by omega
    have hseg :=
      abs_vfMidMidpointLinearSegment_nextSquare_sub_finishedMass_le
        (S := R - 1) hS
    have hpred : R - 1 + 1 = R := by omega
    simpa [hpred] using hseg

/-- Counterfactual identification of the actual prime-count staircase with the
literal all-real midpoint-to-midpoint VF interpolation. -/
def VFMidMidpointLinearFantasyIdentification : Prop :=
  ∀ x : ℝ, 4 ≤ x →
    vfMidPrimeCount x = vfMidMidpointLinear x

/-- The midpoint-linear fantasy supplies the square-endpoint von-Koch bound.
The mismatch between the affine midpoint presentation and the original VF
square endpoint is only O(R), which is strictly inside O(R log R). -/
theorem vfMidSquareEndpointVonKochBounded_of_midpointLinearFantasy
    (h : VFMidMidpointLinearFantasyIdentification) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  let C : ℝ := (4 / Real.log 4) / Real.log 2
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro R hR
  have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have h4 : (4 : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
  have hid := h ((R : ℝ) ^ 2) h4
  have herr :
      vfMidPrimeError ((R : ℝ) ^ 2) =
        vfMidMidpointLinear ((R : ℝ) ^ 2) -
          vfMid ((R : ℝ) ^ 2) := by
    unfold vfMidPrimeError
    rw [hid]
  rw [herr]
  have hlocal := abs_vfMidMidpointLinear_sq_sub_vfMid_le R hR
  have hlogR : Real.log 2 ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by norm_num) hRreal
  calc
    |vfMidMidpointLinear ((R : ℝ) ^ 2) - vfMid ((R : ℝ) ^ 2)|
        ≤ (4 / Real.log 4) * (R : ℝ) := hlocal
    _ = C * (R : ℝ) * Real.log 2 := by
      dsimp [C]
      field_simp [hlog2.ne']
    _ ≤ C * (R : ℝ) * Real.log R := by
      exact mul_le_mul_of_nonneg_left hlogR (by
        dsimp [C]
        positivity)

/-- Fantasy closure 4: the literal midpoint-to-midpoint VF interpolation,
identified with the actual prime-count staircase, closes RH. -/
theorem riemannHypothesis_of_midpointLinearFantasy
    (criterion : ClassicalVonKochRHCriterion)
    (h : VFMidMidpointLinearFantasyIdentification) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_midpointLinearFantasy h)

/-! ## One theorem collecting all four counterfactual closures -/

/-- All four fantasy identifications individually close the same classical
von-Koch/RH consumer. -/
theorem fourFantasyPrimeModels_close_RH
    (criterion : ClassicalVonKochRHCriterion) :
    (ContinuousLiFantasyIdentification →
      VFMidRiemannHypothesisStatement) ∧
    (FlooredLiFantasyIdentification →
      VFMidRiemannHypothesisStatement) ∧
    (VFMidFractionalClusterFantasyIdentification →
      VFMidRiemannHypothesisStatement) ∧
    (VFMidMidpointLinearFantasyIdentification →
      VFMidRiemannHypothesisStatement) := by
  exact ⟨riemannHypothesis_of_continuousLiFantasy criterion,
    riemannHypothesis_of_flooredLiFantasy criterion,
    riemannHypothesis_of_fractionalClusterFantasy criterion,
    riemannHypothesis_of_midpointLinearFantasy criterion⟩

end RHLean.Analysis
