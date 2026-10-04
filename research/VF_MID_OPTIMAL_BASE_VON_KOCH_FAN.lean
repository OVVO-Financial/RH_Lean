import Mathlib
import RHLean.Analysis.OptimalLogBase
import «research.VF_MID_SOLVED_FANTASY_CONE»
import «research.VF_MID_CORNER_CHANNEL»

/-!
# Optimal-base image of the already-solved VF fantasy boundaries

For fixed x > 1, send any count value y to its exact optimal logarithmic base

  B_x(y) = exp (y * log x / x).

This map is strictly order preserving and reconstructs y exactly through
x / log_b x.  Therefore every count-space fantasy boundary already proved
RH-safe has an exact optimal-base image, and containment between the base
images is equivalent to containment between the original count boundaries.

The two main instantiations here are:

* the normalized solved-fantasy radial cone, whose count-space walls are
  VF(R^2) +/- K R log R;
* the genuine widened VF outer-corner walls already formalized in
  VF_MID_CORNER_CHANNEL.

No new prime-distribution hypothesis is introduced.  The actual prime optimal
base is simply the image of the exact prime-count endpoint.
-/

noncomputable section

namespace RHLean.Analysis

/-- Scalar optimal-base image of one count value at cutoff x. -/
def optimalBaseImage (x y : ℝ) : ℝ :=
  Real.exp (y * Real.log x / x)

/-- The function-valued optimal base already in the repository is exactly the
scalar image of its value at x. -/
@[simp] theorem optimalLogBase_eq_optimalBaseImage
    (P : ℝ → ℝ) (x : ℝ) :
    optimalLogBase P x = optimalBaseImage x (P x) := by
  rfl

/-- Exact inverse reconstruction from the scalar optimal-base image. -/
theorem optimalBaseImage_reconstructs
    {x y : ℝ} (hx : x ≠ 0) (hlogx : Real.log x ≠ 0) :
    x * Real.log (optimalBaseImage x y) / Real.log x = y := by
  simp [optimalBaseImage]
  field_simp [hx, hlogx]

/-- At fixed x > 1, optimal-base coordinates preserve and reflect order. -/
theorem optimalBaseImage_le_iff
    {x a b : ℝ} (hx : 1 < x) :
    optimalBaseImage x a ≤ optimalBaseImage x b ↔ a ≤ b := by
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  unfold optimalBaseImage
  rw [Real.exp_le_exp]
  constructor
  · intro h
    have hmul : a * Real.log x ≤ b * Real.log x :=
      (div_le_div_iff_of_pos_right hx0).mp h
    exact (mul_le_mul_right hlog).mp hmul
  · intro h
    have hmul : a * Real.log x ≤ b * Real.log x :=
      (mul_le_mul_right hlog).mpr h
    exact (div_le_div_iff_of_pos_right hx0).mpr hmul

/-- A two-sided count bracket is exactly the same two-sided optimal-base
bracket. -/
theorem optimalBaseImage_bracket_iff
    {x lower y upper : ℝ} (hx : 1 < x) :
    (optimalBaseImage x lower ≤ optimalBaseImage x y ∧
        optimalBaseImage x y ≤ optimalBaseImage x upper) ↔
      (lower ≤ y ∧ y ≤ upper) := by
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨(optimalBaseImage_le_iff hx).mp hl,
      (optimalBaseImage_le_iff hx).mp hu⟩
  · rintro ⟨hl, hu⟩
    exact ⟨(optimalBaseImage_le_iff hx).mpr hl,
      (optimalBaseImage_le_iff hx).mpr hu⟩

/-- Exact optimal base of the honest prime-count staircase. -/
def vfMidActualPrimeOptimalBase (x : ℝ) : ℝ :=
  optimalBaseImage x (vfMidPrimeCount x)

@[simp] theorem vfMidActualPrimeOptimalBase_eq_optimalLogBase
    (x : ℝ) :
    vfMidActualPrimeOptimalBase x =
      optimalLogBase vfMidPrimeCount x := by
  rfl

/-! ## Existing solved radial cone in optimal-base coordinates -/

/-- Lower count-space wall of the already-solved normalized radial cone. -/
def vfMidSolvedFantasyRadialLowerCount (K : ℝ) (R : ℕ) : ℝ :=
  vfMid ((R : ℝ) ^ 2) -
    K * (R : ℝ) * Real.log (R : ℝ)

/-- Upper count-space wall of the already-solved normalized radial cone. -/
def vfMidSolvedFantasyRadialUpperCount (K : ℝ) (R : ℕ) : ℝ :=
  vfMid ((R : ℝ) ^ 2) +
    K * (R : ℝ) * Real.log (R : ℝ)

/-- Optimal-base image of the lower solved radial wall. -/
def vfMidSolvedFantasyRadialLowerOptimalBase
    (K : ℝ) (R : ℕ) : ℝ :=
  optimalBaseImage ((R : ℝ) ^ 2)
    (vfMidSolvedFantasyRadialLowerCount K R)

/-- Optimal-base image of the upper solved radial wall. -/
def vfMidSolvedFantasyRadialUpperOptimalBase
    (K : ℝ) (R : ℕ) : ℝ :=
  optimalBaseImage ((R : ℝ) ^ 2)
    (vfMidSolvedFantasyRadialUpperCount K R)

/-- The optimal-base walls reconstruct exactly to the existing count-space
radial walls. -/
theorem vfMidSolvedFantasyRadialLowerOptimalBase_reconstructs
    (K : ℝ) {R : ℕ} (hR : 2 ≤ R) :
    ((R : ℝ) ^ 2) *
        Real.log (vfMidSolvedFantasyRadialLowerOptimalBase K R) /
          Real.log ((R : ℝ) ^ 2) =
      vfMidSolvedFantasyRadialLowerCount K R := by
  have hx : ((R : ℝ) ^ 2) ≠ 0 := by positivity
  have hlog : Real.log ((R : ℝ) ^ 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    nlinarith
  exact optimalBaseImage_reconstructs hx hlog

theorem vfMidSolvedFantasyRadialUpperOptimalBase_reconstructs
    (K : ℝ) {R : ℕ} (hR : 2 ≤ R) :
    ((R : ℝ) ^ 2) *
        Real.log (vfMidSolvedFantasyRadialUpperOptimalBase K R) /
          Real.log ((R : ℝ) ^ 2) =
      vfMidSolvedFantasyRadialUpperCount K R := by
  have hx : ((R : ℝ) ^ 2) ≠ 0 := by positivity
  have hlog : Real.log ((R : ℝ) ^ 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    nlinarith
  exact optimalBaseImage_reconstructs hx hlog

/-- At every square endpoint, actual optimal-base containment between the two
radial-wall bases is exactly membership of the already-solved radial cone. -/
theorem vfMidActualPrimeOptimalBase_radialBracket_iff
    {K : ℝ} {R : ℕ} (hR : 2 ≤ R) :
    (vfMidSolvedFantasyRadialLowerOptimalBase K R ≤
          vfMidActualPrimeOptimalBase ((R : ℝ) ^ 2) ∧
        vfMidActualPrimeOptimalBase ((R : ℝ) ^ 2) ≤
          vfMidSolvedFantasyRadialUpperOptimalBase K R) ↔
      VFMidSolvedFantasyRadialConeAt K R
        (vfMidPrimeCount ((R : ℝ) ^ 2)) := by
  have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hx1 : (1 : ℝ) < (R : ℝ) ^ 2 := by nlinarith
  rw [vfMidSolvedFantasyRadialConeAt_iff hR]
  unfold vfMidSolvedFantasyRadialLowerOptimalBase
    vfMidSolvedFantasyRadialUpperOptimalBase
    vfMidActualPrimeOptimalBase
  rw [optimalBaseImage_bracket_iff hx1]
  unfold vfMidSolvedFantasyRadialLowerCount
    vfMidSolvedFantasyRadialUpperCount
  rw [abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Uniform optimal-base containment in the images of the solved radial walls. -/
def ActualPrimeOptimalBaseContainedInSolvedFantasyRadialConeStatement : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ R : ℕ, 2 ≤ R →
      vfMidSolvedFantasyRadialLowerOptimalBase K R ≤
          vfMidActualPrimeOptimalBase ((R : ℝ) ^ 2) ∧
        vfMidActualPrimeOptimalBase ((R : ℝ) ^ 2) ≤
          vfMidSolvedFantasyRadialUpperOptimalBase K R

/-- The optimal-base formulation is exactly the existing solved radial-cone
containment statement. -/
theorem actualPrimeOptimalBaseContainedInSolvedFantasyRadialCone_iff :
    ActualPrimeOptimalBaseContainedInSolvedFantasyRadialConeStatement ↔
      ActualPrimeContainedInSolvedFantasyRadialConeStatement := by
  constructor
  · rintro ⟨K, hK, hbase⟩
    refine ⟨K, hK, ?_⟩
    intro R hR
    exact (vfMidActualPrimeOptimalBase_radialBracket_iff hR).mp
      (hbase R hR)
  · rintro ⟨K, hK, hcone⟩
    refine ⟨K, hK, ?_⟩
    intro R hR
    exact (vfMidActualPrimeOptimalBase_radialBracket_iff hR).mpr
      (hcone R hR)

/-- Therefore the optimal-base radial statement is exactly the direct
square-endpoint von-Koch target. -/
theorem actualPrimeOptimalBaseContainedInSolvedFantasyRadialCone_iff_vonKoch :
    ActualPrimeOptimalBaseContainedInSolvedFantasyRadialConeStatement ↔
      VFMidSquareEndpointVonKochBoundedStatement := by
  rw [actualPrimeOptimalBaseContainedInSolvedFantasyRadialCone_iff,
    actualPrimeContainedInSolvedFantasyRadialCone_iff]

/-- Existing RH consumer, now fed by the exact optimal-base image of the
already-solved radial fantasy boundaries. -/
theorem riemannHypothesis_of_actualPrimeOptimalBaseContainedInSolvedFantasyRadialCone
    (criterion : ClassicalVonKochRHCriterion)
    (hbase :
      ActualPrimeOptimalBaseContainedInSolvedFantasyRadialConeStatement) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (actualPrimeOptimalBaseContainedInSolvedFantasyRadialCone_iff_vonKoch.mp
      hbase)

/-! ## Existing genuine VF outer-corner walls in optimal-base coordinates -/

/-- Optimal-base image of the already-formalized lower outer VF corner. -/
def vfMidOuterLowerCornerOptimalBase (A : ℝ) (R : ℕ) : ℝ :=
  optimalBaseImage ((R : ℝ) ^ 2) (vfMidOuterLowerCorner A R)

/-- Optimal-base image of the already-formalized upper outer VF corner. -/
def vfMidOuterUpperCornerOptimalBase (A : ℝ) (R : ℕ) : ℝ :=
  optimalBaseImage ((R : ℝ) ^ 2) (vfMidOuterUpperCorner A R)

/-- Pointwise optimal-base bracketing by the genuine outer VF corners is
exactly the existing count-space outer-corner bracket. -/
theorem vfMidActualPrimeOptimalBase_outerCornerBracket_iff
    {A : ℝ} {R : ℕ} (hR : 4 ≤ R) :
    (vfMidOuterLowerCornerOptimalBase A R ≤
          vfMidActualPrimeOptimalBase ((R : ℝ) ^ 2) ∧
        vfMidActualPrimeOptimalBase ((R : ℝ) ^ 2) ≤
          vfMidOuterUpperCornerOptimalBase A R) ↔
      (vfMidOuterLowerCorner A R ≤
          (Nat.primeCounting (R ^ 2) : ℝ) ∧
        (Nat.primeCounting (R ^ 2) : ℝ) ≤
          vfMidOuterUpperCorner A R) := by
  have hRreal : (4 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hx1 : (1 : ℝ) < (R : ℝ) ^ 2 := by nlinarith
  unfold vfMidOuterLowerCornerOptimalBase
    vfMidOuterUpperCornerOptimalBase
    vfMidActualPrimeOptimalBase
  rw [optimalBaseImage_bracket_iff hx1]
  rw [vfMidPrimeCount_sq_exact R]

/-- Uniform optimal-base version of the existing outer-corner endpoint
bracket. -/
def ActualPrimeOptimalBaseContainedInOuterCornerStatement (A : ℝ) : Prop :=
  ∀ R : ℕ, 4 ≤ R →
    vfMidOuterLowerCornerOptimalBase A R ≤
        vfMidActualPrimeOptimalBase ((R : ℝ) ^ 2) ∧
      vfMidActualPrimeOptimalBase ((R : ℝ) ^ 2) ≤
        vfMidOuterUpperCornerOptimalBase A R

/-- The optimal-base outer-corner statement is exactly the already-existing
count-space outer-corner statement. -/
theorem actualPrimeOptimalBaseContainedInOuterCorner_iff
    (A : ℝ) :
    ActualPrimeOptimalBaseContainedInOuterCornerStatement A ↔
      VFMidOuterCornerEndpointBracket A := by
  constructor
  · intro h R hR
    exact (vfMidActualPrimeOptimalBase_outerCornerBracket_iff hR).mp
      (h R hR)
  · intro h R hR
    exact (vfMidActualPrimeOptimalBase_outerCornerBracket_iff hR).mpr
      (h R hR)

/-- Any nonnegative canonical outer-corner schedule that traps the actual
optimal base inherits the already-proved square-endpoint von-Koch bound. -/
theorem vfMidSquareEndpointVonKochBounded_of_actualPrimeOptimalBaseOuterCorners
    {A : ℝ} (hA : 0 ≤ A)
    (hbase : ActualPrimeOptimalBaseContainedInOuterCornerStatement A) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  apply vfMidSquareEndpointVonKochBounded_of_fromFour
  apply vfMidSquareEndpointVonKochBoundedFromFour_of_outerCornerBracket hA
  exact (actualPrimeOptimalBaseContainedInOuterCorner_iff A).mp hbase

/-- And therefore the existing RH consumer closes directly from optimal-base
containment between the genuine outer-corner fantasy boundaries. -/
theorem riemannHypothesis_of_actualPrimeOptimalBaseOuterCorners
    (criterion : ClassicalVonKochRHCriterion)
    {A : ℝ} (hA : 0 ≤ A)
    (hbase : ActualPrimeOptimalBaseContainedInOuterCornerStatement A) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_actualPrimeOptimalBaseOuterCorners
      hA hbase)

end RHLean.Analysis
