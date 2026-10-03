import Mathlib
import RHLean.Analysis.OptimalLogBase
import «research.VF_MID_VON_KOCH_BRIDGE»

/-!
# Optimal-base von-Koch fantasy fan

The exact optimal-base coordinate of a counting function P is

  s_P(x) = P(x) * log(x) / x,
  b_P(x) = exp(s_P(x)).

For the deterministic VF midpoint reference, define the von-Koch-radius in
this logarithmic-base coordinate by

  rho_C(x) = C * sqrt(x) * log(x)^2 / x.

The full one-parameter fantasy fan is

  s_theta(x) = s_VF(x) + theta * rho_C(x),   -1 <= theta <= 1,
  b_theta(x) = exp(s_theta(x)).

Reconstruction by x / log_b(x) gives the exact count

  VF(x) + theta * C * sqrt(x) * log(x).

Thus every member of the fan is automatically inside the VF von-Koch tube.

The second half packages the actual-prime containment statement in the same
coordinate.  If the exact optimal base of the real prime-count staircase lies
between the two fan walls for every x >= 4, then the native VF von-Koch bound
follows immediately.  The existing unconditional VF/Li quadrature theorem then
transfers this to the classical prime-minus-Li von-Koch statement and the
repository's RH consumer.

No assertion that the actual prime optimal base is contained in the fan is
made here.  That containment is isolated as the sole arithmetic hypothesis.
-/

noncomputable section

namespace RHLean.Analysis

/-- VF in the exact logarithmic optimal-base coordinate. -/
def vfMidOptimalLogCoordinate (x : ℝ) : ℝ :=
  normalizedCountingRatio vfMid x

/-- The von-Koch radius after moving the count-space width
C * sqrt(x) * log(x) into the normalized logarithmic-base coordinate. -/
def vfMidOptimalBaseVonKochRadius (C x : ℝ) : ℝ :=
  C * Real.sqrt x * (Real.log x) ^ 2 / x

/-- Logarithmic coordinate of one member of the continuous fantasy fan. -/
def vfMidOptimalBaseFanLogCoordinate (theta C x : ℝ) : ℝ :=
  vfMidOptimalLogCoordinate x +
    theta * vfMidOptimalBaseVonKochRadius C x

/-- Actual logarithmic base corresponding to one member of the fan. -/
def vfMidOptimalBaseFanBase (theta C x : ℝ) : ℝ :=
  Real.exp (vfMidOptimalBaseFanLogCoordinate theta C x)

/-- Reconstructed counting curve of one member of the fan. -/
def vfMidOptimalBaseFanCount (theta C x : ℝ) : ℝ :=
  x * Real.log (vfMidOptimalBaseFanBase theta C x) / Real.log x

/-- Lower optimal-base wall of the fan. -/
def vfMidOptimalBaseLowerWall (C x : ℝ) : ℝ :=
  Real.exp
    (vfMidOptimalLogCoordinate x -
      vfMidOptimalBaseVonKochRadius C x)

/-- Upper optimal-base wall of the fan. -/
def vfMidOptimalBaseUpperWall (C x : ℝ) : ℝ :=
  Real.exp
    (vfMidOptimalLogCoordinate x +
      vfMidOptimalBaseVonKochRadius C x)

@[simp] theorem log_vfMidOptimalBaseFanBase
    (theta C x : ℝ) :
    Real.log (vfMidOptimalBaseFanBase theta C x) =
      vfMidOptimalBaseFanLogCoordinate theta C x := by
  simp [vfMidOptimalBaseFanBase]

/-- The fan count really is the change-of-base reconstruction from its base. -/
theorem vfMidOptimalBaseFanCount_eq_logCoordinate
    (theta C x : ℝ) :
    vfMidOptimalBaseFanCount theta C x =
      x * vfMidOptimalBaseFanLogCoordinate theta C x / Real.log x := by
  simp [vfMidOptimalBaseFanCount]

/-- Exact count-space form of the fan.

The chosen radius is calibrated so that a displacement of one unit in theta
is exactly one von-Koch-width displacement in the count coordinate. -/
theorem vfMidOptimalBaseFanCount_eq_vfMid_add
    (theta C : ℝ) {x : ℝ} (hx : 4 ≤ x) :
    vfMidOptimalBaseFanCount theta C x =
      vfMid x + theta * C * Real.sqrt x * Real.log x := by
  have hxne : x ≠ 0 := by linarith
  have hlogne : Real.log x ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by linarith))
  rw [vfMidOptimalBaseFanCount_eq_logCoordinate]
  unfold vfMidOptimalBaseFanLogCoordinate
    vfMidOptimalLogCoordinate
    vfMidOptimalBaseVonKochRadius
    normalizedCountingRatio
  field_simp [hxne, hlogne]
  ring

/-- Every theta in [-1,1] reconstructs to a count inside the VF von-Koch tube. -/
theorem abs_vfMidOptimalBaseFanCount_sub_vfMid_le
    {theta C x : ℝ} (hC : 0 ≤ C)
    (htheta : -1 ≤ theta ∧ theta ≤ 1)
    (hx : 4 ≤ x) :
    |vfMidOptimalBaseFanCount theta C x - vfMid x| ≤
      C * Real.sqrt x * Real.log x := by
  have hlog0 : 0 ≤ Real.log x :=
    (Real.log_pos (by linarith : 1 < x)).le
  have habstheta : |theta| ≤ 1 := by
    rw [abs_le]
    exact htheta
  rw [vfMidOptimalBaseFanCount_eq_vfMid_add theta C hx]
  have hnonneg :
      0 ≤ C * Real.sqrt x * Real.log x := by positivity
  calc
    |vfMid x + theta * C * Real.sqrt x * Real.log x - vfMid x|
        = |theta| * (C * Real.sqrt x * Real.log x) := by
            rw [show
              vfMid x + theta * C * Real.sqrt x * Real.log x - vfMid x =
                theta * (C * Real.sqrt x * Real.log x) by ring,
              abs_mul, abs_of_nonneg hnonneg]
    _ ≤ 1 * (C * Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_right habstheta hnonneg
    _ = C * Real.sqrt x * Real.log x := by ring

/-- The two explicit wall bases are exactly the theta=-1 and theta=+1 fan
members. -/
theorem vfMidOptimalBaseFanBase_neg_one
    (C x : ℝ) :
    vfMidOptimalBaseFanBase (-1) C x =
      vfMidOptimalBaseLowerWall C x := by
  unfold vfMidOptimalBaseFanBase vfMidOptimalBaseFanLogCoordinate
    vfMidOptimalBaseLowerWall
  congr 1
  ring

theorem vfMidOptimalBaseFanBase_one
    (C x : ℝ) :
    vfMidOptimalBaseFanBase 1 C x =
      vfMidOptimalBaseUpperWall C x := by
  unfold vfMidOptimalBaseFanBase vfMidOptimalBaseFanLogCoordinate
    vfMidOptimalBaseUpperWall
  congr 1
  ring

/-- Every fantasy base with theta in [-1,1] lies between the two wall bases. -/
theorem vfMidOptimalBaseFanBase_between_walls
    {theta C x : ℝ} (hC : 0 ≤ C)
    (htheta : -1 ≤ theta ∧ theta ≤ 1)
    (hx : 0 ≤ x) :
    vfMidOptimalBaseLowerWall C x ≤
        vfMidOptimalBaseFanBase theta C x ∧
      vfMidOptimalBaseFanBase theta C x ≤
        vfMidOptimalBaseUpperWall C x := by
  have hrho0 :
      0 ≤ vfMidOptimalBaseVonKochRadius C x := by
    unfold vfMidOptimalBaseVonKochRadius
    positivity
  unfold vfMidOptimalBaseLowerWall vfMidOptimalBaseUpperWall
    vfMidOptimalBaseFanBase vfMidOptimalBaseFanLogCoordinate
  simp only [Real.exp_le_exp]
  constructor <;> nlinarith

/-- Exact actual-prime optimal base lies inside the moving von-Koch fan.

This is the arithmetic containment statement.  It is deliberately not proved
in this file. -/
def VFMidActualPrimeOptimalBaseContainedInVonKochFan (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ x : ℝ, 4 ≤ x →
      vfMidOptimalBaseLowerWall C x ≤
          optimalLogBase vfMidPrimeCount x ∧
        optimalLogBase vfMidPrimeCount x ≤
          vfMidOptimalBaseUpperWall C x

/-- Multiplying the normalized-coordinate displacement by x/log(x) recovers
the native prime-minus-VF discrepancy exactly. -/
theorem vfMidOptimalCoordinateDifference_scaled_eq_primeError
    {x : ℝ} (hx : 4 ≤ x) :
    (x / Real.log x) *
        (normalizedCountingRatio vfMidPrimeCount x -
          vfMidOptimalLogCoordinate x) =
      vfMidPrimeError x := by
  have hxne : x ≠ 0 := by linarith
  have hlogne : Real.log x ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by linarith))
  unfold normalizedCountingRatio vfMidOptimalLogCoordinate vfMidPrimeError
  field_simp [hxne, hlogne]
  ring

/-- The same scaling sends the base-coordinate fan radius exactly to the
von-Koch count-space radius. -/
theorem vfMidOptimalBaseVonKochRadius_scaled
    (C : ℝ) {x : ℝ} (hx : 4 ≤ x) :
    (x / Real.log x) *
        vfMidOptimalBaseVonKochRadius C x =
      C * Real.sqrt x * Real.log x := by
  have hxne : x ≠ 0 := by linarith
  have hlogne : Real.log x ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by linarith))
  unfold vfMidOptimalBaseVonKochRadius
  field_simp [hxne, hlogne]
  ring

/-- Base containment is already the native VF von-Koch estimate.

There is no cancellation or Mertens estimate after this point: the exponential
order converts the two base walls to a normalized-coordinate bracket, and the
preceding exact scaling identities convert that bracket to count space. -/
theorem vfMidPrimeError_le_of_optimalBaseFanContainment
    {C x : ℝ} (hC : 0 ≤ C) (hx : 4 ≤ x)
    (hbase :
      vfMidOptimalBaseLowerWall C x ≤
          optimalLogBase vfMidPrimeCount x ∧
        optimalLogBase vfMidPrimeCount x ≤
          vfMidOptimalBaseUpperWall C x) :
    |vfMidPrimeError x| ≤
      C * Real.sqrt x * Real.log x := by
  have hcoord :
      vfMidOptimalLogCoordinate x -
          vfMidOptimalBaseVonKochRadius C x ≤
        normalizedCountingRatio vfMidPrimeCount x ∧
      normalizedCountingRatio vfMidPrimeCount x ≤
        vfMidOptimalLogCoordinate x +
          vfMidOptimalBaseVonKochRadius C x := by
    simpa [vfMidOptimalBaseLowerWall, vfMidOptimalBaseUpperWall,
      optimalLogBase, vfMidOptimalLogCoordinate,
      normalizedCountingRatio] using hbase
  let scale : ℝ := x / Real.log x
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hdiff :
      -vfMidOptimalBaseVonKochRadius C x ≤
          normalizedCountingRatio vfMidPrimeCount x -
            vfMidOptimalLogCoordinate x ∧
        normalizedCountingRatio vfMidPrimeCount x -
            vfMidOptimalLogCoordinate x ≤
          vfMidOptimalBaseVonKochRadius C x := by
    constructor <;> linarith
  have hlo := mul_le_mul_of_nonneg_left hdiff.1 hscale0
  have hup := mul_le_mul_of_nonneg_left hdiff.2 hscale0
  have hprime :=
    vfMidOptimalCoordinateDifference_scaled_eq_primeError hx
  have hradius :=
    vfMidOptimalBaseVonKochRadius_scaled C hx
  change
    scale *
        (normalizedCountingRatio vfMidPrimeCount x -
          vfMidOptimalLogCoordinate x) =
      vfMidPrimeError x at hprime
  change
    scale * vfMidOptimalBaseVonKochRadius C x =
      C * Real.sqrt x * Real.log x at hradius
  have hlow :
      -(C * Real.sqrt x * Real.log x) ≤ vfMidPrimeError x := by
    calc
      -(C * Real.sqrt x * Real.log x) =
          scale * (-vfMidOptimalBaseVonKochRadius C x) := by
            rw [mul_neg, hradius]
      _ ≤ scale *
          (normalizedCountingRatio vfMidPrimeCount x -
            vfMidOptimalLogCoordinate x) := hlo
      _ = vfMidPrimeError x := hprime
  have hupp :
      vfMidPrimeError x ≤ C * Real.sqrt x * Real.log x := by
    calc
      vfMidPrimeError x =
          scale *
            (normalizedCountingRatio vfMidPrimeCount x -
              vfMidOptimalLogCoordinate x) := hprime.symm
      _ ≤ scale * vfMidOptimalBaseVonKochRadius C x := hup
      _ = C * Real.sqrt x * Real.log x := hradius
  exact (abs_le).2 ⟨hlow, hupp⟩

/-- Uniform optimal-base containment supplies the repository's sole native VF
von-Koch arithmetic target. -/
theorem vfMidVonKochBounded_of_actualPrimeOptimalBaseContained
    {C : ℝ}
    (hcontain : VFMidActualPrimeOptimalBaseContainedInVonKochFan C) :
    VFMidVonKochBoundedStatement := by
  rcases hcontain with ⟨hC, hfan⟩
  refine ⟨C, hC, ?_⟩
  intro x hx
  exact
    vfMidPrimeError_le_of_optimalBaseFanContainment
      hC hx (hfan x hx)

/-- The same containment therefore gives the classical prime-minus-Li
von-Koch bound through the already-proved deterministic VF/Li bridge. -/
theorem primeLiVonKochBounded_of_actualPrimeOptimalBaseContained
    {C : ℝ}
    (hcontain : VFMidActualPrimeOptimalBaseContainedInVonKochFan C) :
    PrimeLiVonKochBoundedStatement :=
  primeLiVonKochBounded_of_vfMid vfMidLiRootBounded
    (vfMidVonKochBounded_of_actualPrimeOptimalBaseContained hcontain)

/-- Final consumer: once the actual optimal base is trapped inside the moving
fan, the existing classical von-Koch interface closes RH. -/
theorem riemannHypothesis_of_actualPrimeOptimalBaseContained
    (criterion : ClassicalVonKochRHCriterion)
    {C : ℝ}
    (hcontain : VFMidActualPrimeOptimalBaseContainedInVonKochFan C) :
    VFMidRiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (primeLiVonKochBounded_of_actualPrimeOptimalBaseContained hcontain)

end RHLean.Analysis
