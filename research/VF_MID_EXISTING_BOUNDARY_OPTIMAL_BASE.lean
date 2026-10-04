import Mathlib
import «research.VF_MID_OPTIMAL_BASE_VON_KOCH_FAN»
import «research.VF_MID_SOLVED_FANTASY_CONE»
import «research.VF_MID_CORNER_CHANNEL»

/-!
# Existing fantasy boundaries in exact optimal-base coordinates

This file does not invent a new channel.  It applies the exact monotone map

  B_x(y) = exp (y * log x / x)

to fantasy boundaries that are already present and already proved RH-safe in
count space.

Two instantiations are recorded.

1. The normalized solved-fantasy radial interval
     VF(R^2) ± K R log R.
   Its optimal-base image is exactly equivalent to the existing radial cone,
   hence exactly equivalent to the square-endpoint von-Koch target.

2. The genuine widened outer-corner VF boundaries.  Their optimal-base image
   is pointwise equivalent to the existing outer-corner endpoint bracket and
   therefore feeds the already-compiled von-Koch/RH consumer.

Thus optimal-base containment is a lossless coordinate rewrite of the solved
fantasy geometry, not an additional approximation or cancellation hypothesis.
-/

noncomputable section

namespace RHLean.Analysis

/-! ## Existing normalized radial walls -/

/-- Lower count-space wall of the existing normalized solved-fantasy radial
interval. -/
def vfMidSolvedFantasyRadialLowerCount (K : ℝ) (R : ℕ) : ℝ :=
  vfMid ((R : ℝ) ^ 2) -
    K * (R : ℝ) * Real.log (R : ℝ)

/-- Upper count-space wall of the existing normalized solved-fantasy radial
interval. -/
def vfMidSolvedFantasyRadialUpperCount (K : ℝ) (R : ℕ) : ℝ :=
  vfMid ((R : ℝ) ^ 2) +
    K * (R : ℝ) * Real.log (R : ℝ)

/-- Exact optimal-base image of the lower radial wall. -/
def vfMidSolvedFantasyRadialLowerOptimalBase (K : ℝ) (R : ℕ) : ℝ :=
  optimalLogBaseValue
    (vfMidSolvedFantasyRadialLowerCount K R)
    ((R : ℝ) ^ 2)

/-- Exact optimal-base image of the upper radial wall. -/
def vfMidSolvedFantasyRadialUpperOptimalBase (K : ℝ) (R : ℕ) : ℝ :=
  optimalLogBaseValue
    (vfMidSolvedFantasyRadialUpperCount K R)
    ((R : ℝ) ^ 2)

/-- At each square endpoint, actual-prime optimal-base containment between the
two radial wall images is exactly the already-existing solved radial-cone
containment statement. -/
theorem actualPrimeOptimalBase_between_solvedRadialWalls_iff
    {K : ℝ} {R : ℕ} (hR : 2 ≤ R) :
    (vfMidSolvedFantasyRadialLowerOptimalBase K R ≤
        optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ∧
      optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ≤
        vfMidSolvedFantasyRadialUpperOptimalBase K R) ↔
      VFMidSolvedFantasyRadialConeAt K R
        (vfMidPrimeCount ((R : ℝ) ^ 2)) := by
  have hRgt1 : (1 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 1 < R by omega)
  have hx :
      (1 : ℝ) < (R : ℝ) ^ 2 := by
    nlinarith
  rw [vfMidSolvedFantasyRadialConeAt_iff hR]
  unfold vfMidSolvedFantasyRadialLowerOptimalBase
    vfMidSolvedFantasyRadialUpperOptimalBase
  rw [optimalLogBase_eq_value]
  rw [optimalLogBaseValue_between_iff hx]
  unfold vfMidSolvedFantasyRadialLowerCount
    vfMidSolvedFantasyRadialUpperCount
    vfMidPrimeError
  rw [abs_le]
  constructor
  · rintro ⟨hlo, hup⟩
    constructor <;> linarith
  · rintro ⟨hlo, hup⟩
    constructor <;> linarith

/-- Global optimal-base formulation of the existing solved radial cone. -/
def ActualPrimeOptimalBaseContainedInSolvedFantasyRadialWallsStatement : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ R : ℕ, 2 ≤ R →
      vfMidSolvedFantasyRadialLowerOptimalBase K R ≤
          optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ∧
        optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ≤
          vfMidSolvedFantasyRadialUpperOptimalBase K R

/-- The new optimal-base statement is literally the old radial-cone statement
under the exact order-preserving coordinate map. -/
theorem actualPrimeOptimalBaseContainedInSolvedFantasyRadialWalls_iff :
    ActualPrimeOptimalBaseContainedInSolvedFantasyRadialWallsStatement ↔
      ActualPrimeContainedInSolvedFantasyRadialConeStatement := by
  constructor
  · rintro ⟨K, hK, hbase⟩
    refine ⟨K, hK, ?_⟩
    intro R hR
    exact
      (actualPrimeOptimalBase_between_solvedRadialWalls_iff hR).1
        (hbase R hR)
  · rintro ⟨K, hK, hcone⟩
    refine ⟨K, hK, ?_⟩
    intro R hR
    exact
      (actualPrimeOptimalBase_between_solvedRadialWalls_iff hR).2
        (hcone R hR)

/-- Therefore the existing radial optimal-base containment is exactly the
square-endpoint von-Koch arithmetic target. -/
theorem actualPrimeOptimalBaseContainedInSolvedFantasyRadialWalls_iff_vonKoch :
    ActualPrimeOptimalBaseContainedInSolvedFantasyRadialWallsStatement ↔
      VFMidSquareEndpointVonKochBoundedStatement := by
  rw [actualPrimeOptimalBaseContainedInSolvedFantasyRadialWalls_iff,
    actualPrimeContainedInSolvedFantasyRadialCone_iff]

/-! ## Existing widened outer-corner walls -/

/-- Exact optimal-base image of the already-defined lower outer VF corner. -/
def vfMidOuterLowerCornerOptimalBase (A : ℝ) (R : ℕ) : ℝ :=
  optimalLogBaseValue
    (vfMidOuterLowerCorner A R)
    ((R : ℝ) ^ 2)

/-- Exact optimal-base image of the already-defined upper outer VF corner. -/
def vfMidOuterUpperCornerOptimalBase (A : ℝ) (R : ℕ) : ℝ :=
  optimalLogBaseValue
    (vfMidOuterUpperCorner A R)
    ((R : ℝ) ^ 2)

/-- Pointwise optimal-base containment between the existing outer corners is
exactly the existing count-space outer-corner bracket. -/
theorem actualPrimeOptimalBase_between_outerCorners_iff
    {A : ℝ} {R : ℕ} (hR : 4 ≤ R) :
    (vfMidOuterLowerCornerOptimalBase A R ≤
        optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ∧
      optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ≤
        vfMidOuterUpperCornerOptimalBase A R) ↔
    (vfMidOuterLowerCorner A R ≤
        (Nat.primeCounting (R ^ 2) : ℝ) ∧
      (Nat.primeCounting (R ^ 2) : ℝ) ≤
        vfMidOuterUpperCorner A R) := by
  have hRgt1 : (1 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 1 < R by omega)
  have hx :
      (1 : ℝ) < (R : ℝ) ^ 2 := by
    nlinarith
  unfold vfMidOuterLowerCornerOptimalBase
    vfMidOuterUpperCornerOptimalBase
  rw [optimalLogBase_eq_value]
  rw [optimalLogBaseValue_between_iff hx]
  simp only [vfMidPrimeCount_sq_exact]

/-- Global optimal-base image of the existing widened outer-corner endpoint
bracket. -/
def VFMidActualPrimeOptimalBaseOuterCornerBracket (A : ℝ) : Prop :=
  ∀ R : ℕ, 4 ≤ R →
    vfMidOuterLowerCornerOptimalBase A R ≤
        optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ∧
      optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ≤
        vfMidOuterUpperCornerOptimalBase A R

/-- The optimal-base outer-corner bracket is exactly the existing count-space
outer-corner endpoint bracket. -/
theorem actualPrimeOptimalBaseOuterCornerBracket_iff
    {A : ℝ} :
    VFMidActualPrimeOptimalBaseOuterCornerBracket A ↔
      VFMidOuterCornerEndpointBracket A := by
  constructor
  · intro hbase R hR
    exact
      (actualPrimeOptimalBase_between_outerCorners_iff hR).1
        (hbase R hR)
  · intro hcorner R hR
    exact
      (actualPrimeOptimalBase_between_outerCorners_iff hR).2
        (hcorner R hR)

/-- No new analytic work is required after transporting the outer corners:
their existing RH-scale theorem applies verbatim. -/
theorem vfMidSquareEndpointVonKochBounded_of_actualPrimeOptimalBaseOuterCornerBracket
    {A : ℝ} (hA : 0 ≤ A)
    (hbase : VFMidActualPrimeOptimalBaseOuterCornerBracket A) :
    VFMidSquareEndpointVonKochBoundedStatement :=
  vfMidSquareEndpointVonKochBounded_of_outerCornerBracket hA
    (actualPrimeOptimalBaseOuterCornerBracket_iff.mp hbase)

/-- Existing RH consumer in the optimal-base outer-corner coordinate. -/
theorem riemannHypothesis_of_actualPrimeOptimalBaseOuterCornerBracket
    (criterion : ClassicalVonKochRHCriterion)
    {A : ℝ} (hA : 0 ≤ A)
    (hbase : VFMidActualPrimeOptimalBaseOuterCornerBracket A) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_actualPrimeOptimalBaseOuterCornerBracket
      hA hbase)

end RHLean.Analysis
