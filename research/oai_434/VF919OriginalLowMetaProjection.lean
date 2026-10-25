import Mathlib
import OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius

/-!
# J = 1: exact completed column weight and the finite projection obstruction

These lemmas isolate algebra that must be respected by the proposed
metaplectic residue test. They do NOT assert a metaplectic pole,
uniform analytic saving, improvement over 3/16, or RH.

See research/OAI_LOW_GAUSSIAN_J_ONE_METAPLECTIC_RESIDUE_AUDIT_20261025.md.
-/

namespace OAI

namespace VF919OriginalLowMetaProjection

open scoped BigOperators
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O

/-- At the ACTUAL completed ideal J=1, the cubeWeight factor is exactly 1,
    leaving the column's existing 1/sqrt(N(I)) amplitude. -/
theorem j_one_bare_completed_weight (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (T : ℝ) (I : Ideal O) :
    CompletedGauss.summand Ψ W T I (1 : Ideal O) =
      CompletedGauss.columnWeight Ψ I /
        (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        CompletedGauss.Vstar W ((Ideal.absNorm I : ℝ) / T) := by
  simp [CompletedGauss.summand]

/-- The pole of the Dirichlet series for an additional N(I)^(-1/2)
    column weight is at 5/6 - 1/2 = 1/3, IF the unweighted
    Dirichlet series has a pole at 5/6. This is arithmetic only. -/
theorem normalized_column_pole_exponent :
    (5 / 6 : ℚ) - 1 / 2 = 1 / 3 := by
  norm_num

/-- For any finite group-valued character, twisting by its inverse
    gives a NONZERO full projection. Thus a character having zero
    unweighted mean does not force its weighted metaplectic projection
    to vanish. No source character equality is assumed here. -/
theorem inverse_character_projection {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂ) :
    (∑ u : G, χ u * χ (u⁻¹)) = (Fintype.card G : ℂ) := by
  have h (u : G) : χ u * χ (u⁻¹) = 1 := by
    calc
      χ u * χ (u⁻¹) = χ (u * u⁻¹) := (map_mul χ u (u⁻¹)).symm
      _ = 1 := by simp
  simp [h]

/-- Concrete parity example of centering without cancellation under
    matching twist; the phenomenon is independent of analytic issues. -/
theorem centered_coefficients_can_have_nonzero_projection :
    ((1 : ℂ) + (-1) = 0) ∧
      ((1 : ℂ) * 1 + (-1) * (-1) = 2) := by
  constructor <;> ring

end VF919OriginalLowMetaProjection

end OAI
