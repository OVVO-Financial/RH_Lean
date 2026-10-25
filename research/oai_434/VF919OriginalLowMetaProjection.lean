import Mathlib
import OAI.NumberTheory.DirichletL.Detector.SourcePrime

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
open CompletedGauss ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalQuadraticSieve ConcretePrimeRowBridge CubicEisenstein ConcreteTraceCRT
open SevenEighths.ProbePhysical SevenEighths.ProbePhase SevenEighths.ProbePrimePower
open FiniteGaussPhase QuadraticGaussRay
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


/-- Exact criterion for a finite source-residue projection: a centered
    source coefficient cancels a CONSTANT residue vector, but no general
    theorem permits replacing a variable ray-dependent residue by one. -/
theorem centered_projection_vanishes_of_constant_residue
    {H : Type*} [Fintype H] (c : H → ℂ) (r : ℂ)
    (hc : ∑ u : H, c u = 0) :
    (∑ u : H, c u * r) = 0 := by
  rw [← Finset.sum_mul, hc, zero_mul]

/-- Concrete parity example of centering without cancellation under
    matching twist; the phenomenon is independent of analytic issues. -/
theorem centered_coefficients_can_have_nonzero_projection :
    ((1 : ℂ) + (-1) = 0) ∧
      ((1 : ℂ) * 1 + (-1) * (-1) = 2) := by
  constructor <;> ring


/-- Exact ORIGINAL prime-column phase bridge: after the angular and
    quadratic Gauss correction, cubic gaussTwo agrees with the negative
    inverse normalized cubic gamma1, not bare gaussTwo. This reuses TWO
    separately certified original OAI theorems; extension to arbitrary
    squarefree columns and actual ray/calibration-weighted residues is open. -/
theorem corrected_j_one_prime_gamma (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p - 1)
    (hI : CompletedGauss.primaryGenerator (Ideal.span {p}) ≠ 0)
    (hs : CanonicalQuadraticSieve.Supported (Ideal.span {p})) :
    CompletedGauss.gaussTwo (Ideal.span {p}) hI *
        star (FiniteGaussPhase.angularFactor p) *
        star (SevenEighths.ProbePhase.G p) =
      -(ProbePrimePower.localGamma p hp.ne_zero hg 1)⁻¹ := by
  rw [SevenEighths.ProbePhysical.gaussTwo_prime_localGamma p hp hg hprimary hI]
  exact SevenEighths.ProbePhysical.corrected_prime_cubic_signal
    p hp.ne_zero hg hchar hprimary hs

#print axioms j_one_bare_completed_weight
#print axioms inverse_character_projection
#print axioms centered_projection_vanishes_of_constant_residue
#print axioms corrected_j_one_prime_gamma

end VF919OriginalLowMetaProjection

end OAI
