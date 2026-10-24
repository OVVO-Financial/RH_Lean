import Mathlib
import «research.VF_919_OAI_ONE_SLOT_DEFECT_AND_FOUR_SECTOR_20261021»

/-!
# OAI one-slot subratio audit, conditional reduction, and physical W0 obstruction

Source authority:
  openai/math/lean/OAI/NumberTheory/DirichletL/Detector/Physical.lean
  openai/math/lean/OAI/NumberTheory/DirichletL/Detector/Compensation.lean
  openai/math/lean/OAI/NumberTheory/DirichletL/Detector/Row.lean
  openai/math/lean/OAI/NumberTheory/DirichletL/Detector/Completed.lean

The three-ratio-to-one assertion is NOT an upstream theorem.
The actual marked probe contains W0(Nm/(Nc*Ns*X)), W1(Ns/Y),
a D-dependent spectral mask, a sexticGauss(s,-m) and an integral
with (Z : C)^t. The same-m cofactor comparison shears W0 by Np^2.
This file isolates the identities one may use WITHOUT conflating
a model Mellin kernel with the original physical source.

No actual Hecke/Gauss/source pair identification or moment power
saving is asserted. #1002 is stacked on #1001, then #1000.
-/

noncomputable section
open scoped Classical BigOperators

namespace RHLean.Proof.CompensatedTupleSubratioReduction

/-! ## Pure real normalizer algebra; NOT a source-level Gauss identity. -/

/-- An exact algebraic inverse-volume/square-root identity for q>0. -/
theorem inverse_volume_sqrt_cancel (q : ℝ) (hqpos : 0 < q) :
    (q⁻¹ * (Real.sqrt q)⁻¹) * (q * Real.sqrt q) = 1 := by
  have hq : q ≠ 0 := ne_of_gt hqpos
  have hs : Real.sqrt q ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hqpos)
  field_simp [hq, hs]

/-- The -3/2 factor cancels the ABSTRACT q * sqrt(q) multiplier. -/
theorem real_power_three_halves_cancel (q : ℝ) (hq : 0 < q) :
    q ^ (-(3 / 2 : ℝ)) * (q * q ^ (1 / 2 : ℝ)) = 1 := by
  have hcombine : q * q ^ (1 / 2 : ℝ) = q ^ (3 / 2 : ℝ) := by
    calc
      q * q ^ (1 / 2 : ℝ) =
          q ^ (1 : ℝ) * q ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = q ^ (1 + (1 / 2 : ℝ)) := (Real.rpow_add hq 1 (1 / 2 : ℝ)).symm
      _ = q ^ (3 / 2 : ℝ) := by norm_num
  calc
    q ^ (-(3 / 2 : ℝ)) * (q * q ^ (1 / 2 : ℝ)) =
        q ^ (-(3 / 2 : ℝ)) * q ^ (3 / 2 : ℝ) := by rw [hcombine]
    _ = q ^ (-(3 / 2 : ℝ) + (3 / 2 : ℝ)) :=
      (Real.rpow_add hq (-(3 / 2 : ℝ)) (3 / 2 : ℝ)).symm
    _ = 1 := by norm_num

/-! ## OAI Physical.lean: the TWO windows must be checked separately. -/

def markedW1Arg (q b Y : ℝ) : ℝ := (q * b) / Y

def rescaledW1Arg (q b Y : ℝ) : ℝ := b / (Y / q)

/-- OAI W1 matches on the SAME ideal-cofactor pairing s=p*b. -/
theorem physical_W1_window_matches (q b Y : ℝ)
    (hq : q ≠ 0) (hY : Y ≠ 0) :
    markedW1Arg q b Y = rescaledW1Arg q b Y := by
  unfold markedW1Arg rescaledW1Arg
  field_simp [hq, hY]

/-- For the same m, these are the literal W0 arguments in OAI
markedPhysicalProbe(s=p*b,X) and physicalProbe(s=b,X/q). -/
def markedW0Arg (m Nc q b X : ℝ) : ℝ :=
  m / (Nc * (q * b) * X)

def rescaledW0Arg (m Nc q b X : ℝ) : ℝ :=
  m / (Nc * b * (X / q))

/-- OAI W0 has an exact q^2 SHEAR; the proposed generic model
K(Na/X,Na/Y,X/(Z*q)) does not cover this actual W0 factor. -/
theorem physical_W0_has_q_square_shear (m Nc q b X : ℝ)
    (hNc : Nc ≠ 0) (hq : q ≠ 0)
    (hb : b ≠ 0) (hX : X ≠ 0) :
    rescaledW0Arg m Nc q b X =
      q ^ 2 * markedW0Arg m Nc q b X := by
  unfold rescaledW0Arg markedW0Arg
  field_simp [hNc, hq, hb, hX]

/-- Concrete admissible positive-norm example: a same-m pairing
does NOT make the W0 arguments identical. -/
theorem physical_W0_same_m_noninvariance_example :
    markedW0Arg 1 1 2 1 1 = (1 / 2 : ℝ) ∧
    rescaledW0Arg 1 1 2 1 1 = (2 : ℝ) := by
  norm_num [markedW0Arg, rescaledW0Arg]

/-! ## Distinguish a synthetic dimensionless Mellin kernel. -/

/-- Correct for a kernel whose COMPLETE dependence is exactly this
three-argument tuple. Not a theorem about the full OAI Mellin integrand. -/
theorem model_three_argument_kernel_invariance
    (K : ℝ → ℝ → ℝ → ℂ) (X Y Z q b : ℝ)
    (hX : X ≠ 0) (hY : Y ≠ 0) (hZ : Z ≠ 0) (hq : q ≠ 0) :
    K ((q * b) / X) ((q * b) / Y) (X / (Z * q)) =
      K (b / (X / q)) (b / (Y / q)) ((X / q) / Z) := by
  have hx : (q * b) / X = b / (X / q) := by
    field_simp [hX, hq]
  have hy : (q * b) / Y = b / (Y / q) := by
    field_simp [hY, hq]
  have hz : X / (Z * q) = (X / q) / Z := by
    field_simp [hZ, hq]
  rw [hx, hy, hz]

/-! ## Phase and full four-subratio algebra. -/

/-- A multiplicative unit phase cancels its own conjugate. This
does not cancel the D-dependent spectralRow or the Z^t twist. -/
theorem isolated_hecke_phase_cancels (ep eb : ℂ)
    (hunit : star ep * ep = 1) :
    star ep * (ep * eb) = eb := by
  rw [← mul_assoc, hunit, one_mul]

/-- Unconditional exact telescoping of the FOUR defects. -/
theorem four_factor_defect_telescope
    (a b c d : ℂ) :
    1 - a * b * c * d =
      (1 - a) + a * (1 - b) +
      a * b * (1 - c) + a * b * c * (1 - d) := by
  ring

/-- This is the CORRECT conditional Gauss-only reduction:
it explicitly assumes the other three ratios have been proved 1. -/
theorem gauss_only_defect_under_three_equalities
    (a b c d : ℂ) (ha : a = 1) (hb : b = 1) (hd : d = 1) :
    1 - a * b * c * d = 1 - c := by
  rw [ha, hb, hd]
  ring

/-- Exact compensated log-polynomial decomposition retaining gamma. -/
theorem one_slot_log_shift_with_defect
    (gamma w Lb Lp : ℂ) (j : ℕ) :
    w * Lb ^ j - gamma * w * (Lb + Lp) ^ j =
      (1 - gamma) * w * Lb ^ j -
        gamma * w * ((Lb + Lp) ^ j - Lb ^ j) := by
  ring

theorem one_slot_degree_zero_with_defect (gamma w : ℂ) :
    w - gamma * w = (1 - gamma) * w := by
  ring

theorem one_slot_degree_one_with_defect (gamma w Lb Lp : ℂ) :
    w * Lb - gamma * w * (Lb + Lp) =
      (1 - gamma) * w * Lb - gamma * w * Lp := by
  ring

theorem one_slot_degree_two_with_defect (gamma w Lb Lp : ℂ) :
    w * Lb ^ 2 - gamma * w * (Lb + Lp) ^ 2 =
      (1 - gamma) * w * Lb ^ 2 -
        gamma * w * (2 * Lb * Lp + Lp ^ 2) := by
  ring

/-! ## A nonprincipal phase does NOT cancel its constant defect. -/

/-- -1 is a sixth root of unity, but 1 - (-1) is nonzero. -/
theorem sextic_root_of_unity_can_have_nonzero_defect :
    ((-1 : ℂ) ^ 6 = 1) ∧ (1 - (-1 : ℂ) = 2) := by
  norm_num

/-- Even PERFECT cancellation of a two-term phase sum leaves the
constant term in the sum of (1 - phase) untouched. -/
theorem vanishing_phase_sum_does_not_cancel_defect :
    ((1 : ℂ) + (-1 : ℂ) = 0) ∧
      ((1 - (1 : ℂ)) + (1 - (-1 : ℂ)) = 2) := by
  norm_num

/-! ## The marked mask is genuinely different on a simple model. -/

def toyCompletedMask (D n : ℕ) : ℂ :=
  if D ∣ n then 1 else 0

theorem marked_mask_not_unmarked_mask_example :
    toyCompletedMask 2 3 = 0 ∧ toyCompletedMask 1 3 = 1 := by
  norm_num [toyCompletedMask]

/-! ## Collision support compression is NOT an l2 estimate. -/

/-- On the abstract collision cofactor b=q*b', b<=X/q implies
b'<=X/q^2. This is only a norm SUPPORT bound. -/
theorem collision_cofactor_cutoff (X q b' : ℝ) (hq : 0 < q)
    (hresc : q * b' ≤ X / q) :
    b' ≤ X / (q ^ 2) := by
  have htotal : (q * b') * q ≤ X :=
    (le_div_iff₀ hq).mp hresc
  apply (le_div_iff₀ (pow_pos hq 2)).2
  nlinarith [htotal]

end RHLean.Proof.CompensatedTupleSubratioReduction

#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.inverse_volume_sqrt_cancel
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.real_power_three_halves_cancel
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.physical_W1_window_matches
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.physical_W0_has_q_square_shear
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.physical_W0_same_m_noninvariance_example
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.model_three_argument_kernel_invariance
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.isolated_hecke_phase_cancels
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.four_factor_defect_telescope
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.gauss_only_defect_under_three_equalities
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.one_slot_log_shift_with_defect
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.one_slot_degree_zero_with_defect
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.one_slot_degree_one_with_defect
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.one_slot_degree_two_with_defect
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.sextic_root_of_unity_can_have_nonzero_defect
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.vanishing_phase_sum_does_not_cancel_defect
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.marked_mask_not_unmarked_mask_example
#print axioms RHLean.Proof.CompensatedTupleSubratioReduction.collision_cofactor_cutoff
