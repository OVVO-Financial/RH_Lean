import RHLean.Geometry.NativeMeanEnergyDescent
import RHLean.Geometry.NativeTwistedTraceDiagnostic

/-!
# Volume payment for actual integral translation--trace maps

For a genuine integral function u on a finite additive group, the maps are
translated multiplication followed by the unnormalized trivial-character
trace. Their integer matrix is C(h,i)=u(i+h). In normalized counting measure
on the source, the squared volume expansion is q^q det(C)^2.

Every orthonormal column has energy q*sum(u^2), giving a volume price
(q*sum(u^2))^q <= (q^2 B^2)^q when |u|<=B. The known q^2 collective-norm
counterexample is untouched. An explicit four-point integral section attains
the volume bound, so its leading factor cannot be reduced in this class.

This is an actual finite function-algebra construction and a quantitative
descent ingredient. It does not identify these data with the still-open
arithmetic geometric family controlling the complete G_z source.
-/

noncomputable section

open Matrix Module
open scoped BigOperators

namespace RHLean.Geometry

section MatrixVolume

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Real matrix Hadamard bound in exact column-energy form. -/
theorem nativeRealMatrix_det_sq_le_column_energy (M : Matrix I I ℝ) :
    M.det ^ 2 ≤ ∏ j, ∑ i, (M i j) ^ 2 := by
  let v (j : I) : EuclideanSpace ℝ I := WithLp.toLp 2 (M.col j)
  have h := nativeGramDet_le_prod_norm_sq_fintype
    (by simpa using (finrank_euclideanSpace (𝕜 := ℝ) (ι := I))) v
  have hG : Matrix.gram ℝ v = M.conjTranspose * M :=
    Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun I ℝ) v
  rw [hG, Matrix.det_mul, Matrix.det_conjTranspose, star_trivial] at h
  have hv (j : I) : ‖v j‖ ^ 2 = ∑ i, (M i j) ^ 2 := by
    simpa [v, Matrix.col] using EuclideanSpace.real_norm_sq_eq (v j)
  simp_rw [hv] at h
  simpa only [← sq] using h

/-- Integral coordinates are kept; no normalization of the trace is used. -/
theorem nativeIntegerMatrix_det_sq_le_column_energy (C : Matrix I I ℤ) :
    (C.det : ℝ) ^ 2 ≤ ∏ j, ∑ i, (C i j : ℝ) ^ 2 := by
  have h := nativeRealMatrix_det_sq_le_column_energy (C.map fun z : ℤ => (z : ℝ))
  simpa only [← Int.cast_det, Matrix.map_apply] using h

end MatrixVolume

section TranslationTrace

variable {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]

/-- The actual integer coefficients of translated multiplication followed
by the unnormalized trivial-character trace. -/
def nativeTranslationTraceMatrix (u : G → ℤ) : Matrix G G ℤ :=
  fun h i => u (i + h)

def nativeTranslationTraceEnergy (u : G → ℤ) : ℝ :=
  ∑ i, (u i : ℝ) ^ 2

/-- Translation invariance of counting measure identifies every column
energy with the energy of the original integral section. -/
theorem nativeTranslationTrace_column_energy (u : G → ℤ) (i : G) :
    (∑ h, (nativeTranslationTraceMatrix u h i : ℝ) ^ 2) =
      nativeTranslationTraceEnergy u := by
  exact (Equiv.addLeft i).sum_comp (fun h => (u h : ℝ) ^ 2)

/-- The genuine integer determinant is paid by section energy, not a
repeated worst-direction operator estimate. -/
theorem nativeTranslationTrace_det_sq_le (u : G → ℤ) :
    ((nativeTranslationTraceMatrix u).det : ℝ) ^ 2 ≤
      nativeTranslationTraceEnergy u ^ Fintype.card G := by
  have h := nativeIntegerMatrix_det_sq_le_column_energy (nativeTranslationTraceMatrix u)
  simp_rw [nativeTranslationTrace_column_energy] at h
  simpa using h

/-- Normalized counting measure has source Gram determinant q^(-q).
Consequently the exact squared-volume expansion has the factor q^q. -/
theorem nativeTranslationTrace_normalized_volume_le (u : G → ℤ) :
    (Fintype.card G : ℝ) ^ Fintype.card G *
        ((nativeTranslationTraceMatrix u).det : ℝ) ^ 2 ≤
      ((Fintype.card G : ℝ) * nativeTranslationTraceEnergy u) ^ Fintype.card G := by
  calc
    _ ≤ (Fintype.card G : ℝ) ^ Fintype.card G *
        nativeTranslationTraceEnergy u ^ Fintype.card G :=
      mul_le_mul_of_nonneg_left (nativeTranslationTrace_det_sq_le u)
        (pow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := (mul_pow _ _ _).symm

theorem nativeTranslationTrace_energy_le (u : G → ℤ) (B : ℝ)
    (hB : 0 ≤ B) (hu : ∀ i, |(u i : ℝ)| ≤ B) :
    nativeTranslationTraceEnergy u ≤ (Fintype.card G : ℝ) * B ^ 2 := by
  calc
    _ ≤ ∑ _ : G, B ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := hu i
      nlinarith [sq_abs (u i : ℝ), abs_nonneg (u i : ℝ)]
    _ = _ := by simp

/-- The q^2 volume price is valid even when the corresponding q^2
collective operator estimate is false. -/
theorem nativeTranslationTrace_normalized_volume_le_qSquared
    (u : G → ℤ) (B : ℝ) (hB : 0 ≤ B) (hu : ∀ i, |(u i : ℝ)| ≤ B) :
    (Fintype.card G : ℝ) ^ Fintype.card G *
        ((nativeTranslationTraceMatrix u).det : ℝ) ^ 2 ≤
      ((Fintype.card G : ℝ) ^ 2 * B ^ 2) ^ Fintype.card G := by
  apply (nativeTranslationTrace_normalized_volume_le u).trans
  apply pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have h := mul_le_mul_of_nonneg_left (nativeTranslationTrace_energy_le u B hB hu)
    (Nat.cast_nonneg (α := ℝ) (Fintype.card G))
  simpa only [sq, mul_assoc] using h

end TranslationTrace

section SharpFiniteExample

/-- A genuine integral section on the four-point cyclic group. -/
def nativeFourTraceSection (i : Fin 4) : ℤ := ![1, 1, 1, -1] i

theorem nativeFourTrace_matrix :
    nativeTranslationTraceMatrix nativeFourTraceSection =
      !![1, 1, 1, -1; 1, 1, -1, 1; 1, -1, 1, 1; -1, 1, 1, 1] := by
  ext h i
  fin_cases h <;> fin_cases i <;>
    norm_num [nativeTranslationTraceMatrix, nativeFourTraceSection]

/-- All four singular directions have the same nonzero squared size. -/
theorem nativeFourTrace_gram :
    (nativeTranslationTraceMatrix nativeFourTraceSection).transpose *
        nativeTranslationTraceMatrix nativeFourTraceSection =
      (4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  rw [nativeFourTrace_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

theorem nativeFourTrace_det_sq :
    (nativeTranslationTraceMatrix nativeFourTraceSection).det ^ 2 = 256 := by
  have h := congrArg Matrix.det nativeFourTrace_gram
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one] at h
  norm_num at h
  nlinarith

theorem nativeFourTrace_injective :
    Function.Injective (nativeTranslationTraceMatrix nativeFourTraceSection).mulVec := by
  apply Matrix.mulVec_injective_of_det_ne_zero
  intro h
  have hd := nativeFourTrace_det_sq
  rw [h] at hd
  norm_num at hd

/-- At B=1 and q=4, the new bound is attained exactly by integral
translation maps. The normalized squared-volume price is q^2 per rank. -/
theorem nativeFourTrace_normalized_volume_sharp :
    (∀ i : Fin 4, |(nativeFourTraceSection i : ℝ)| = 1) ∧
    (4 : ℝ) ^ 4 * ((nativeTranslationTraceMatrix nativeFourTraceSection).det : ℝ) ^ 2 =
      ((4 : ℝ) ^ 2 * 1 ^ 2) ^ 4 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [nativeFourTraceSection]
  · have hd : ((nativeTranslationTraceMatrix nativeFourTraceSection).det : ℝ) ^ 2 = 256 := by
      exact_mod_cast nativeFourTrace_det_sq
    rw [hd]
    norm_num

/-- The existing two-point operator obstruction survives the improved
volume bound: its joint energy is 50 while q^2 B^2 is only 36. -/
theorem nativeTraceVolume_does_not_assert_operator_improvement :
    ¬ nativeTwoTraceJointEnergy (fun _ => 1) ≤
      (2 : ℝ) ^ 2 * 3 ^ 2 * nativeTwoTraceSourceEnergy (fun _ => 1) :=
  nativeTwoTrace_not_qSquared.2.2

end SharpFiniteExample

end RHLean.Geometry
