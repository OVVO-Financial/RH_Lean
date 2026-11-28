import RHLean.Analysis.PartialMomentSchurTarget
import Mathlib.Analysis.Matrix.Order

/-!
# Lossless Co/Div synthesis and its normalized determinant

The four original partial moments retain their arbitrary target and original
weights. Combine the two transpose cross terms first, and then the two
convergent terms. The normalized divergent spectrum is an actual matrix
spectrum; no signed height inequality is an input or asserted as an output.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators MatrixOrder

namespace RHLean.Analysis.NNSCoDiv

section Weighted
variable {α ι : Type*}

def finiteCo (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    Matrix ι ι ℝ := finiteCLPM S w x t + finiteCUPM S w x t

def finiteDiv (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    Matrix ι ι ℝ := finiteDLPM S w x t + finiteDUPM S w x t

theorem divergent_transpose (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (t : ι → ℝ) : (finiteDLPM S w x t)ᵀ = finiteDUPM S w x t := by
  ext i j
  unfold finiteDLPM finiteDUPM
  exact Finset.sum_congr rfl fun a _ => by
    change w a * partialLower (x a j) (t j) * partialUpper (x a i) (t i) =
      w a * partialUpper (x a i) (t i) * partialLower (x a j) (t j)
    ring

theorem clpm_symmetric (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (t : ι → ℝ) : (finiteCLPM S w x t)ᵀ = finiteCLPM S w x t := by
  ext i j
  unfold finiteCLPM
  exact Finset.sum_congr rfl fun a _ => by
    change w a * partialLower (x a j) (t j) * partialLower (x a i) (t i) =
      w a * partialLower (x a i) (t i) * partialLower (x a j) (t j)
    ring

theorem cupm_symmetric (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (t : ι → ℝ) : (finiteCUPM S w x t)ᵀ = finiteCUPM S w x t := by
  ext i j
  unfold finiteCUPM
  exact Finset.sum_congr rfl fun a _ => by
    change w a * partialUpper (x a j) (t j) * partialUpper (x a i) (t i) =
      w a * partialUpper (x a i) (t i) * partialUpper (x a j) (t j)
    ring

theorem co_symmetric (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (t : ι → ℝ) : (finiteCo S w x t)ᵀ = finiteCo S w x t := by
  rw [finiteCo, Matrix.transpose_add, clpm_symmetric, cupm_symmetric]

theorem div_symmetric (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (t : ι → ℝ) : (finiteDiv S w x t)ᵀ = finiteDiv S w x t := by
  rw [finiteDiv, Matrix.transpose_add, ← divergent_transpose S w x t,
    Matrix.transpose_transpose, add_comm]

theorem three_matrix (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    finiteTargetSecondMoment S w x t =
      finiteCLPM S w x t + finiteCUPM S w x t - finiteDiv S w x t := by
  rw [finiteTargetSecondMoment_eq_partial_reassembly, finiteDiv]
  abel

theorem two_matrix (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    finiteTargetSecondMoment S w x t = finiteCo S w x t - finiteDiv S w x t :=
  three_matrix S w x t

/-- The other sign is the second moment of the unsigned deviations. -/
theorem absolute_synthesis (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ) (t : ι → ℝ) :
    finiteCo S w x t + finiteDiv S w x t =
      finiteTargetSecondMoment S w
        (fun a i => partialUpper (x a i) (t i) + partialLower (x a i) (t i)) 0 := by
  ext i j
  simp only [finiteCo, finiteDiv, finiteCLPM, finiteCUPM, finiteDLPM, finiteDUPM,
    finiteTargetSecondMoment, Matrix.add_apply, Pi.zero_apply, sub_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem divergent_diagonal_zero (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (t : ι → ℝ) (i : ι) : finiteDiv S w x t i i = 0 := by
  have h (a : α) : partialLower (x a i) (t i) * partialUpper (x a i) (t i) = 0 := by
    by_cases ha : t i ≤ x a i
    · simp [partialLower, not_lt_of_ge ha]
    · simp [partialUpper, ha]
  unfold finiteDiv finiteDLPM finiteDUPM
  simp only [Matrix.add_apply, mul_assoc]
  have h' (a : α) : partialUpper (x a i) (t i) * partialLower (x a i) (t i) = 0 :=
    (mul_comm _ _).trans (h a)
  simp only [h, h', mul_zero, Finset.sum_const_zero, add_zero]

/-- This is the original true-zero/mean-independent Schur, not a new target. -/
theorem scaled_schur_two_matrix (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (s t : ι → ℝ) :
    (fun i j => finiteTotalWeight S w * (finiteCo S w x t - finiteDiv S w x t) i j -
      finiteTargetFirstMoment S w x t i * finiteTargetFirstMoment S w x t j) =
      (fun i j => finiteTotalWeight S w * (finiteCo S w x s - finiteDiv S w x s) i j -
        finiteTargetFirstMoment S w x s i * finiteTargetFirstMoment S w x s j) := by
  simp only [← two_matrix]
  exact finiteTargetScaledSchur_target_invariant S w x s t

/-- Nonnegative weights give the original weighted Gram, at any target. -/
theorem second_moment_psd [Finite ι] (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (t : ι → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a) :
    (finiteTargetSecondMoment S w x t).PosSemidef := by
  let z (a : α) (i : ι) := x a i - t i
  have he : finiteTargetSecondMoment S w x t =
      ∑ a ∈ S, w a • vecMulVec (z a) (z a) := by
    ext i j
    simp only [finiteTargetSecondMoment, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply, z]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [he]
  exact Matrix.posSemidef_sum S fun a ha =>
    (by simpa only [star_trivial] using
      (Matrix.posSemidef_vecMulVec_self_star (z a)) :
      (vecMulVec (z a) (z a)).PosSemidef).smul (hw a ha)

theorem synthesis_psd [Finite ι] (S : Finset α) (w : α → ℝ) (x : α → ι → ℝ)
    (t : ι → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a) :
    (finiteCo S w x t - finiteDiv S w x t).PosSemidef ∧
    (finiteCo S w x t + finiteDiv S w x t).PosSemidef := by
  rw [← two_matrix, absolute_synthesis]
  exact ⟨second_moment_psd S w x t hw, second_moment_psd S w _ 0 hw⟩

end Weighted

section Normalized

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- No diagonal norm surrogate: the normalization is the actual inverse
positive square root of Co. -/
def normalized (C D : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (CFC.sqrt C)⁻¹ * D * (CFC.sqrt C)⁻¹

private theorem whitening (C : Matrix ι ι ℝ) (hc : C.PosDef) :
    let R := (CFC.sqrt C)⁻¹
    Rᴴ = R ∧ R * C * R = 1 := by
  let S := CFC.sqrt C
  have hs : S * S = C := by
    simpa only [S, pow_two] using CFC.sq_sqrt C hc.posSemidef.nonneg
  have hsd : S.det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det hs
    rw [Matrix.det_mul, hz, zero_mul] at h
    exact hc.det_pos.ne' h.symm
  have hunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hsd
  have hh : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).isHermitian
  change S⁻¹ᴴ = S⁻¹ ∧ S⁻¹ * C * S⁻¹ = 1
  constructor
  · rw [Matrix.conjTranspose_nonsing_inv, hh.eq]
  · rw [← hs, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul S hunit,
      Matrix.one_mul, Matrix.mul_nonsing_inv S hunit]

/-- Determinant factorization and the two PSD bounds on the same normalized
matrix. The positive sign corresponds to absolute deviations. -/
theorem normalized_certificate (C D : Matrix ι ι ℝ) (hc : C.PosDef)
    (hd : D.IsHermitian) (hm : (C-D).PosSemidef) (hp : (C+D).PosSemidef) :
    (normalized C D).IsHermitian ∧
    (1-normalized C D).PosSemidef ∧ (1+normalized C D).PosSemidef ∧
    (C-D).det = C.det * (1-normalized C D).det := by
  let R := (CFC.sqrt C)⁻¹
  let K := normalized C D
  have hR : Rᴴ = R ∧ R*C*R = 1 := whitening C hc
  have hk : K = R*D*R := rfl
  have hmk : Rᴴ*(C-D)*R = 1-K := by
    rw [hR.1, Matrix.mul_sub, Matrix.sub_mul, hR.2, ← hk]
  have hpk : Rᴴ*(C+D)*R = 1+K := by
    rw [hR.1, Matrix.mul_add, Matrix.add_mul, hR.2, ← hk]
  refine ⟨?_, hmk ▸ hm.conjTranspose_mul_mul_same R,
    hpk ▸ hp.conjTranspose_mul_mul_same R, ?_⟩
  · have he : K = Rᴴ*D*R := by rw [hR.1, hk]
    rw [he]
    exact Matrix.isHermitian_conjTranspose_mul_mul R hd
  · have h₁ : R.det * C.det * R.det = 1 := by
      simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hR.2
    have h₂ : R.det * (C-D).det * R.det = (1-K).det := by
      simpa only [hR.1, Matrix.det_mul] using congrArg Matrix.det hmk
    calc
      (C-D).det = (R.det * C.det * R.det) * (C-D).det := by rw [h₁, one_mul]
      _ = C.det * (R.det * (C-D).det * R.det) := by ring
      _ = C.det * (1-K).det := by rw [h₂]

/-- The determinant of a PSD pair I±K is controlled by the actual Hermitian
eigenvalues, not by an arbitrarily chosen list of scalars. -/
theorem spectrum_factor (K : Matrix ι ι ℝ) (hK : K.IsHermitian)
    (hm : (1-K).PosSemidef) (hp : (1+K).PosSemidef) :
    (∀ i, -1 ≤ hK.eigenvalues i ∧ hK.eigenvalues i ≤ 1) ∧
      (1-K).det = ∏ i, (1-hK.eigenvalues i) := by
  let V : Matrix ι ι ℝ := hK.eigenvectorUnitary
  have hV : Vᴴ * V = 1 := Unitary.coe_star_mul_self hK.eigenvectorUnitary
  have hd : Vᴴ * K * V = diagonal hK.eigenvalues := by
    have h := hK.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    exact h
  have hm' : Vᴴ*(1-K)*V = diagonal (fun i => 1-hK.eigenvalues i) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV, hd]
    ext i j
    rw [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs <;> ring
  have hp' : Vᴴ*(1+K)*V = diagonal (fun i => 1+hK.eigenvalues i) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hV, hd]
    ext i j
    rw [Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs <;> ring
  have hmP : (diagonal (fun i => 1-hK.eigenvalues i)).PosSemidef :=
    hm' ▸ hm.conjTranspose_mul_mul_same V
  have hpP : (diagonal (fun i => 1+hK.eigenvalues i)).PosSemidef :=
    hp' ▸ hp.conjTranspose_mul_mul_same V
  constructor
  · intro i
    have a : 0 ≤ 1-hK.eigenvalues i := by simpa only [Matrix.diagonal_apply_eq] using
      (hmP.diag_nonneg (i := i))
    have b : 0 ≤ 1+hK.eigenvalues i := by simpa only [Matrix.diagonal_apply_eq] using
      (hpP.diag_nonneg (i := i))
    constructor <;> linarith
  · have h₁ : Vᴴ.det * V.det = 1 := by
      simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hV
    have h₂ := congrArg Matrix.det hm'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h₂
    calc
      (1-K).det = (Vᴴ.det * V.det) * (1-K).det := by rw [h₁, one_mul]
      _ = Vᴴ.det * (1-K).det * V.det := by ring
      _ = _ := h₂

/-- End-to-end arbitrary-target synthesis, using only the original moment
matrices and positivity of the convergent baseline. -/
theorem finite_spectral_synthesis {α : Type*} (S : Finset α) (w : α → ℝ)
    (x : α → ι → ℝ) (t : ι → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a)
    (hc : (finiteCo S w x t).PosDef) :
    ∃ hK : (normalized (finiteCo S w x t) (finiteDiv S w x t)).IsHermitian,
      (∀ i, -1 ≤ hK.eigenvalues i ∧ hK.eigenvalues i ≤ 1) ∧
      (finiteTargetSecondMoment S w x t).det =
        (finiteCo S w x t).det * ∏ i, (1-hK.eigenvalues i) := by
  have hd : (finiteDiv S w x t).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact div_symmetric S w x t
  have h := synthesis_psd S w x t hw
  obtain ⟨hk,hm,hp,det⟩ := normalized_certificate _ _ hc hd h.1 h.2
  obtain ⟨he,hf⟩ := spectrum_factor _ hk hm hp
  exact ⟨hk,he,by rw [two_matrix, det, hf]⟩

/-- The exact logarithmic correction and its strict eigenvalue condition
for a nonsingular synthesized moment. -/
theorem finite_log_synthesis {α : Type*} (S : Finset α) (w : α → ℝ)
    (x : α → ι → ℝ) (t : ι → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a)
    (hc : (finiteCo S w x t).PosDef) (hg : (finiteTargetSecondMoment S w x t).PosDef) :
    ∃ hK : (normalized (finiteCo S w x t) (finiteDiv S w x t)).IsHermitian,
      (∀ i, -1 ≤ hK.eigenvalues i ∧ hK.eigenvalues i < 1) ∧
      Real.log (finiteTargetSecondMoment S w x t).det =
        Real.log (finiteCo S w x t).det + ∑ i, Real.log (1-hK.eigenvalues i) := by
  obtain ⟨hk,he,hf⟩ := finite_spectral_synthesis S w x t hw hc
  have hn : (∏ i, (1-hk.eigenvalues i)) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hf
    exact hg.det_pos.ne' hf
  have hs : ∀ i, 1-hk.eigenvalues i ≠ 0 :=
    fun i => Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ i)
  refine ⟨hk,fun i => ⟨(he i).1,lt_of_le_of_ne (he i).2 (fun h => hs i (by rw [h, sub_self]))⟩,?_⟩
  rw [hf, Real.log_mul hc.det_pos.ne' hn, Real.log_prod (fun i _ => hs i)]

/-- A nonsingular original Gram automatically has a positive definite
convergent baseline; no independent full-rank assumption is needed. -/
theorem co_posDef_of_second_moment {α : Type*} (S : Finset α) (w : α → ℝ)
    (x : α → ι → ℝ) (t : ι → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a)
    (hg : (finiteTargetSecondMoment S w x t).PosDef) :
    (finiteCo S w x t).PosDef := by
  rw [two_matrix] at hg
  have he : finiteCo S w x t =
      (1/2:ℝ) • ((finiteCo S w x t-finiteDiv S w x t)+
        (finiteCo S w x t+finiteDiv S w x t)) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply]
    ring
  rw [he]
  exact (hg.add_posSemidef (synthesis_psd S w x t hw).2).smul (by norm_num)

/-- A rigorous sufficient bound for net synthesis gain. The trace has
its actual sign; it is not replaced by an unsigned estimate. -/
theorem log_spectrum_le_neg_sum {λ : ι → ℝ} (h : ∀ i, λ i < 1) :
    (∑ i, Real.log (1-λ i)) ≤ -(∑ i, λ i) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  have H := Real.log_le_sub_one_of_pos (sub_pos.mpr (h i))
  linarith only [H]

/-- Direct signed bound on the original second moment, with no guessed
synthesis factor and no positive-definiteness assumption on Div. -/
theorem finite_log_trace_bound {α : Type*} (S : Finset α) (w : α → ℝ)
    (x : α → ι → ℝ) (t : ι → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a)
    (hg : (finiteTargetSecondMoment S w x t).PosDef) :
    Real.log (finiteTargetSecondMoment S w x t).det ≤
      Real.log (finiteCo S w x t).det -
        (normalized (finiteCo S w x t) (finiteDiv S w x t)).trace := by
  obtain ⟨hk,he,hf⟩ := finite_log_synthesis S w x t hw
    (co_posDef_of_second_moment S w x t hw hg) hg
  have ht : (normalized (finiteCo S w x t) (finiteDiv S w x t)).trace =
      ∑ i, hk.eigenvalues i := hk.trace_eq_sum_eigenvalues
  rw [hf, ht]
  linarith only [log_spectrum_le_neg_sum (fun i => (he i).2)]

end Normalized

end RHLean.Analysis.NNSCoDiv
