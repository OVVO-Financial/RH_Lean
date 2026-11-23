import RHLean.Geometry.NativeNumberFieldIntegralDescent

/-!
# Integral volume descent from mean map energy

The existing integral completion retains the determinant of the complete image
Gram matrix. This file pays that determinant with the mean squared energy of an
orthonormal frame, rather than repeating the largest singular value in every
source direction. The source metric, integral determinant credit, completion
vectors and rank defect are unchanged.

For q maps into a b-dimensional target, an individual squared operator bound H
gives total frame energy at most q*b*H. Near rank saturation q*b <= (1+e)*r
therefore gives image volume at most ((1+e)*H)^r. This is a volume statement;
it does not assert the corresponding bound on the joint operator norm.
-/

noncomputable section

open Module NumberField Matrix
open scoped BigOperators ComplexOrder Matrix

namespace RHLean.Geometry.NumberFieldDescent

section MeanEnergy

variable {I J Q : Type*} [Fintype I] [Fintype J] [Fintype Q]

/-- A total energy bound pays a product of energies by AM--GM. -/
theorem product_le_power_of_sum_le (e : I → ℝ) (H : ℝ)
    (hI : 0 < Fintype.card I) (he : ∀ i, 0 ≤ e i)
    (hsum : ∑ i, e i ≤ (Fintype.card I : ℝ) * H) :
    ∏ i, e i ≤ H ^ Fintype.card I := by
  have hi : (0 : ℝ) < Fintype.card I := by exact_mod_cast hI
  have hp : 0 ≤ ∏ i, e i := Finset.prod_nonneg fun i _ => he i
  have hg : (∏ i, e i) ^ (Fintype.card I : ℝ)⁻¹ ≤
      (∑ i, e i) / (Fintype.card I : ℝ) := by
    have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : I => (1 : ℝ)) e
      (fun _ _ => zero_le_one) (by simpa using hi) (fun i _ => he i)
    simpa using h
  have hm : (∑ i, e i) / (Fintype.card I : ℝ) ≤ H :=
    (div_le_iff₀ hi).mpr (by simpa [mul_comm] using hsum)
  calc
    ∏ i, e i = ((∏ i, e i) ^ (Fintype.card I : ℝ)⁻¹) ^
        (Fintype.card I : ℝ) := by
      rw [← Real.rpow_mul hp, inv_mul_cancel₀ hi.ne', Real.rpow_one]
    _ ≤ H ^ (Fintype.card I : ℝ) := Real.rpow_le_rpow
      (Real.rpow_nonneg hp _) (hg.trans hm) hi.le
    _ = H ^ Fintype.card I := Real.rpow_natCast H _

/-- The diagonal of the Gram matrix is the original column energy. -/
theorem gram_diagonal_re_eq_columnEnergy (M : Matrix J I ℂ) (i : I) :
    ((Mᴴ * M) i i).re = columnEnergy (M.col i) := by
  simp [columnEnergy, Matrix.mul_apply, Matrix.col, RCLike.star_def,
    RCLike.conj_mul, ← Complex.ofReal_pow]

/-- Hadamard and AM--GM retain the average frame energy. A single large
singular direction is not charged in every source dimension. -/
theorem gram_det_le_power_of_mean_energy [DecidableEq I] (M : Matrix J I ℂ) (H : ℝ)
    (hI : 0 < Fintype.card I)
    (hsum : ∑ i, columnEnergy (M.col i) ≤ (Fintype.card I : ℝ) * H) :
    ‖(Mᴴ * M).det‖ ≤ H ^ Fintype.card I := by
  have h := hermitian_hadamard (posSemidef_conjTranspose_mul_self M)
  simp_rw [gram_diagonal_re_eq_columnEnergy] at h
  exact h.trans (product_le_power_of_sum_le (fun i => columnEnergy (M.col i))
    H hI (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) hsum)

/-- An individual squared operator bound controls each row energy. The test
vector is the conjugate row itself, so no singular-value API is needed. -/
theorem row_energy_le_of_operator_energy (M : Matrix J I ℂ) (H : ℝ)
    (hH : 0 ≤ H)
    (hM : ∀ z : I → ℂ, columnEnergy (M *ᵥ z) ≤ H * columnEnergy z)
    (j : J) : columnEnergy (M.row j) ≤ H := by
  let z : I → ℂ := fun i => star (M j i)
  let E : ℝ := columnEnergy (M.row j)
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hz : columnEnergy z = E := by simp [columnEnergy, z, E, Matrix.row]
  have hentry : (M *ᵥ z) j = (E : ℂ) := by
    simp [Matrix.mulVec, dotProduct, z, E, columnEnergy, Matrix.row,
      RCLike.star_def, RCLike.mul_conj, ← Complex.ofReal_pow]
  have hsingle : ‖(M *ᵥ z) j‖ ^ 2 ≤ columnEnergy (M *ᵥ z) :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have hbound := hM z
  rw [hz] at hbound
  have hsq : E ^ 2 ≤ H * E := by
    have hnorm : ‖(M *ᵥ z) j‖ = E := by
      rw [hentry, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
    rw [hnorm] at hsingle
    exact hsingle.trans hbound
  change E ≤ H
  by_contra hnot
  have hpos : 0 < E := lt_of_le_of_lt hH (lt_of_not_ge hnot)
  have hstrict : H * E < E * E :=
    mul_lt_mul_of_pos_right (lt_of_not_ge hnot) hpos
  nlinarith

/-- The Hilbert--Schmidt sum is at most target rank times the individual
squared operator bound, rather than source rank times that bound. -/
theorem total_column_energy_le_target_rank (M : Matrix J I ℂ) (H : ℝ)
    (hH : 0 ≤ H)
    (hM : ∀ z : I → ℂ, columnEnergy (M *ᵥ z) ≤ H * columnEnergy z) :
    ∑ i, columnEnergy (M.col i) ≤ (Fintype.card J : ℝ) * H := by
  calc
    ∑ i, columnEnergy (M.col i) = ∑ j, columnEnergy (M.row j) := by
      unfold columnEnergy Matrix.col Matrix.row
      exact Finset.sum_comm
    _ ≤ ∑ _ : J, H := Finset.sum_le_sum fun j _ =>
      row_energy_le_of_operator_energy M H hH hM j
    _ = _ := by simp

/-- The matrix of the actual joint map into the Hilbert direct sum. -/
def jointMapMatrix (φ : Q → Matrix J I ℂ) : Matrix (J × Q) I ℂ :=
  fun p i => φ p.2 p.1 i

theorem jointMapMatrix_total_column_energy (φ : Q → Matrix J I ℂ) :
    (∑ i, columnEnergy ((jointMapMatrix φ).col i)) =
      ∑ h : Q, ∑ i, columnEnergy ((φ h).col i) := by
  simp only [columnEnergy, jointMapMatrix, Matrix.col, Fintype.sum_prod_type]
  calc
    (∑ i : I, ∑ j : J, ∑ h : Q, ‖φ h j i‖ ^ 2) =
        ∑ i : I, ∑ h : Q, ∑ j : J, ‖φ h j i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ h : Q, ∑ i : I, ∑ j : J, ‖φ h j i‖ ^ 2 := Finset.sum_comm

/-- Rank saturation improves the determinant price for the same family of
maps. It does not improve their joint squared operator norm. -/
theorem jointMapMatrix_gram_det_le_of_rank_saturation [DecidableEq I]
    (φ : Q → Matrix J I ℂ) (H ε : ℝ) (hI : 0 < Fintype.card I)
    (hH : 0 ≤ H)
    (hφ : ∀ h (z : I → ℂ), columnEnergy (φ h *ᵥ z) ≤ H * columnEnergy z)
    (hrank : (Fintype.card Q : ℝ) * Fintype.card J ≤
      (1 + ε) * Fintype.card I) :
    ‖((jointMapMatrix φ)ᴴ * jointMapMatrix φ).det‖ ≤
      ((1 + ε) * H) ^ Fintype.card I := by
  apply gram_det_le_power_of_mean_energy _ _ hI
  rw [jointMapMatrix_total_column_energy]
  calc
    ∑ h : Q, ∑ i, columnEnergy ((φ h).col i) ≤
        ∑ _ : Q, (Fintype.card J : ℝ) * H := Finset.sum_le_sum fun h _ =>
      total_column_energy_le_target_rank (φ h) H hH (hφ h)
    _ = ((Fintype.card Q : ℝ) * Fintype.card J) * H := by simp [mul_assoc]
    _ ≤ ((1 + ε) * Fintype.card I) * H := mul_le_mul_of_nonneg_right hrank hH
    _ = (Fintype.card I : ℝ) * ((1 + ε) * H) := by ring

end MeanEnergy

section IntegralDescent

variable {K I J : Type*} [Field K] [NumberField K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Replace the original worst-direction image estimate by a mean-energy
estimate in the same metric. No lattice or source is redefined. -/
theorem image_gram_bound_of_mean_energy (A : Metric K I) (σ : K →+* ℂ)
    (X : Matrix J I ℂ) (P : ℝ) (hI : 0 < Fintype.card I)
    (hmean : ∑ i, columnEnergy ((X * (A.frame σ)⁻¹).col i) ≤
      (Fintype.card I : ℝ) * Real.exp (2 * P)) :
    ‖(Xᴴ * X).det‖ ≤ A.gramDet σ * Real.exp (2 * Fintype.card I * P) := by
  let F := A.frame σ
  let M := X * F⁻¹
  have hu : IsUnit F.det := isUnit_iff_ne_zero.mpr (A.nonsingular σ)
  have hM : ‖(Mᴴ * M).det‖ ≤ Real.exp (2 * Fintype.card I * P) := by
    have h := gram_det_le_power_of_mean_energy M (Real.exp (2 * P)) hI hmean
    have he : (Real.exp (2 * P)) ^ Fintype.card I =
        Real.exp (2 * Fintype.card I * P) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    exact he ▸ h
  have hX : X = M * F := (F.nonsing_inv_mul_cancel_right X hu).symm
  calc
    ‖(Xᴴ * X).det‖ = ‖F.det‖ ^ 2 * ‖(Mᴴ * M).det‖ := by
      rw [hX, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ M,
        det_mul, det_mul, det_conjTranspose, norm_mul, norm_mul, norm_star]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hM (sq_nonneg _)

/-- Genuine integral slope descent from mean squared map energy. The
completion and its nonzero integral determinant are constructed by the
existing number-field theorem and the product-formula credit is retained. -/
theorem mean_energy_weighted_descent {r d : ℕ} (hr : 0 < r)
    (A : Metric K (Fin r)) (B : Metric K J) (F : Matrix J (Fin r) (𝓞 K))
    (hinj : Function.Injective (overField F).mulVec) (hdim : Fintype.card J = r + d)
    (S : Set (J → K)) (hS : Submodule.span K S = ⊤) (hi : ∀ x ∈ S, IntegralVector x)
    (P Λ : ℝ)
    (hmean : ∀ σ, ∑ i, columnEnergy
      ((B.imageFrame F σ * (A.frame σ)⁻¹).col i) ≤ (r : ℝ) * Real.exp (2 * P))
    (hs : ∀ x ∈ S, ∀ σ, B.energy σ x ≤ Real.exp (2 * Λ)) :
    r * (A.slopeSq - 2 * P) - 2 * d * Λ ≤ Fintype.card J * B.slopeSq := by
  classical
  obtain ⟨_, C, _, _, _, _, hc, hlocal⟩ := completed_image_bound B F hinj hdim S hS hi Λ hs
  have hlog (σ : K →+* ℂ) :
      2 * Real.log ‖σ (C.det : K)‖ + Real.log (B.gramDet σ) ≤
        Real.log (A.gramDet σ) + (2 * r * P + 2 * d * Λ) := by
    have h := image_gram_bound_of_mean_energy A σ (B.imageFrame F σ) P
      (by simpa using hr) (by simpa using hmean σ)
    rw [Fintype.card_fin] at h
    have hv := (hlocal σ).trans (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le)
    have ha : 0 < A.gramDet σ := sq_pos_of_pos (norm_pos_iff.mpr (A.nonsingular σ))
    have hb : 0 < B.gramDet σ := sq_pos_of_pos (norm_pos_iff.mpr (B.nonsingular σ))
    have hσ : 0 < ‖σ (C.det : K)‖ := norm_pos_iff.mpr
      ((map_ne_zero σ).mpr ((Subalgebra.coe_eq_zero _).not.mpr hc))
    have hl := Real.log_le_log (mul_pos (sq_pos_of_pos hσ) hb) hv
    rw [Real.log_mul (pow_ne_zero _ hσ.ne') hb.ne', Real.log_pow,
      mul_assoc, ← Real.exp_add, Real.log_mul ha.ne' (Real.exp_ne_zero _), Real.log_exp] at hl
    exact_mod_cast hl
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hlog σ)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at ht
  have hcredit := log_det_credit C hc
  have hJ : (0 : ℝ) < Fintype.card J := by exact_mod_cast (hdim ▸ Nat.add_pos_left hr d)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have he : (0 : ℝ) < Fintype.card (K →+* ℂ) := by exact_mod_cast Fintype.card_pos
  unfold Metric.slopeSq
  rw [Fintype.card_fin]
  field_simp [hr'.ne', hJ.ne', he.ne', he, hr', hJ]
  nlinarith only [ht, hcredit]

end IntegralDescent

end RHLean.Geometry.NumberFieldDescent
