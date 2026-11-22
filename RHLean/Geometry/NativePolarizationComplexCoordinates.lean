import RHLean.Geometry.NativePrescribedHermitianSpaces
import RHLean.Geometry.NativeTraceDualDiscriminant

/-!
# Explicit complex coordinates for the prescribed polarization

The diagonal operator is literally multiplication by i on the positive
coordinates and by -i on the negative coordinates of the constructed W_j.
Its square, preservation of the original conjugate-first Hermitian form,
positive rotated pairing and exact trace are proved on these coordinates.
The finite block trace is computed as a real trace, retaining the factor 2.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean,
the GlobalTheory section (blk through trace_blk), star_dot_self_eq and sum_normSq_pos;
SumEmbeddingsEq.lean, trace_eq_sum_psi; DatProofs.lean, re_mul_negI.
The diagonal specialization replaces the generic change-of-basis choice by
the actual standard frame already constructed natively. The source archive
states no license; attribution is preserved without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField ComplexConjugate Matrix
open scoped BigOperators Classical

namespace RHLean.Geometry.NativePolarizationComplexCoordinates

open NativePrescribedHermitian

section FieldTrace

variable {E : Type} [Field E] [NumberField E]

theorem trace_eq_sum_psi (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ ∈ Ψ, 2 * (τ z).re := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, NativeNumberFieldLattice.trace_eq_sum_complexEmbeddings, ← Finset.sum_add_sum_compl Ψ]

  have hc : ∑ σ ∈ Ψᶜ, σ z = ∑ τ ∈ Ψ, conj (τ z) := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_coe, Finset.mem_compl] at hσ ⊢
      rw [hΨ, show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ from star_star σ]
      exact hσ
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_compl]
      exact (hΨ τ).mp hτ
    · intro σ _; exact star_star σ
    · intro τ _; exact star_star τ
    · intro σ _; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [hc, ← Finset.sum_add_distrib, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Complex.add_conj]

end FieldTrace

section GlobalTheory

variable {ι n : Type} [Fintype n]

def blk (N : ι → Matrix n n ℂ) : (ι → n → ℂ) →ₗ[ℝ] (ι → n → ℂ) where
  toFun u τ := N τ *ᵥ u τ
  map_add' u v := by ext τ : 1; simp [Matrix.mulVec_add]
  map_smul' c u := by
    ext τ i
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Matrix.mulVec_smul]
    rfl

theorem blk_apply (N : ι → Matrix n n ℂ) (u : ι → n → ℂ) (τ : ι) : blk N u τ = N τ *ᵥ u τ := rfl

theorem blk_comp (N N' : ι → Matrix n n ℂ) : blk N ∘ₗ blk N' = blk (fun τ => N τ * N' τ) := by
  apply LinearMap.ext
  intro u
  funext τ
  simp only [LinearMap.comp_apply, blk_apply, Matrix.mulVec_mulVec]

def blkC (N : ι → Matrix n n ℂ) : (ι → n → ℂ) →ₗ[ℂ] (ι → n → ℂ) where
  toFun u τ := N τ *ᵥ u τ
  map_add' u v := by ext τ : 1; simp [Matrix.mulVec_add]
  map_smul' c u := by ext τ : 1; simp [Matrix.mulVec_smul]

theorem blk_eq_restrict (N : ι → Matrix n n ℂ) : blk N = (blkC N).restrictScalars ℝ := rfl

theorem trace_restrict_complex {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    [IsScalarTower ℝ ℂ M] [Module.Free ℂ M] [Module.Finite ℂ M] (f : M →ₗ[ℂ] M) :
    LinearMap.trace ℝ M (f.restrictScalars ℝ) = 2 * (LinearMap.trace ℂ M f).re := by
  classical
  let c := Module.Free.chooseBasis ℂ M
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower c), LinearMap.trace_eq_matrix_trace ℂ c]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr,
    Fintype.sum_prod_type, LinearMap.restrictScalars_apply, LinearMap.map_smul, map_smul, Finsupp.smul_apply,
    smul_eq_mul, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, Fin.sum_univ_two]
  simp [Complex.re_sum, Finset.mul_sum, Finset.sum_add_distrib, two_mul]

theorem trace_blkC [Fintype ι] [DecidableEq ι] [DecidableEq n] (N : ι → Matrix n n ℂ) :
    LinearMap.trace ℂ _ (blkC N) = ∑ τ, (N τ).trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis fun _ : ι => Pi.basisFun ℂ n)]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_sigma, blkC, Matrix.mulVec_single_one]

theorem trace_blk [Fintype ι] [DecidableEq ι] [DecidableEq n] (N : ι → Matrix n n ℂ) :
    LinearMap.trace ℝ _ (blk N) = ∑ τ, 2 * (N τ).trace.re := by
  rw [blk_eq_restrict, trace_restrict_complex, trace_blkC, Complex.re_sum, Finset.mul_sum]

end GlobalTheory


section Diagonal

/-- The actual diagonal Gram matrix of the prescribed standard frame. -/
def diagonalGram {N : ℕ} (neg : Fin N → Bool) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => sgn (neg i)

/-- Multiplication by i on positive coordinates and -i on negative ones. -/
def diagonalJ {N : ℕ} (neg : Fin N → Bool) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => Complex.I * sgn (neg i)

theorem diagonalGram_apply {N : ℕ} (neg : Fin N → Bool) (u : Fin N → ℂ) (i : Fin N) :
    (diagonalGram neg *ᵥ u) i = sgn (neg i) * u i :=
  Matrix.mulVec_diagonal _ _ _

theorem diagonalJ_apply {N : ℕ} (neg : Fin N → Bool) (u : Fin N → ℂ) (i : Fin N) :
    (diagonalJ neg *ᵥ u) i = Complex.I * sgn (neg i) * u i :=
  Matrix.mulVec_diagonal _ _ _

theorem diagonalJ_sq {N : ℕ} (neg : Fin N → Bool) (u : Fin N → ℂ) :
    diagonalJ neg *ᵥ (diagonalJ neg *ᵥ u) = -u := by
  funext i
  simp only [diagonalJ_apply, Pi.neg_apply]
  calc Complex.I * sgn (neg i) * (Complex.I * sgn (neg i) * u i) =
      (Complex.I * Complex.I) * (sgn (neg i) * sgn (neg i)) * u i := by ring
    _ = -u i := by rw [Complex.I_mul_I, sgn_mul_self, mul_one, neg_one_mul]

theorem diagonalJ_isometry {N : ℕ} (neg : Fin N → Bool) (u v : Fin N → ℂ) :
    star (diagonalJ neg *ᵥ u) ⬝ᵥ (diagonalGram neg *ᵥ (diagonalJ neg *ᵥ v)) =
      star u ⬝ᵥ (diagonalGram neg *ᵥ v) := by
  simp only [dotProduct, Pi.star_apply, diagonalGram_apply, diagonalJ_apply,
    star_mul', star_sgn, Complex.star_def, Complex.conj_I]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc (-Complex.I * sgn (neg i) * conj (u i)) *
        (sgn (neg i) * (Complex.I * sgn (neg i) * v i)) =
      -(Complex.I * Complex.I) * (sgn (neg i) * sgn (neg i)) *
        (conj (u i) * (sgn (neg i) * v i)) := by ring
    _ = conj (u i) * (sgn (neg i) * v i) := by
      rw [Complex.I_mul_I, neg_neg, sgn_mul_self, mul_one, one_mul]

theorem star_dot_self_eq {N : ℕ} (u : Fin N → ℂ) :
    star u ⬝ᵥ u = ((∑ i, Complex.normSq (u i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum,
    Complex.normSq_eq_conj_mul_self, Complex.star_def]

theorem sum_normSq_pos {N : ℕ} {u : Fin N → ℂ} (hu : u ≠ 0) :
    0 < ∑ i, Complex.normSq (u i) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩

/-- The first argument is conjugated, fixing the source's negative-i sign. -/
theorem diagonalJ_pairing {N : ℕ} (neg : Fin N → Bool) (u : Fin N → ℂ) :
    star (diagonalJ neg *ᵥ u) ⬝ᵥ (diagonalGram neg *ᵥ u) =
      -(Complex.I * ((∑ i, Complex.normSq (u i) : ℝ) : ℂ)) := by
  have h : star (diagonalJ neg *ᵥ u) ⬝ᵥ (diagonalGram neg *ᵥ u) =
      (-Complex.I) * (star u ⬝ᵥ u) := by
    simp only [dotProduct, Pi.star_apply, diagonalGram_apply, diagonalJ_apply,
      star_mul', star_sgn, Complex.star_def, Complex.conj_I, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc (-Complex.I * sgn (neg i) * conj (u i)) * (sgn (neg i) * u i) =
        (-Complex.I) * (sgn (neg i) * sgn (neg i)) * (conj (u i) * u i) := by ring
      _ = (-Complex.I) * (conj (u i) * u i) := by rw [sgn_mul_self, mul_one]
  rw [h, star_dot_self_eq, neg_mul]

theorem re_mul_negI (c : ℂ) (ρ : ℝ) :
    (c * -(Complex.I * ρ)).re = ρ * c.im := by
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem diagonalJ_term_pos {N : ℕ} (neg : Fin N → Bool) (c : ℂ) (hc : 0 < c.im)
    (u : Fin N → ℂ) :
    0 ≤ 2 * (c * (star (diagonalJ neg *ᵥ u) ⬝ᵥ (diagonalGram neg *ᵥ u))).re ∧
      (u ≠ 0 →
        0 < 2 * (c * (star (diagonalJ neg *ᵥ u) ⬝ᵥ (diagonalGram neg *ᵥ u))).re) := by
  rw [diagonalJ_pairing, re_mul_negI]
  constructor
  · exact mul_nonneg (by norm_num)
      (mul_nonneg (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) hc.le)
  · intro hu
    exact mul_pos (by norm_num) (mul_pos (sum_normSq_pos hu) hc)

theorem dot_smul_real {n : Type} [Fintype n] (G : Matrix n n ℂ)
    (a a' : ℝ) (u w : n → ℂ) :
    star (fun i => (a : ℂ) * u i) ⬝ᵥ (G *ᵥ fun i => (a' : ℂ) * w i) =
      ((a * a' : ℝ) : ℂ) * (star u ⬝ᵥ (G *ᵥ w)) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Complex.star_def, map_mul,
    Complex.conj_ofReal, Finset.mul_sum, Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- Count the actual negative tail by its explicit finite-coordinate permutation. -/
theorem sum_sgn_negTail (N q : ℕ) (hq : q ≤ N) :
    (∑ i : Fin N, (sgn (negTail N q i) : ℂ)) = ((N - q : ℕ) : ℂ) - q := by
  let e : Fin N ≃ Fin (N - q) ⊕ Fin q :=
    (finCongr (by omega : N = (N - q) + q)).trans finSumFinEquiv.symm
  have hl : ∀ i, ((e.symm (Sum.inl i) : Fin N) : ℕ) = i := fun i => by simp [e]
  have hr : ∀ i, ((e.symm (Sum.inr i) : Fin N) : ℕ) = N - q + i := fun i => by simp [e]
  rw [← Equiv.sum_comp e.symm]
  rw [Fintype.sum_sum_type]
  have hpos : ∀ i : Fin (N - q), negTail N q (e.symm (Sum.inl i)) = false :=
    fun i => negTail_false _ _ _ (by rw [hl]; exact i.isLt)
  have hneg : ∀ i : Fin q, negTail N q (e.symm (Sum.inr i)) = true :=
    fun i => negTail_true _ _ _ (by rw [hr]; omega)
  simp [hpos, hneg, sgn, sub_eq_add_neg]

theorem diagonalJ_tail_trace (N q : ℕ) (hq : q ≤ N) :
    (diagonalJ (negTail N q)).trace =
      Complex.I * (((N - q : ℕ) : ℂ) - q) := by
  rw [diagonalJ, Matrix.trace_diagonal, ← Finset.mul_sum, sum_sgn_negTail N q hq]

end Diagonal

end RHLean.Geometry.NativePolarizationComplexCoordinates

end
