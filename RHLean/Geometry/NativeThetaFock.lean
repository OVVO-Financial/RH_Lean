import Mathlib

/-!
# The positive Fock coefficient pairing used in actual orbit generation

Only the finite factorial-weighted coefficient pairing, its derivative
adjoints and its orthogonal projection onto a finite-dimensional polynomial
space are needed here. Positivity is proved directly from the coefficient
sum, so no analytic Gaussian integral construction is imported.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/`
`SumFinsuppAntidiagProdPowDivMultiFactorial.lean`, Fock;
and `Proofs/CovolumeBounds/EventuallyExistsMulIsLowerTriangular.lean`,
`exists_fockInner_sub_eq_zero`.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MvPolynomial Finset

namespace RHLean.Geometry.NativeTheta.Fock

variable {σ K L : Type*}

def multiFactorial (α : σ →₀ ℕ) : ℕ := α.prod fun _ n => n.factorial

def fockNormSq [NormedCommRing K] (P : MvPolynomial σ K) : ℝ :=
  ∑ α ∈ P.support, (multiFactorial α : ℝ) * ‖P.coeff α‖ ^ 2

def fockInner {𝕜 : Type*} [RCLike 𝕜] (P Q : MvPolynomial σ 𝕜) : 𝕜 :=
  ∑ α ∈ P.support, (multiFactorial α : 𝕜) * (P.coeff α * starRingEnd 𝕜 (Q.coeff α))

section Fock

theorem multiFactorial_pos (α : σ →₀ ℕ) : 0 < multiFactorial α :=
  prod_pos fun _ _ ↦ Nat.factorial_pos _

@[simp] theorem multiFactorial_zero : multiFactorial (0 : σ →₀ ℕ) = 1 := by simp [multiFactorial]

@[simp] theorem multiFactorial_single (i : σ) (n : ℕ) :
    multiFactorial (Finsupp.single i n) = n.factorial :=
  Finsupp.prod_single_index rfl

theorem multiFactorial_add_single (α : σ →₀ ℕ) (i : σ) :
    multiFactorial (α + Finsupp.single i 1) = (α i + 1) * multiFactorial α := by
  classical
  have h1 : ∀ β : σ →₀ ℕ, β.support ⊆ insert i α.support →
      multiFactorial β = (β i).factorial * ∏ j ∈ (insert i α.support).erase i, (β j).factorial :=
    fun β hβ ↦ by
      rw [multiFactorial, Finsupp.prod_of_support_subset β hβ _ fun _ _ ↦ rfl,
        mul_prod_erase _ (fun j ↦ (β j).factorial) (mem_insert_self _ _)]
  rw [h1 α (subset_insert _ _), h1 _ (Finsupp.support_add.trans ?_), ← mul_assoc]
  · congr 1
    · simp [Nat.factorial_succ]
    · refine prod_congr rfl fun j hj ↦ ?_
      simp [Finsupp.single_eq_of_ne (ne_of_mem_erase hj)]
  · exact union_subset (subset_insert _ _)
      (Finsupp.support_single_subset.trans (by simp))

variable [NormedCommRing K] [NormedCommRing L]

theorem fockNormSq_eq_sum_of_subset {P : MvPolynomial σ K} {s : Finset (σ →₀ ℕ)}
    (h : P.support ⊆ s) : fockNormSq P = ∑ α ∈ s, (multiFactorial α : ℝ) * ‖P.coeff α‖ ^ 2 :=
  sum_subset h fun α _ hα ↦ by simp [notMem_support_iff.mp hα]

theorem fockNormSq_nonneg (P : MvPolynomial σ K) : 0 ≤ fockNormSq P :=
  sum_nonneg fun _ _ ↦ by positivity

@[simp] theorem fockNormSq_zero : fockNormSq (0 : MvPolynomial σ K) = 0 := by simp [fockNormSq]

@[simp] theorem fockNormSq_monomial (α : σ →₀ ℕ) (c : K) :
    fockNormSq (monomial α c) = multiFactorial α * ‖c‖ ^ 2 := by
  classical
  rw [fockNormSq_eq_sum_of_subset (s := {α}) support_monomial_subset]
  simp

@[simp] theorem fockNormSq_eq_zero {P : MvPolynomial σ K} : fockNormSq P = 0 ↔ P = 0 := by
  classical
  refine ⟨fun h => ?_, fun h => h ▸ fockNormSq_zero⟩
  ext α
  change P.coeff α = 0
  by_cases hα : α ∈ P.support
  · have hα0 : (multiFactorial α : ℝ) * ‖P.coeff α‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun m _ =>
        mul_nonneg (Nat.cast_nonneg (multiFactorial m)) (sq_nonneg ‖P.coeff m‖))).mp h α hα
    have hm : (multiFactorial α : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (multiFactorial_pos α))
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hα0).resolve_left hm))
  · exact notMem_support_iff.mp hα

variable {𝕜 : Type*} [RCLike 𝕜]

theorem fockInner_eq_sum_of_subset_left {P : MvPolynomial σ 𝕜} (Q : MvPolynomial σ 𝕜)
    {s : Finset (σ →₀ ℕ)} (h : P.support ⊆ s) : fockInner P Q =
      ∑ α ∈ s, (multiFactorial α : 𝕜) * (P.coeff α * starRingEnd 𝕜 (Q.coeff α)) :=
  sum_subset h fun α _ hα ↦ by simp [notMem_support_iff.mp hα]

theorem fockInner_eq_sum_of_subset_right (P : MvPolynomial σ 𝕜) {Q : MvPolynomial σ 𝕜}
    {s : Finset (σ →₀ ℕ)} (h : Q.support ⊆ s) : fockInner P Q =
      ∑ α ∈ s, (multiFactorial α : 𝕜) * (P.coeff α * starRingEnd 𝕜 (Q.coeff α)) := by
  classical
  rw [fockInner_eq_sum_of_subset_left Q (s := P.support ∪ s) subset_union_left]
  exact (sum_subset subset_union_right fun α _ hα ↦ by
    simp [notMem_support_iff.mp fun h' ↦ hα (h h')]).symm

theorem fockInner_conj_symm (P Q : MvPolynomial σ 𝕜) :
    starRingEnd 𝕜 (fockInner P Q) = fockInner Q P := by
  rw [fockInner_eq_sum_of_subset_right Q (subset_refl P.support), fockInner, map_sum]
  exact sum_congr rfl fun α _ ↦ by simp [mul_comm]

theorem fockInner_add_left (P P' Q : MvPolynomial σ 𝕜) :
    fockInner (P + P') Q = fockInner P Q + fockInner P' Q := by
  simp only [fockInner_eq_sum_of_subset_right _ (subset_refl Q.support), AddMonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul,
    mul_add, sum_add_distrib]

theorem fockInner_smul_left (c : 𝕜) (P Q : MvPolynomial σ 𝕜) :
    fockInner (c • P) Q = c * fockInner P Q := by
  simp only [fockInner_eq_sum_of_subset_right _ (subset_refl Q.support), mul_sum]
  exact sum_congr rfl fun α _ ↦ by rw [coeff_smul, smul_eq_mul]; ring

theorem fockInner_add_right (P Q Q' : MvPolynomial σ 𝕜) :
    fockInner P (Q + Q') = fockInner P Q + fockInner P Q' := by
  simp only [fockInner, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, mul_add, sum_add_distrib]

theorem fockInner_smul_right (c : 𝕜) (P Q : MvPolynomial σ 𝕜) :
    fockInner P (c • Q) = starRingEnd 𝕜 c * fockInner P Q := by
  simp only [fockInner, mul_sum]
  exact sum_congr rfl fun α _ ↦ by rw [coeff_smul, smul_eq_mul, map_mul]; ring

def fockInnerₛₗ (σ 𝕜 : Type*) [RCLike 𝕜] :
    MvPolynomial σ 𝕜 →ₗ[𝕜] MvPolynomial σ 𝕜 →ₗ⋆[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (RingHom.id 𝕜) (starRingEnd 𝕜) fockInner fockInner_add_left
    fockInner_smul_left fockInner_add_right fockInner_smul_right

@[simp] theorem fockInnerₛₗ_apply (P Q : MvPolynomial σ 𝕜) :
    fockInnerₛₗ σ 𝕜 P Q = fockInner P Q := rfl

theorem fockInner_self (P : MvPolynomial σ 𝕜) : fockInner P P = (fockNormSq P : 𝕜) := by
  simp [fockInner, fockNormSq, RCLike.mul_conj]

theorem fockInner_monomial_left (α : σ →₀ ℕ) (c : 𝕜) (Q : MvPolynomial σ 𝕜) :
    fockInner (monomial α c) Q = multiFactorial α * (c * starRingEnd 𝕜 (Q.coeff α)) := by
  classical
  rw [fockInner_eq_sum_of_subset_left Q (s := {α}) support_monomial_subset]
  simp

theorem fockInner_monomial_right (P : MvPolynomial σ 𝕜) (α : σ →₀ ℕ) (c : 𝕜) :
    fockInner P (monomial α c) = multiFactorial α * (P.coeff α * starRingEnd 𝕜 c) := by
  classical
  rw [fockInner_eq_sum_of_subset_right P (s := {α}) support_monomial_subset]
  simp

theorem fockInner_X_mul_left (i : σ) (P Q : MvPolynomial σ 𝕜) :
    fockInner (X i * P) Q = fockInner P (pderiv i Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [X, monomial_mul_monomial, one_mul, fockInner_monomial_left, fockInner_monomial_left, coeff_pderiv,
      add_comm _ α, multiFactorial_add_single]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, map_mul, map_add, map_natCast, map_one]
    ring
  | add P P' h h' => rw [mul_add, fockInner_add_left, fockInner_add_left, h, h']

theorem fockInner_pderiv_left (i : σ) (P Q : MvPolynomial σ 𝕜) :
    fockInner (pderiv i P) Q = fockInner P (X i * Q) := by
  rw [← fockInner_conj_symm, ← fockInner_X_mul_left, fockInner_conj_symm]

end Fock

end RHLean.Geometry.NativeTheta.Fock

namespace RHLean.Geometry.NativeTheta.Paired

open RHLean.Geometry.NativeTheta.Fock

theorem exists_fockInner_sub_eq_zero {σ : Type*} (W : Submodule ℂ (MvPolynomial σ ℂ))
    [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) :
    ∃ Q ∈ W, ∀ w ∈ W, fockInner (P - Q) w = 0 := by
  let b := Module.finBasis ℂ W
  let L : MvPolynomial σ ℂ →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    LinearMap.pi fun i => (fockInnerₛₗ σ ℂ).flip (b i)
  have hL (P) (h : L P = 0) (w) (hw : w ∈ W) : fockInner P w = 0 := by
    have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)
    rw [map_sum, Submodule.subtype_apply] at this
    change _ = w at this
    rw [← this, ← fockInnerₛₗ_apply, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, fockInnerₛₗ_apply, fockInner_smul_right]
    exact mul_eq_zero_of_right _ (congrFun h i)
  have hinj : Function.Injective (L ∘ₗ W.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have := hL x hx x x.2
    rw [fockInner_self] at this
    exact Subtype.ext (fockNormSq_eq_zero.mp (RCLike.ofReal_eq_zero.mp this))
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
    (L P)
  exact ⟨x, x.2, hL _ (by rw [map_sub, ← hx]; simp)⟩

end RHLean.Geometry.NativeTheta.Paired

end
