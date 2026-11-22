import Mathlib

/-!
# Coefficient norms for the concrete native theta polynomials

This is the finite polynomial norm calculation used by the original harmonic
polynomial constructor. The coefficient number field K remains independent of
the CM host E. In the geometric application K is Y.d.c₂.F.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
Development/AbelianVarietyTheory/Definitions/ThetaMetrics/
SumFinsuppAntidiagProdPowDivMultiFactorial.lean, GlobalTheory.MvPoly.l1Norm
and its finite sum/product/determinant inequalities; and
Proofs/DivisorProofs/PolynomialCoefficientEmbeddingNormLeOfL1Bound.lean,
CovGmin.PrismSpan.polynomialCoefficientEmbeddingNorm_le_of_l1Bound.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativeTheta.CoeffNorm

open MvPolynomial Finset

variable {σ : Type*}

section L1

variable {K : Type*} [NormedCommRing K]

def l1Norm (P : MvPolynomial σ K) : ℝ := ∑ α ∈ P.support, ‖P.coeff α‖

theorem l1Norm_eq_sum_of_subset {P : MvPolynomial σ K} {s : Finset (σ →₀ ℕ)}
    (h : P.support ⊆ s) : l1Norm P = ∑ α ∈ s, ‖P.coeff α‖ :=
  sum_subset h fun α _ hα ↦ by rw [notMem_support_iff.mp hα, norm_zero]

theorem l1Norm_nonneg (P : MvPolynomial σ K) : 0 ≤ l1Norm P :=
  sum_nonneg fun _ _ ↦ norm_nonneg _

theorem sum_norm_coeff_le_l1Norm (P : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) :
    ∑ α ∈ s, ‖P.coeff α‖ ≤ l1Norm P := by
  classical
  rw [l1Norm_eq_sum_of_subset (s := P.support ∪ s) subset_union_left]
  exact sum_le_sum_of_subset_of_nonneg subset_union_right fun _ _ _ ↦ norm_nonneg _

theorem norm_coeff_le_l1Norm (P : MvPolynomial σ K) (α : σ →₀ ℕ) : ‖P.coeff α‖ ≤ l1Norm P := by
  simpa using sum_norm_coeff_le_l1Norm P {α}

@[simp] theorem l1Norm_zero : l1Norm (0 : MvPolynomial σ K) = 0 := by simp [l1Norm]

@[simp] theorem l1Norm_eq_zero {P : MvPolynomial σ K} : l1Norm P = 0 ↔ P = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ l1Norm_zero⟩
  ext α
  simpa using norm_le_zero_iff.mp (h ▸ norm_coeff_le_l1Norm P α)

@[simp] theorem l1Norm_monomial (α : σ →₀ ℕ) (c : K) : l1Norm (monomial α c) = ‖c‖ := by
  classical
  rw [l1Norm_eq_sum_of_subset (s := {α}) support_monomial_subset]
  simp

@[simp] theorem l1Norm_C (c : K) : l1Norm (C c : MvPolynomial σ K) = ‖c‖ := l1Norm_monomial 0 c

@[simp] theorem l1Norm_one [NormOneClass K] : l1Norm (1 : MvPolynomial σ K) = 1 := by
  rw [← C_1, l1Norm_C, norm_one]

@[simp] theorem l1Norm_X [NormOneClass K] (i : σ) : l1Norm (X i : MvPolynomial σ K) = 1 := by
  rw [X, l1Norm_monomial, norm_one]

@[simp] theorem l1Norm_neg (P : MvPolynomial σ K) : l1Norm (-P) = l1Norm P := by
  simp [l1Norm]

theorem l1Norm_add_le (P Q : MvPolynomial σ K) : l1Norm (P + Q) ≤ l1Norm P + l1Norm Q := by
  classical
  rw [l1Norm_eq_sum_of_subset (s := P.support ∪ Q.support) support_add,
    l1Norm_eq_sum_of_subset (s := P.support ∪ Q.support) subset_union_left,
    l1Norm_eq_sum_of_subset (s := P.support ∪ Q.support) subset_union_right, ← sum_add_distrib]
  exact sum_le_sum fun α _ ↦ by rw [coeff_add]; exact norm_add_le _ _

theorem l1Norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    l1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1Norm (f i) :=
  Finset.le_sum_of_subadditive l1Norm l1Norm_zero.le l1Norm_add_le s f

theorem l1Norm_mul_le (P Q : MvPolynomial σ K) : l1Norm (P * Q) ≤ l1Norm P * l1Norm Q := by
  conv_lhs => rw [P.as_sum, Q.as_sum, sum_mul_sum]
  refine (l1Norm_sum_le _ _).trans ?_
  rw [l1Norm, l1Norm, sum_mul_sum]
  refine sum_le_sum fun α _ ↦ (l1Norm_sum_le _ _).trans (sum_le_sum fun β _ ↦ ?_)
  rw [monomial_mul, l1Norm_monomial]
  exact norm_mul_le _ _

theorem l1Norm_prod_le [NormOneClass K] {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    l1Norm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (l1Norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (l1Norm_nonneg _))

theorem l1Norm_pow_le [NormOneClass K] (P : MvPolynomial σ K) (n : ℕ) :
    l1Norm (P ^ n) ≤ l1Norm P ^ n := by
  simpa using l1Norm_prod_le (range n) fun _ ↦ P

theorem l1Norm_prod_pow_le [NormOneClass K] {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ K) (c : ι → ℕ) (B : ι → ℝ) (h : ∀ i ∈ s, l1Norm (f i) ≤ B i) :
    l1Norm (∏ i ∈ s, f i ^ c i) ≤ ∏ i ∈ s, B i ^ c i :=
  (l1Norm_prod_le _ _).trans <| prod_le_prod₀ (fun _ _ ↦ l1Norm_nonneg _) fun i hi ↦
    (l1Norm_pow_le _ _).trans (pow_le_pow_left₀ (l1Norm_nonneg _) (h i hi) _)

theorem l1Norm_map {R : Type*} [CommSemiring R] (φ : R →+* K) (P : MvPolynomial σ R) :
    l1Norm (map φ P) = ∑ α ∈ P.support, ‖φ (P.coeff α)‖ := by
  rw [l1Norm_eq_sum_of_subset (support_map_subset φ P)]
  simp [coeff_map]

theorem l1Norm_det_le [NormOneClass K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ K)) {R : ℝ} (h : ∀ a b, l1Norm (M a b) ≤ R) :
    l1Norm M.det ≤ (Fintype.card ι).factorial * R ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine (l1Norm_sum_le _ _).trans ?_
  rw [← Fintype.card_perm, ← nsmul_eq_mul, ← card_univ (α := Equiv.Perm ι)]
  refine sum_le_card_nsmul _ _ _ fun π _ ↦ ?_
  have h1 : l1Norm (Equiv.Perm.sign π • ∏ i, M (π i) i) = l1Norm (∏ i, M (π i) i) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  rw [h1]
  refine (l1Norm_prod_le _ _).trans ?_
  rw [← card_univ, ← prod_const]
  exact prod_le_prod₀ (fun _ _ ↦ l1Norm_nonneg _) fun _ _ ↦ h _ _

theorem factorial_mul_pow_le (i : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (i.factorial : ℝ) * R ^ i ≤ (i * R) ^ i := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le_pow i) (pow_nonneg hR _)

theorem l1Norm_det_le_pow [NormOneClass K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ K)) {R : ℝ} (h : ∀ a b, l1Norm (M a b) ≤ R) :
    l1Norm M.det ≤ (Fintype.card ι * R) ^ Fintype.card ι := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨a⟩⟩
  · simp
  · exact (l1Norm_det_le M h).trans (factorial_mul_pow_le _ ((l1Norm_nonneg _).trans (h a a)))

end L1

section NumberField

open NumberField

variable {K : Type} [Field K] [NumberField K]

/-- The same all-embedding coefficient norm used by ThetaWeightData.polyNorm. -/
def allEmbeddingNorm (P : MvPolynomial σ K) : ℝ :=
  Real.sqrt (∑ s : K →+* ℂ, ∑ m ∈ P.support, ‖s (P.coeff m)‖ ^ 2)

/-- The original coefficient-field factor is retained literally. -/
theorem allEmbeddingNorm_le_of_l1Bound (P : MvPolynomial σ K) (B : ℝ)
    (hB : 0 ≤ B) (h : ∀ s : K →+* ℂ, ∑ m ∈ P.support, ‖s (P.coeff m)‖ ≤ B) :
    allEmbeddingNorm P ≤ Real.sqrt (Module.finrank ℚ K) * B := by
  unfold allEmbeddingNorm
  rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  have hs : ∀ s : K →+* ℂ, ∑ m ∈ P.support, ‖s (P.coeff m)‖ ^ 2 ≤ B ^ 2 := by
    intro s
    let S := ∑ m ∈ P.support, ‖s (P.coeff m)‖
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc ∑ m ∈ P.support, ‖s (P.coeff m)‖ ^ 2 ≤ ∑ m ∈ P.support, ‖s (P.coeff m)‖ * S := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [sq]
          exact mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun m => ‖s (P.coeff m)‖)
              (fun _ _ => norm_nonneg _) hm) (norm_nonneg _)
      _ = S * S := by rw [← Finset.sum_mul]
      _ ≤ B * B := mul_le_mul (h s) (h s) hS0 hB
      _ = B ^ 2 := (sq B).symm
  calc ∑ s : K →+* ℂ, ∑ m ∈ P.support, ‖s (P.coeff m)‖ ^ 2 ≤
        ∑ _s : K →+* ℂ, B ^ 2 := Finset.sum_le_sum fun s _ => hs s
    _ = (Module.finrank ℚ K : ℝ) * B ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card K ℂ, nsmul_eq_mul]

end NumberField

end RHLean.Geometry.NativeTheta.CoeffNorm

end
