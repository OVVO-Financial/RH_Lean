import RHLean.Geometry.NativeThetaGridParametrization

/-!
# Integral and metric bounds for the actual theta vector grid

The Hermitian pairing is the canonical CM conjugate pairing. The integral
perpendicular construction stays in the same supplied lattice, and the
complex-embedding norm estimate retains the source factorial and degree cost.
All coefficient-polynomial estimates use the independent target field's
embeddings; the host field is used only for the input lattice vectors.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`L1NormRowBlockLeadingMinorProductLe.lean`, and
`ExistsShortHarmonicFamilyLinear.lean`, hermPairing/perpVec_hermPairing_mem;
`Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean`,
the linear-form coefficient estimate. The source archive/mirror states no
license; this notice preserves attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace RHLean.Geometry.NativeTheta

namespace CoeffNorm

open MvPolynomial Finset

variable {σ K : Type*} [NormedCommRing K]

theorem sum_le_sqrt_card_mul_sqrt_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, f i ≤ √(#s) * √(∑ i ∈ s, f i ^ 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.le_sqrt_of_sq_le sq_sum_le_card_mul_sum_sq

theorem l1Norm_linearForm_le_sum {ι : Type*} (s : Finset ι) (v : ι → σ) (e : ι → K) :
    l1Norm (∑ k ∈ s, C (e k) * X (v k) : MvPolynomial σ K) ≤ ∑ k ∈ s, ‖e k‖ := by
  refine (l1Norm_sum_le _ _).trans_eq (sum_congr rfl fun k _ ↦ ?_)
  rw [C_mul_X_eq_monomial, l1Norm_monomial]

theorem l1Norm_linearForm_le {ι : Type*} [Fintype ι] (v : ι → σ) (e : ι → K) :
    l1Norm (∑ k, C (e k) * X (v k) : MvPolynomial σ K) ≤
      √(Fintype.card ι) * √(∑ k, ‖e k‖ ^ 2) :=
  (l1Norm_linearForm_le_sum _ v e).trans (sum_le_sqrt_card_mul_sqrt_sum_sq _ _)

end CoeffNorm

namespace GridBounds

open NumberField Paired CoeffNorm

section Minor

variable {T : Type*} {p q n : ℕ}

theorem l1Norm_rowBlockLinearForm_le (t : T) (r : Fin p ⊕ Fin q) (v : Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hv : ∑ k, ‖v k‖ ^ 2 ≤ R ^ 2) : l1Norm (rowForm t r v) ≤ √(n : ℝ) * R := by
  rw [rowForm_apply]
  refine (l1Norm_linearForm_le (fun k => (t, r, k)) v).trans ?_
  rw [Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hR, hv⟩) (Real.sqrt_nonneg _)

theorem l1Norm_det_le_of_entry_bound {σ : Type*} {i N : ℕ} (hi : i ≤ N)
    (M : Matrix (Fin i) (Fin i) (MvPolynomial σ ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ a b, l1Norm (M a b) ≤ B) : l1Norm M.det ≤ (N * B) ^ i := by
  refine (l1Norm_det_le_pow M h).trans ?_
  rw [Fintype.card_fin]
  have : (i : ℝ) ≤ N := by exact_mod_cast hi
  gcongr

theorem l1Norm_rowBlockLeadingMinorProduct_le [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → Fin n → ℂ) (φ : T → Fin q → Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hε : ∀ t a, ∑ k, ‖ε t a k‖ ^ 2 ≤ R ^ 2) (hφ : ∀ t b, ∑ k, ‖φ t b k‖ ^ 2 ≤ R ^ 2)
    {N : ℕ} (hp : p ≤ N) (hq : q ≤ N) :
    l1Norm (minorProd c c' ε φ) ≤ (N * √(n : ℝ) * R) ^ typeDegree c c' := by
  have hB : 0 ≤ √(n : ℝ) * R := by positivity
  rw [minorProd, typeDegree, ← Finset.prod_pow_eq_pow_sum, mul_assoc]
  refine (l1Norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun _ _ => l1Norm_nonneg _) fun t _ => ?_)
  rw [pow_add]
  refine (l1Norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (l1Norm_nonneg _) (by positivity))
  · refine (l1Norm_prod_pow_le _ _ _ (fun i => (N * (√(n : ℝ) * R)) ^ (i.val + 1))
      fun i _ => ?_).trans_eq ?_
    · exact l1Norm_det_le_of_entry_bound (by have := i.isLt; omega) _ hB
        fun a b => l1Norm_rowBlockLinearForm_le _ _ _ hR (hε _ _)
    · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, partSize]
  · refine (l1Norm_prod_pow_le _ _ _ (fun i => (N * (√(n : ℝ) * R)) ^ (i.val + 1))
      fun i _ => ?_).trans_eq ?_
    · exact l1Norm_det_le_of_entry_bound (by have := i.isLt; omega) _ hB
        fun a b => l1Norm_rowBlockLinearForm_le _ _ _ hR (hφ _ _)
    · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, partSize]

end Minor

section Length

variable {E : Type*} [CommRing E] {κ : Type*} [Fintype κ]

noncomputable def embSeminorm (τ : E →+* ℂ) : RingSeminorm E where
  toFun x := ‖τ x‖
  map_zero' := by simp
  add_le' x y := by rw [map_add]; exact norm_add_le _ _
  neg' x := by simp
  mul_le' x y := by simp

@[simp] theorem embSeminorm_apply (τ : E →+* ℂ) (x : E) : embSeminorm τ x = ‖τ x‖ := rfl

noncomputable def embVec (τ : E →+* ℂ) : (κ → E) →+ EuclideanSpace ℂ κ where
  toFun v := WithLp.toLp 2 fun k => τ (v k)
  map_zero' := by ext k; simp
  map_add' v w := by ext k; simp

omit [Fintype κ] in

@[simp] theorem embVec_apply (τ : E →+* ℂ) (v : κ → E) (k : κ) : embVec τ v k = τ (v k) := rfl

omit [Fintype κ] in

theorem embVec_smul (τ : E →+* ℂ) (x : E) (v : κ → E) : embVec τ (x • v) = τ x • embVec τ v := by
  ext k; simp

noncomputable def embLength (τ : E →+* ℂ) : AddGroupSeminorm (κ → E) where
  toFun v := ‖embVec τ v‖
  map_zero' := by simp
  add_le' x y := by rw [map_add]; exact norm_add_le _ _
  neg' x := by simp

theorem embLength_apply (τ : E →+* ℂ) (v : κ → E) : embLength τ v = ‖embVec τ v‖ := rfl

theorem embLength_sq (τ : E →+* ℂ) (v : κ → E) : embLength τ v ^ 2 = ∑ k, ‖τ (v k)‖ ^ 2 := by
  rw [embLength_apply, EuclideanSpace.norm_sq_eq]; rfl

theorem embLength_smul (τ : E →+* ℂ) (x : E) (v : κ → E) :
    embLength τ (x • v) = ‖τ x‖ * embLength τ v := by
  rw [embLength_apply, embVec_smul, norm_smul, embLength_apply]

theorem embLength_le_abs (τ : E →+* ℂ) {v : κ → E} {R : ℝ} (h : ∑ k, ‖τ (v k)‖ ^ 2 ≤ R ^ 2) :
    embLength τ v ≤ |R| :=
  (le_abs_self _).trans (sq_le_sq.mp (by rwa [embLength_sq]))

theorem sum_sq_le_of_embLength_le (τ : E →+* ℂ) {v : κ → E} {R : ℝ} (h : embLength τ v ≤ |R|) :
    ∑ k, ‖τ (v k)‖ ^ 2 ≤ R ^ 2 := by
  rw [← embLength_sq, ← sq_abs R]
  exact pow_le_pow_left₀ (apply_nonneg _ _) h 2

theorem norm_emb_sum_mul_le (τ : E →+* ℂ) (s : E → E) (hs : ∀ x, ‖τ (s x)‖ = ‖τ x‖)
    (x y : κ → E) : ‖τ (∑ k, x k * s (y k))‖ ≤ embLength τ x * embLength τ y := by
  rw [map_sum]
  refine (norm_sum_le _ _).trans ?_
  simp only [map_mul, norm_mul, hs]
  refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_
    (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  rw [mul_pow, embLength_sq, embLength_sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem sum_sq_combination_le (τ : E →+* ℂ) {ι : Type*} [Fintype ι] (v : ι → κ → E) {ρ : ℝ}
    (hv : ∀ i, ∑ k, ‖τ (v i k)‖ ^ 2 ≤ ρ ^ 2) (A : ι → ℕ) {d : ℕ} (hA : ∀ i, A i ≤ d) :
    ∑ k, ‖τ ((∑ i, (A i : E) • v i) k)‖ ^ 2 ≤ ((Fintype.card ι : ℝ) * d * ρ) ^ 2 := by
  apply sum_sq_le_of_embLength_le
  rw [embLength_apply, map_sum, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast, mul_assoc,
    ← nsmul_eq_mul, ← Finset.card_univ]
  refine (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_)
  rw [← embLength_apply, embLength_smul, map_natCast, Complex.norm_natCast]
  exact mul_le_mul (by exact_mod_cast hA i) (embLength_le_abs τ (hv i)) (apply_nonneg _ _)
    (Nat.cast_nonneg _)

end Length

section Perp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {p n : ℕ}

theorem sum_sq_perpVec_le (τ : E →+* ℂ) (h : (Fin n → E) →ₗ[E] ((Fin n → E) → E))
    (hh : ∀ x y, h x y = ∑ k, x k * IsCMField.complexConj E (y k)) (e e' : Fin p → Fin n → E) (g : Fin n → E) {R : ℝ}
    (he : ∀ a, ∑ k, ‖τ (e a k)‖ ^ 2 ≤ R ^ 2) (he' : ∀ a, ∑ k, ‖τ (e' a k)‖ ^ 2 ≤ R ^ 2)
    (hg : ∑ k, ‖τ (g k)‖ ^ 2 ≤ R ^ 2) :
    ∑ k, ‖τ (perpVec h e e' g k)‖ ^ 2 ≤ (((p + 1).factorial : ℝ) * R ^ (2 * p + 1)) ^ 2 := by
  have hs : ∀ x, ‖τ (cc x)‖ = ‖τ x‖ := fun x => by
    rw [IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  have key : ∀ u v, embLength τ u ≤ |R| → embLength τ v ≤ |R| → ‖τ (h u v)‖ ≤ |R| ^ 2 :=
    fun u v hu hv => by
      rw [hh, sq]
      exact (norm_emb_sum_mul_le τ (IsCMField.complexConj E) hs u v).trans
        (mul_le_mul hu hv (apply_nonneg _ _) (abs_nonneg _))
  apply sum_sq_le_of_embLength_le
  rw [perpVec_eq_perpVector, abs_mul, Nat.abs_cast, abs_pow, pow_succ, pow_mul, ← mul_assoc]
  exact Perpendicular.seminorm_perpVector_le (embSeminorm τ) (by simp) (embLength τ)
    (fun x v => (embLength_smul τ x v).le) _ e' g
    (fun a a' => key _ _ (embLength_le_abs τ (he' a')) (embLength_le_abs τ (he a)))
    (fun a => key _ _ (embLength_le_abs τ hg) (embLength_le_abs τ (he a)))
    (fun a => embLength_le_abs τ (he' a)) (embLength_le_abs τ hg)

end Perp

end GridBounds

namespace Paired

open NumberField

/-- The original Hermitian form, defined from the canonical CM conjugation. -/
def hermPairing (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (Fin n → E) →ₗ[E] ((Fin n → E) → E) where
  toFun x y := ∑ k, x k * IsCMField.complexConj E (y k)
  map_add' x x' := funext fun y => by
    change (∑ k, (x k + x' k) * IsCMField.complexConj E (y k)) =
      (∑ k, x k * IsCMField.complexConj E (y k)) +
        ∑ k, x' k * IsCMField.complexConj E (y k)
    simp only [add_mul, Finset.sum_add_distrib]
  map_smul' r x := funext fun y => by
    change (∑ k, (r * x k) * IsCMField.complexConj E (y k)) =
      r * ∑ k, x k * IsCMField.complexConj E (y k)
    simp only [Finset.mul_sum, mul_assoc]

@[simp] theorem hermPairing_apply (E : Type) [Field E] [NumberField E] [IsCMField E]
    (n : ℕ) (x y : Fin n → E) :
    hermPairing E n x y = ∑ k, x k * IsCMField.complexConj E (y k) := rfl

/-- Adjugates preserve the actual integral lattice: no inverse or new lattice
is chosen by the perpendicular construction. -/
theorem perpVec_hermPairing_mem
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n p : ℕ}
    {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y))
    {e e' : Fin p → Fin n → E} {g : Fin n → E}
    (he : ∀ a, e a ∈ Λ) (he' : ∀ a, e' a ∈ Λ) (hg : g ∈ Λ) :
    perpVec (hermPairing E n) e e' g ∈ Λ := by
  rw [perpVec_eq_perpVector]
  exact Perpendicular.perpVector_mem Λ
    (fun a => (LinearMap.proj (e a)).comp (hermPairing E n)) he' hg
    (fun a a' => ⟨⟨_, hint _ (he' a') _ (he a)⟩, rfl⟩)
    (fun a => ⟨⟨_, hint _ hg _ (he a)⟩, rfl⟩)

end Paired

end RHLean.Geometry.NativeTheta

end
