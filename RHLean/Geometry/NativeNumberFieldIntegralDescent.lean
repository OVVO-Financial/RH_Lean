import RHLean.Geometry.NativeIntegralCompletion

/-!
# Integral descent at the complex embeddings

In a chosen integral basis a metric frame sends lattice coordinates to orthonormal
coordinates. Thus the frame used here is the inverse of Alpöge's frame `X`.
Squared slope is minus the mean log Gram determinant divided by the lattice rank.
-/

noncomputable section

open Module NumberField Matrix
open scoped BigOperators ComplexOrder Matrix

namespace RHLean.Geometry.NumberFieldDescent

variable {K : Type*} [Field K] [NumberField K]

/-- The two conjugate embeddings both occur in the field norm. -/
theorem prod_embedding_norm (a : 𝓞 K) :
    ∏ σ : K →+* ℂ, ‖σ (a : K)‖ = |(Algebra.norm ℤ a : ℝ)| := by
  classical
  have h := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ (a : K))
  rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ)
    (fun f => ‖f (a : K)‖) (fun φ => ‖φ (a : K)‖)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← h, ← Algebra.coe_norm_int]
  simp

theorem det_credit {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I (𝓞 K)) (hC : C.det ≠ 0) :
    1 ≤ ∏ σ : K →+* ℂ, ‖σ (C.det : K)‖ := by
  rw [prod_embedding_norm]
  exact_mod_cast Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hC)

theorem log_det_credit {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I (𝓞 K)) (hC : C.det ≠ 0) :
    0 ≤ ∑ σ : K →+* ℂ, Real.log ‖σ (C.det : K)‖ := by
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr
    ((map_ne_zero σ).mpr ((Subalgebra.coe_eq_zero _).not.mpr hC)))]
  exact Real.log_nonneg (det_credit C hC)

/-- An integral basis identifies the free lattice with `(𝓞 K)^I`. -/
structure Metric (K I : Type*) [Field K] [NumberField K] [Fintype I] [DecidableEq I] where
  frame : (K →+* ℂ) → Matrix I I ℂ
  nonsingular : ∀ σ, (frame σ).det ≠ 0

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def Metric.energy (A : Metric K I) (σ : K →+* ℂ) (x : I → K) : ℝ :=
  ∑ i, ‖((A.frame σ) *ᵥ (σ ∘ x)) i‖ ^ 2

def Metric.gramDet (A : Metric K I) (σ : K →+* ℂ) : ℝ :=
  ‖(A.frame σ).det‖ ^ 2

theorem gramDet_eq (A : Metric K I) (σ : K →+* ℂ) :
    (A.gramDet σ : ℂ) = ((A.frame σ)ᴴ * A.frame σ).det := by
  rw [det_mul, det_conjTranspose, RCLike.star_def, RCLike.conj_mul]
  simp [Metric.gramDet]

def Metric.slopeSq (A : Metric K I) : ℝ :=
  -(∑ σ, Real.log (A.gramDet σ)) / (Fintype.card (K →+* ℂ) * (Fintype.card I : ℝ))

abbrev integralEmbedding (σ : K →+* ℂ) : 𝓞 K →+* ℂ :=
  σ.comp (algebraMap (𝓞 K) K)

private theorem det_map_hom {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (C : Matrix I I R) : (C.map f).det = f C.det := (f.map_det C).symm

/-- Exact index factor in the transported squared volume at a single embedding. -/
theorem gram_transport (A : Metric K I) (C : Matrix I I (𝓞 K)) (σ : K →+* ℂ) :
    ‖(A.frame σ * C.map (integralEmbedding σ)).det‖ ^ 2 =
      ‖σ (C.det : K)‖ ^ 2 * A.gramDet σ := by
  rw [det_mul, norm_mul, mul_pow, det_map_hom]
  exact mul_comm _ _

/-- Squared covolume transport over every embedding, including the full index. -/
theorem prod_gram_transport (A : Metric K I) (C : Matrix I I (𝓞 K)) :
    ∏ σ, ‖(A.frame σ * C.map (integralEmbedding σ)).det‖ ^ 2 =
      |(Algebra.norm ℤ C.det : ℝ)| ^ 2 * ∏ σ, A.gramDet σ := by
  simp_rw [gram_transport]
  rw [Finset.prod_mul_distrib, Finset.prod_pow, prod_embedding_norm]

omit [DecidableEq J] in
/-- The selected columns are integral in the original target basis. -/
theorem integral_completion {r d : ℕ} (b : Basis (Fin r ⊕ Fin d) K (J → K))
    (v : Fin r → J → K) (hv : LinearIndependent K v)
    (S : Set (J → K)) (hS : Submodule.span K S = ⊤)
    (hi : ∀ x ∈ Set.range v ∪ S, ∀ i, ∃ a : 𝓞 K, b.repr x i = (a : K)) :
    ∃ (w : Fin d → J → K) (C : Matrix (Fin r ⊕ Fin d) (Fin r ⊕ Fin d) (𝓞 K)),
      (∀ j, w j ∈ S) ∧ b.toMatrix (Sum.elim v w) = C.map (algebraMap (𝓞 K) K) ∧
      C.det ≠ 0 := by
  classical
  obtain ⟨w, B, hl, hr, hw⟩ := nativeCompletionFromSpanningSetOver v hv
    (by simpa using finrank_eq_card_basis b) S hS
  have hmem (j) : B j ∈ Set.range v ∪ S := by
    cases j with
    | inl j => exact Or.inl ⟨j, (hl j).symm⟩
    | inr j => exact Or.inr (hr j ▸ hw j)
  choose C hC using fun i j => hi (B j) (hmem j) i
  let D : Matrix (Fin r ⊕ Fin d) (Fin r ⊕ Fin d) (𝓞 K) := C
  have hcoord : b.toMatrix (B : _ → _) = D.map (algebraMap (𝓞 K) K) :=
    Matrix.ext hC
  have hfamily : Sum.elim v w = (B : _ → _) := funext fun j => by
    cases j with
    | inl j => exact (hl j).symm
    | inr j => exact (hr j).symm
  refine ⟨w, D, hw, hfamily ▸ hcoord, ?_⟩
  have hd := congrArg Matrix.det (b.toMatrix_mul_toMatrix_flip B)
  rw [det_mul, det_one, hcoord, det_map_hom] at hd
  intro hz
  simp [hz] at hd

omit [NumberField K] in
private theorem embedding_dense [IsTotallyComplex K] (σ : K →+* ℂ) : DenseRange σ := by
  have h := Complex.subfield_eq_of_closed σ.fieldRange.isClosed_topologicalClosure
  rcases h with hr | ht
  · exfalso
    apply IsTotallyComplex.complexEmbedding_not_isReal σ
    ext x
    obtain ⟨y, hy⟩ : σ x ∈ Complex.ofRealHom.fieldRange :=
      hr ▸ σ.fieldRange.le_topologicalClosure ⟨x, rfl⟩
    simp [← hy]
  · rw [DenseRange, dense_iff_closure_eq]
    exact congrArg SetLike.coe ht

def columnEnergy {n : Type*} [Fintype n] (v : n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
private theorem diag_gram (M : Matrix J I ℂ) (i : I) :
    ((Mᴴ * M) i i).re = columnEnergy (M.col i) := by
  simp [columnEnergy, Matrix.mul_apply, Matrix.col, RCLike.star_def, RCLike.conj_mul, ← Complex.ofReal_pow]

private theorem complex_hadamard_fin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖M.det‖ ^ 2 ≤ ∏ i, columnEnergy (M.col i) := by
  let v (i : Fin n) : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (M.col i)
  have hd : finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := finrank_euclideanSpace
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hd v
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  have he : Matrix.gram ℂ v = Mᴴ * M := Matrix.gram_eq_conjTranspose_mul e v
  have hb := Matrix.gram_eq_conjTranspose_mul b v
  change Matrix.gram ℂ v = (b.toBasis.toMatrix v)ᴴ * b.toBasis.toMatrix v at hb
  have hnorm := congrArg (fun A => ‖(A : Matrix (Fin n) (Fin n) ℂ).det‖) (he.symm.trans hb)
  simp only [det_mul, norm_mul, det_conjTranspose, norm_star, ← sq] at hnorm
  rw [hnorm, ← Basis.det_apply, InnerProductSpace.gramSchmidtOrthonormalBasis_det hd v, norm_prod,
    ← Finset.prod_pow]
  apply Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
  intro i _
  have h : ‖inner ℂ (b i) (v i)‖ ≤ ‖v i‖ := by
    simpa using norm_inner_le_norm (𝕜 := ℂ) (b i) (v i)
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (EuclideanSpace.norm_sq_eq _)

open scoped MatrixOrder in
/-- Hadamard's determinant inequality for a positive semidefinite Hermitian matrix. -/
theorem hermitian_hadamard {G : Matrix I I ℂ} (hG : G.PosSemidef) :
    ‖G.det‖ ≤ ∏ i, (G i i).re := by
  classical
  let e := (Fintype.equivFin I).symm
  let M := CFC.sqrt G
  have hs : Mᴴ * M = G := by
    change star M * M = G
    rw [(CFC.sqrt_nonneg G).isSelfAdjoint.star_eq, ← sq, CFC.sq_sqrt G hG.nonneg]
  have h := complex_hadamard_fin (M.submatrix e e)
  rw [det_submatrix_equiv_self] at h
  have he (i) : columnEnergy ((M.submatrix e e).col i) = ((Mᴴ * M) (e i) (e i)).re := by
    rw [diag_gram]
    exact e.sum_comp (fun j => ‖M j (e i)‖ ^ 2)
  simp_rw [he, hs] at h
  rw [e.prod_comp (fun i => (G i i).re)] at h
  calc
    ‖G.det‖ = ‖(Mᴴ * M).det‖ := by rw [hs]
    _ = ‖M.det‖ ^ 2 := by simp [det_mul, sq]
    _ ≤ _ := h

omit [DecidableEq J] in
/-- The image volume is retained. Only the complementary columns pay Hadamard. -/
theorem split_gram_bound {D : Type*} [Fintype D] [DecidableEq D]
    (X : Matrix J I ℂ) (Y : Matrix J D ℂ) (hx : (Xᴴ * X).PosDef) :
    ‖((fromCols X Y)ᴴ * fromCols X Y).det‖ ≤
      ‖(Xᴴ * X).det‖ * ∏ j, columnEnergy (Y.col j) := by
  classical
  let A := Xᴴ * X
  let B := Xᴴ * Y
  let G := Yᴴ * Y
  let T := G - Bᴴ * A⁻¹ * B
  let : Invertible A := hx.isUnit.invertible
  have hblock : (fromCols X Y)ᴴ * fromCols X Y = fromBlocks A B Bᴴ G := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]
    simp [A, B, G]
  have hT : T.PosSemidef := (PosDef.fromBlocks₁₁ B G hx).mp
    (hblock ▸ posSemidef_conjTranspose_mul_self _)
  have hdiff := hx.inv.posSemidef.conjTranspose_mul_mul_same B
  rw [hblock, det_fromBlocks₁₁, invOf_eq_nonsing_inv, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (hermitian_hadamard hT).trans
  apply Finset.prod_le_prod₀ (fun i _ => (Complex.nonneg_iff.mp (hT.diag_nonneg (i := i))).1)
  intro j _
  rw [← diag_gram]
  exact sub_le_self _ (Complex.nonneg_iff.mp (hdiff.diag_nonneg (i := j))).1

omit [DecidableEq J] in
/-- A bound tested on field-valued vectors controls the full complex image volume. -/
theorem image_gram_bound [IsTotallyComplex K] (A : Metric K I) (σ : K →+* ℂ)
    (X : Matrix J I ℂ) (P : ℝ)
    (h : ∀ x : I → K, columnEnergy (X *ᵥ (σ ∘ x)) ≤ Real.exp (2 * P) * A.energy σ x) :
    ‖(Xᴴ * X).det‖ ≤ A.gramDet σ * Real.exp (2 * Fintype.card I * P) := by
  classical
  let F := A.frame σ
  have hd : DenseRange (fun x : I → K => σ ∘ x) :=
    DenseRange.piMap fun _ => embedding_dense σ
  have hc (z : I → ℂ) : columnEnergy (X *ᵥ z) ≤ Real.exp (2 * P) * columnEnergy (F *ᵥ z) := by
    refine hd.induction_on (p := fun u => columnEnergy (X *ᵥ u) ≤ Real.exp (2 * P) *
      columnEnergy (F *ᵥ u)) z ?_ h
    apply isClosed_le <;> unfold columnEnergy Matrix.mulVec dotProduct <;> fun_prop
  let M := X * F⁻¹
  have hu : IsUnit F.det := isUnit_iff_ne_zero.mpr (A.nonsingular σ)
  have hcol (i : I) : columnEnergy (M.col i) ≤ Real.exp (2 * P) := by
    have hi := hc (F⁻¹ *ᵥ Pi.single i 1)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, F.mul_nonsing_inv hu, one_mulVec,
      mulVec_single_one] at hi
    simpa [columnEnergy, Pi.single_apply, apply_ite, M] using hi
  have hM : ‖(Mᴴ * M).det‖ ≤ Real.exp (2 * Fintype.card I * P) := by
    apply (hermitian_hadamard (posSemidef_conjTranspose_mul_self M)).trans
    simp_rw [diag_gram]
    calc
      _ ≤ ∏ _ : I, Real.exp (2 * P) := Finset.prod_le_prod₀
        (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (fun i _ => hcol i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]; ring_nf
  have hX : X = M * F := (F.nonsing_inv_mul_cancel_right X hu).symm
  calc
    ‖(Xᴴ * X).det‖ = ‖F.det‖ ^ 2 * ‖(Mᴴ * M).det‖ := by
      rw [hX, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ M,
        det_mul, det_mul, det_conjTranspose, norm_mul, norm_mul, norm_star]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hM (sq_nonneg _)

/-- Coordinate form of the matrix of an integral linear map. -/
abbrev overField (F : Matrix J I (𝓞 K)) : Matrix J I K := F.map (algebraMap (𝓞 K) K)

def Metric.imageFrame (B : Metric K J) (F : Matrix J I (𝓞 K)) (σ : K →+* ℂ) : Matrix J I ℂ :=
  B.frame σ * F.map (integralEmbedding σ)

def IntegralVector (x : J → K) : Prop := ∀ j, ∃ a : 𝓞 K, x j = (a : K)

omit [DecidableEq J] in
private theorem gram_cols (M : Matrix J J ℂ) {L : Type*} (p : L → J) :
    (M.submatrix id p)ᴴ * M.submatrix id p = (Mᴴ * M).submatrix p p := by
  ext i j
  rfl

/-- A single integral completion works at every embedding. The determinant of the
image Gram matrix retains the whole singular spectrum of the map. -/
theorem completed_image_bound {r d : ℕ} (B : Metric K J) (F : Matrix J (Fin r) (𝓞 K))
    (hinj : Function.Injective (overField F).mulVec) (hdim : Fintype.card J = r + d)
    (S : Set (J → K)) (hS : Submodule.span K S = ⊤) (hi : ∀ x ∈ S, IntegralVector x)
    (Λ : ℝ) (hs : ∀ x ∈ S, ∀ σ, B.energy σ x ≤ Real.exp (2 * Λ)) :
    ∃ (w : Fin d → J → K) (C : Matrix J J (𝓞 K)) (e : Fin r ⊕ Fin d ≃ J),
      (∀ j, w j ∈ S) ∧
      (∀ j, (overField C).col (e (Sum.inl j)) = (overField F).col j) ∧
      (∀ j, (overField C).col (e (Sum.inr j)) = w j) ∧ C.det ≠ 0 ∧
      ∀ σ, ‖σ (C.det : K)‖ ^ 2 * B.gramDet σ ≤
        ‖((B.imageFrame F σ)ᴴ * B.imageFrame F σ).det‖ * Real.exp (2 * d * Λ) := by
  classical
  let e : Fin r ⊕ Fin d ≃ J := Fintype.equivOfCardEq (by simp [hdim])
  let b := (Pi.basisFun K J).reindex e.symm
  have hb (x : J → K) (j) : b.repr x j = x (e j) := by simp [b]
  have hvi (x) (hx : x ∈ Set.range (overField F).col ∪ S) (j) :
      ∃ z : 𝓞 K, b.repr x j = (z : K) := by
    rw [hb]
    rcases hx with ⟨i, rfl⟩ | hx
    · exact ⟨F (e j) i, rfl⟩
    · exact hi x hx (e j)
  obtain ⟨w, D, hw, hcoord, hD⟩ := integral_completion b _ (mulVec_injective_iff.mp hinj) S hS hvi
  let C := D.submatrix e.symm e.symm
  have hc : C.det ≠ 0 := by simpa [C] using hD
  have hcols (i) : (overField C).col (e i) = Sum.elim (overField F).col w i := by
    ext j
    have h := congrFun (congrFun hcoord (e.symm j)) i
    simpa [Basis.toMatrix_apply, hb, C, overField, Matrix.col] using h.symm
  refine ⟨w, C, e, hw, fun j => hcols (.inl j), fun j => hcols (.inr j), hc, fun σ => ?_⟩
  let M := B.imageFrame C σ
  let X := B.imageFrame F σ
  let Y := M.submatrix id (e ∘ Sum.inr)
  have hframe (j : J) : M.col j = B.frame σ *ᵥ (σ ∘ (overField C).col j) := rfl
  have hleft (j) : M.col (e (.inl j)) = X.col j := by rw [hframe, hcols]; rfl
  have hfull : fromCols X Y = M.submatrix id e := by
    ext i j
    cases j with
    | inl j => exact (congrFun (hleft j) i).symm
    | inr j => rfl
  have hdet : M.det ≠ 0 := by
    rw [show M = B.frame σ * C.map (integralEmbedding σ) from rfl, det_mul, det_map_hom]
    exact mul_ne_zero (B.nonsingular σ) ((map_ne_zero σ).mpr ((Subalgebra.coe_eq_zero _).not.mpr hc))
  have hlin : LinearIndependent ℂ X.col := by
    have h := (linearIndependent_cols_of_det_ne_zero hdet).comp (e ∘ Sum.inl)
      (e.injective.comp Sum.inl_injective)
    exact (show M.col ∘ (e ∘ Sum.inl) = X.col from funext hleft) ▸ h
  have hsplit := split_gram_bound X Y (PosDef.conjTranspose_mul_self X (mulVec_injective_iff.mpr hlin))
  rw [hfull, gram_cols, det_submatrix_equiv_self, det_mul, det_conjTranspose, norm_mul,
    norm_star, ← sq] at hsplit
  rw [show ‖M.det‖ ^ 2 = _ from gram_transport B C σ] at hsplit
  apply hsplit.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∏ _ : Fin d, Real.exp (2 * Λ) := by
      apply Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      intro j _
      change columnEnergy (M.col (e (.inr j))) ≤ _
      rw [hframe, hcols]
      exact hs (w j) (hw j) σ
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
                  ← Real.exp_nat_mul]; ring_nf

/-- Global spectral descent before the collective norm is used. -/
theorem spectral_descent {r d : ℕ} (B : Metric K J) (F : Matrix J (Fin r) (𝓞 K))
    (hinj : Function.Injective (overField F).mulVec) (hdim : Fintype.card J = r + d)
    (S : Set (J → K)) (hS : Submodule.span K S = ⊤) (hi : ∀ x ∈ S, IntegralVector x)
    (Λ : ℝ) (hs : ∀ x ∈ S, ∀ σ, B.energy σ x ≤ Real.exp (2 * Λ)) :
    ∏ σ, B.gramDet σ ≤ (∏ σ, ‖((B.imageFrame F σ)ᴴ * B.imageFrame F σ).det‖) *
      Real.exp (Fintype.card (K →+* ℂ) * (2 * d * Λ)) := by
  obtain ⟨_, C, _, _, _, _, hc, h⟩ := completed_image_bound B F hinj hdim S hS hi Λ hs
  have hp := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun σ _ => mul_nonneg (sq_nonneg _) (sq_nonneg ‖(B.frame σ).det‖)) (fun σ _ => h σ)
  rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ← Real.exp_nat_mul] at hp
  refine le_trans (le_mul_of_one_le_left (Finset.prod_nonneg fun σ _ => sq_nonneg _) ?_) hp
  exact one_le_pow₀ (det_credit C hc)

private theorem image_bound_overField [IsTotallyComplex K] (A : Metric K I) (B : Metric K J)
    (F : Matrix J I (𝓞 K)) (σ : K →+* ℂ) (P : ℝ)
    (hf : ∀ x, B.energy σ (overField F *ᵥ x) ≤ Real.exp (2 * P) * A.energy σ x) :
    ‖((B.imageFrame F σ)ᴴ * B.imageFrame F σ).det‖ ≤ A.gramDet σ * Real.exp (2 * Fintype.card I * P) := by
  apply image_gram_bound A σ (B.imageFrame F σ) P
  intro x
  have heq : F.map (integralEmbedding σ) *ᵥ (σ ∘ x) = σ ∘ ((overField F) *ᵥ x) :=
    (funext (σ.map_mulVec (overField F) x)).symm
  unfold Metric.imageFrame
  rw [← Matrix.mulVec_mulVec, heq]
  exact hf x

theorem weighted_descent [IsTotallyComplex K] {r d : ℕ} (hr : 0 < r)
    (A : Metric K (Fin r)) (B : Metric K J) (F : Matrix J (Fin r) (𝓞 K))
    (hinj : Function.Injective (overField F).mulVec) (hdim : Fintype.card J = r + d)
    (S : Set (J → K)) (hS : Submodule.span K S = ⊤) (hi : ∀ x ∈ S, IntegralVector x)
    (P Λ : ℝ) (hf : ∀ σ x, B.energy σ (overField F *ᵥ x) ≤ Real.exp (2 * P) * A.energy σ x)
    (hs : ∀ x ∈ S, ∀ σ, B.energy σ x ≤ Real.exp (2 * Λ)) :
    r * (A.slopeSq - 2 * P) - 2 * d * Λ ≤ Fintype.card J * B.slopeSq := by
  classical
  obtain ⟨_, C, _, _, _, _, hc, hlocal⟩ := completed_image_bound B F hinj hdim S hS hi Λ hs
  have hlog (σ : K →+* ℂ) :
      2 * Real.log ‖σ (C.det : K)‖ + Real.log (B.gramDet σ) ≤
        Real.log (A.gramDet σ) + (2 * r * P + 2 * d * Λ) := by
    have h := image_bound_overField A B F σ P (hf σ)
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

def Metric.power (B : Metric K J) (q : ℕ) : Metric K (J × Fin q) where
  frame σ := blockDiagonal fun _ => B.frame σ
  nonsingular σ := by simp [det_blockDiagonal, B.nonsingular σ]

private theorem power_energy (B : Metric K J) (q : ℕ) (σ : K →+* ℂ) (x : J × Fin q → K) :
    (B.power q).energy σ x = ∑ h, B.energy σ (fun j => x (j, h)) := by
  unfold Metric.energy Metric.power
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul]

private theorem power_slope (B : Metric K J) {q : ℕ} (hq : 0 < q) :
    (B.power q).slopeSq = B.slopeSq := by
  simp only [Metric.slopeSq, Metric.gramDet, Metric.power, det_blockDiagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_pow, Fintype.card_prod, Nat.cast_mul]
  simp_rw [pow_right_comm _ q 2, Real.log_pow, ← Finset.mul_sum]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp [hq']

private def slot {q : ℕ} (h : Fin q) : (J → K) →ₗ[K] (J × Fin q → K) :=
  LinearMap.pi fun p => if p.2 = h then LinearMap.proj p.1 else 0

omit [NumberField K] [Fintype J] [DecidableEq J] in
private theorem slot_apply {q : ℕ} (h : Fin q) (y : J → K) (p : J × Fin q) :
    slot h y p = if p.2 = h then y p.1 else 0 := by
  by_cases he : p.2 = h <;> simp [slot, he]

/-- Descent for a jointly injective family in integral bases. Each matrix represents
an integral linear map. Generator and map bounds are squared norms. -/
theorem descent [IsTotallyComplex K] {r q : ℕ} (hr : 0 < r)
    (A : Metric K (Fin r)) (B : Metric K J) (φ : Fin q → Matrix J (Fin r) (𝓞 K))
    (hinj : ∀ x, (∀ h, (overField (φ h)) *ᵥ x = 0) → x = 0)
    (S : Set (J → K)) (hS : Submodule.span K S = ⊤) (hi : ∀ x ∈ S, IntegralVector x)
    (P Λ ε t : ℝ) (hf : ∀ σ x, ∑ h, B.energy σ (overField (φ h) *ᵥ x) ≤
      Real.exp (2 * P) * A.energy σ x)
    (hs : ∀ x ∈ S, ∀ σ, B.energy σ x ≤ Real.exp (2 * Λ))
    (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε)
    (hrank : (q : ℝ) * Fintype.card J ≤ (1 + ε) * r)
    (ht : t ≤ A.slopeSq - 2 * P) :
    t - ε * (|t| + 2 * Λ) ≤ B.slopeSq := by
  classical
  let F : Matrix (J × Fin q) (Fin r) (𝓞 K) := fun p i => φ p.2 p.1 i
  have hj : Function.Injective (overField F).mulVec := by
    change Function.Injective (overField F).mulVecLin
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact hinj x fun h => funext fun j => congrFun hx (j, h)
  have hle := (mulVec_injective_iff.mp hj).fintype_card_le_finrank
  simp only [Fintype.card_fin, finrank_fintype_fun_eq_card, Fintype.card_prod] at hle
  let d := Fintype.card J * q - r
  have hd : Fintype.card (J × Fin q) = r + d := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    dsimp [d]
    omega
  have hq : 0 < q := by
    by_contra! he
    simp [Nat.eq_zero_of_le_zero he] at hle
    omega
  let T := ⋃ h : Fin q, (slot h) '' S
  have hT : Submodule.span K T = ⊤ := by
    apply top_unique
    intro x _
    have hadd : x = ∑ h : Fin q, slot h (fun j => x (j, h)) := by
      ext p
      simp [Finset.sum_apply, slot_apply]
    rw [hadd]
    apply Submodule.sum_mem
    intro h _
    have hy : (fun j => x (j, h)) ∈ Submodule.span K S := by rw [hS]; trivial
    have hh := Submodule.mem_map_of_mem (f := slot h) hy
    rw [Submodule.map_span] at hh
    exact Submodule.span_mono (Set.subset_iUnion _ h) hh
  have hiT (x) (hx : x ∈ T) : IntegralVector x := by
    obtain ⟨h, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    intro p
    rw [slot_apply]
    split
    · exact hi y hy _
    · exact ⟨0, rfl⟩
  have hsT (x) (hx : x ∈ T) (σ) : (B.power q).energy σ x ≤ Real.exp (2 * Λ) := by
    obtain ⟨h, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    rw [power_energy]
    have hslot (k) : (fun j => slot h y (j, k)) = if k = h then y else 0 := by
      split <;> rename_i hk <;> ext j <;> simp [slot_apply, hk]
    simp_rw [hslot]
    have hzero : B.energy σ 0 = 0 := by simp [Metric.energy, Matrix.mulVec, dotProduct]
    simpa [apply_ite, hzero] using hs y hy σ
  have hfT (σ) (x) : (B.power q).energy σ (overField F *ᵥ x) ≤
      Real.exp (2 * P) * A.energy σ x := by
    rw [power_energy]
    exact hf σ x
  have hw := weighted_descent hr A (B.power q) F hj hd T hT hiT P Λ hfT hsT
  rw [power_slope B hq] at hw
  let N : ℝ := Fintype.card (J × Fin q)
  have hN : N = (r : ℝ) + d := by dsimp [N]; exact_mod_cast hd
  have hNrk : N ≤ (1 + ε) * r := by simpa [N, mul_comm] using hrank
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hNpos : 0 < N := by linarith
  have hdef : (d : ℝ) ≤ ε * N := by nlinarith [mul_nonneg hε hd']
  have hpen := mul_le_mul_of_nonneg_right hdef (show 0 ≤ |t| + 2 * Λ by positivity)
  change _ ≤ N * B.slopeSq at hw
  apply le_of_mul_le_mul_left (a := N) _ hNpos
  nlinarith [mul_le_mul_of_nonneg_left ht hr'.le, mul_le_mul_of_nonneg_left (le_abs_self t) hd',
    congrArg (· * t) hN]

def Metric.normAt (A : Metric K I) (σ : K →+* ℂ) (x : I → K) : ℝ := Real.sqrt (A.energy σ x)

@[simp] theorem normAt_sq (A : Metric K I) (σ : K →+* ℂ) (x : I → K) :
    A.normAt σ x ^ 2 = A.energy σ x :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- In an arbitrary pair of integral bases, it suffices to check integrality on
the source basis. The norm inequality is tested on vectors over the number field. -/
theorem descent_of_linear_maps [IsTotallyComplex K] {U V : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {r q : ℕ} (hr : 0 < r) (a : Basis (Fin r) K U)
    (b : Basis J K V) (A : Metric K (Fin r)) (B : Metric K J) (φ : Fin q → U →ₗ[K] V)
    (hint : ∀ h i, IntegralVector (b.equivFun (φ h (a i))))
    (hinj : ∀ x, (∀ h, φ h x = 0) → x = 0)
    (S : Set V) (hS : Submodule.span K S = ⊤) (hi : ∀ y ∈ S, IntegralVector (b.equivFun y))
    (P Λ ε t : ℝ) (hf : ∀ σ x, ∑ h, (B.normAt σ (b.equivFun (φ h x))) ^ 2 ≤
      Real.exp (2 * P) * (A.normAt σ (a.equivFun x)) ^ 2)
    (hs : ∀ y ∈ S, ∀ σ, B.normAt σ (b.equivFun y) ≤ Real.exp Λ)
    (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε)
    (hrank : (q : ℝ) * Fintype.card J ≤ (1 + ε) * r)
    (ht : t ≤ A.slopeSq - 2 * P) :
    t - ε * (|t| + 2 * Λ) ≤ B.slopeSq := by
  classical
  let F (h : Fin q) : Matrix J (Fin r) (𝓞 K) := fun j i => (hint h i j).choose
  have hmat (h) : overField (F h) = LinearMap.toMatrix a b (φ h) := by
    ext j i
    rw [LinearMap.toMatrix_apply]
    change ((hint h i j).choose : K) = _
    simpa only [Basis.equivFun_apply] using (hint h i j).choose_spec.symm
  have hmap (h) (x : Fin r → K) : overField (F h) *ᵥ x = b.equivFun (φ h (a.equivFun.symm x)) := by
    rw [hmat]
    simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using
      (φ h).toMatrix_mulVec_repr a b (a.equivFun.symm x)
  apply descent hr A B F _ (b.equivFun '' S) _ _ P Λ ε t _ _ hΛ hε hrank ht
  · intro x hx
    apply a.equivFun.symm.injective
    rw [map_zero]
    apply hinj
    intro h
    apply b.equivFun.injective
    rw [map_zero, ← hmap, hx]
  · change Submodule.span K (b.equivFun.toLinearMap '' S) = ⊤
    rw [← Submodule.map_span, hS, Submodule.map_top, LinearMap.range_eq_top.mpr b.equivFun.surjective]
  · rintro _ ⟨y, hy, rfl⟩
    exact hi y hy
  · intro σ x
    simp only [hmap]
    simpa only [normAt_sq, LinearEquiv.apply_symm_apply] using hf σ (a.equivFun.symm x)
  · rintro _ ⟨y, hy, rfl⟩ σ
    rw [← normAt_sq, show 2 * Λ = Λ + Λ by ring, Real.exp_add, ← sq]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hs y hy σ) 2

/-- An integral isogeny to a power of a Hermitian lattice loses at most twice
its log dilation in squared slope. Equal ranks remove the generator hypothesis. -/
theorem isogeny_to_power [IsTotallyComplex K] {r q : ℕ} (hr : 0 < r)
    (A : Metric K (Fin r)) (B : Metric K J) (φ : Fin q → Matrix J (Fin r) (𝓞 K))
    (hinj : ∀ x, (∀ h, overField (φ h) *ᵥ x = 0) → x = 0)
    (hrank : q * Fintype.card J = r) (P : ℝ)
    (hf : ∀ σ x, ∑ h, B.energy σ (overField (φ h) *ᵥ x) ≤ Real.exp (2 * P) * A.energy σ x) :
    A.slopeSq - 2 * P ≤ B.slopeSq := by
  classical
  let b := Pi.basisFun K J
  obtain ⟨c, hc⟩ := (Set.finite_range (fun p : J × (K →+* ℂ) => B.energy p.2 (b p.1))).bddAbove
  let Λ := max 0 c
  have hs (x) (hx : x ∈ Set.range b) (σ) : B.energy σ x ≤ Real.exp (2 * Λ) := by
    obtain ⟨i, rfl⟩ := hx
    have hle : B.energy σ (b i) ≤ c := hc ⟨(i, σ), rfl⟩
    have h₁ : c ≤ Λ := le_max_right _ _
    have h₂ : 0 ≤ Λ := le_max_left _ _
    linarith [Real.add_one_le_exp (2 * Λ)]
  have hi (x) (hx : x ∈ Set.range b) : IntegralVector x := by
    obtain ⟨i, rfl⟩ := hx
    intro j
    exact ⟨if j = i then 1 else 0, by by_cases h : j = i <;> simp [b, h]⟩
  have h := descent hr A B φ hinj (Set.range b) b.span_eq hi P Λ 0 (A.slopeSq - 2 * P) hf hs
    (le_max_left _ _) le_rfl (by simp; exact_mod_cast hrank.le) le_rfl
  simpa using h

/-- For an integral isogeny the squared index multiplies the target covolume.
Equal ranks eliminate the generator and rank-defect costs. -/
theorem isogeny_covolume_bound [IsTotallyComplex K] (A B : Metric K I)
    (F : Matrix I I (𝓞 K)) (hdet : F.det ≠ 0) (P : ℝ)
    (hf : ∀ σ x, B.energy σ (overField F *ᵥ x) ≤ Real.exp (2 * P) * A.energy σ x) :
    1 ≤ |(Algebra.norm ℤ F.det : ℝ)| ∧
      |(Algebra.norm ℤ F.det : ℝ)| ^ 2 * ∏ σ, B.gramDet σ ≤
        (∏ σ, A.gramDet σ) * Real.exp (Fintype.card (K →+* ℂ) * (2 * Fintype.card I * P)) := by
  refine ⟨prod_embedding_norm F.det ▸ det_credit F hdet, ?_⟩
  rw [← prod_gram_transport]
  have h (σ) := image_bound_overField A B F σ P (hf σ)
  simp only [det_mul, det_conjTranspose, norm_mul, norm_star, ← sq] at h
  have hp := Finset.prod_le_prod₀ (s := Finset.univ) (fun σ _ => sq_nonneg ‖(B.imageFrame F σ).det‖)
    (fun σ _ => h σ)
  simpa only [Metric.imageFrame, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← Real.exp_nat_mul] using hp

/-- In particular, an integral endomorphism with nonsingular matrix has index
at most the collective dilation raised to the underlying integer rank. -/
theorem endomorphism_norm_bound [IsTotallyComplex K] (A : Metric K I) (F : Matrix I I (𝓞 K))
    (hdet : F.det ≠ 0) (P : ℝ)
    (hf : ∀ σ x, A.energy σ (overField F *ᵥ x) ≤ Real.exp (2 * P) * A.energy σ x) :
    1 ≤ |(Algebra.norm ℤ F.det : ℝ)| ∧
      |(Algebra.norm ℤ F.det : ℝ)| ≤
        Real.exp (Fintype.card (K →+* ℂ) * (Fintype.card I : ℝ) * P) := by
  obtain ⟨hc, h⟩ := isogeny_covolume_bound A A F hdet P hf
  have hp : 0 < ∏ σ, A.gramDet σ := Finset.prod_pos fun σ _ =>
    sq_pos_of_pos (norm_pos_iff.mpr (A.nonsingular σ))
  rw [mul_comm _ (∏ σ, A.gramDet σ)] at h
  refine ⟨hc, (sq_le_sq₀ (abs_nonneg _) (Real.exp_pos _).le).mp ?_⟩
  rw [← Real.exp_nat_mul]
  convert! le_of_mul_le_mul_left h hp using 2
  push_cast
  ring

open Classical in
/-- Alpöge uses `X⁻¹` on the coordinates at the chosen representative of a place.
At the other embedding the coordinate frame is its complex conjugate. -/
def Metric.ofPlaces (X : InfinitePlace K → Matrix I I ℂ) (hX : ∀ v, (X v).det ≠ 0) : Metric K I where
  frame σ := if σ = (InfinitePlace.mk σ).embedding then (X (InfinitePlace.mk σ))⁻¹
    else ((X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)
  nonsingular σ := by
    split
    · simpa [det_nonsing_inv] using hX (InfinitePlace.mk σ)
    · rw [det_map_hom, map_ne_zero, det_nonsing_inv]
      simpa using hX (InfinitePlace.mk σ)

theorem normAt_place (X : InfinitePlace K → Matrix I I ℂ) (hX : ∀ v, (X v).det ≠ 0)
    (v : InfinitePlace K) (x : I → K) :
    (Metric.ofPlaces X hX).normAt v.embedding x =
      Real.sqrt (columnEnergy ((X v)⁻¹ *ᵥ (v.embedding ∘ x))) := by
  simp [Metric.normAt, Metric.energy, Metric.ofPlaces, InfinitePlace.mk_embedding, columnEnergy]

private theorem sum_over_places [IsTotallyComplex K] (f : InfinitePlace K → ℝ) :
    ∑ σ : K →+* ℂ, f (InfinitePlace.mk σ) = 2 * ∑ v, f v := by
  classical
  rw [← Finset.univ.sum_fiberwise InfinitePlace.mk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hc := InfinitePlace.card_filter_mk_eq v
  rw [(IsTotallyComplex.isComplex v).mult_eq_two] at hc
  calc
    _ = ∑ _ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = v), f v :=
      Finset.sum_congr rfl fun σ hσ => congrArg f (Finset.mem_filter.mp hσ).2
    _ = _ := by simp [hc, two_mul]

/-- At a totally complex field the embedding average is exactly the place average.
The factor two in `log ‖det X‖²` survives passage to places. -/
theorem slopeSq_ofPlaces [IsTotallyComplex K]
    (X : InfinitePlace K → Matrix I I ℂ) (hX : ∀ v, (X v).det ≠ 0) :
    (Metric.ofPlaces X hX).slopeSq =
      (∑ v, 2 * Real.log ‖(X v).det‖) / (Fintype.card (InfinitePlace K) * (Fintype.card I : ℝ)) := by
  have hcard := sum_over_places (K := K) (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcard
  have hl (σ : K →+* ℂ) : Real.log ((Metric.ofPlaces X hX).gramDet σ) =
      -(2 * Real.log ‖(X (InfinitePlace.mk σ)).det‖) := by
    simp only [Metric.gramDet, Metric.ofPlaces]
    split <;> simp [det_map_hom, det_nonsing_inv, Real.log_pow]
  unfold Metric.slopeSq
  simp_rw [hl]
  rw [sum_over_places (fun v => -(2 * Real.log ‖(X v).det‖)), Finset.sum_neg_distrib, hcard]
  ring

end RHLean.Geometry.NumberFieldDescent
