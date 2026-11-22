import Mathlib

/-!
# Finite integral frames and quantitative volume descent

This file proves geometric inequalities from actual finite vector families and
integer coordinate matrices. No field asserts an arithmetic cancellation or
slope estimate. The determinant of the integral matrix is retained explicitly.

The application to Alpoge's theta-lift section lattices still requires their
actual integral maps, norm bounds and completion vectors. Coordinate changes
and a centered restriction of the signed source do not supply those data.
-/

noncomputable section

open scoped BigOperators
open Module

namespace RHLean.Geometry

section Frame

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype I] [Fintype J]

/-- A genuine linear combination of a finite family, with every coefficient
retained. Columns, rather than rows, are the resulting vectors. -/
def nativeFrameCombination (v : I → E) (C : Matrix I J ℝ) (j : J) : E :=
  ∑ i : I, C i j • v i

/-- Exact Gram transport, before any norm or determinant inequality. -/
theorem nativeFrameCombination_gram (v : I → E) (C : Matrix I J ℝ) :
    Matrix.gram ℝ (nativeFrameCombination v C) =
      C.transpose * Matrix.gram ℝ v * C := by
  ext i j
  simp only [Matrix.gram_apply, nativeFrameCombination,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  ring

/-- Finite volume transport includes the square of the full coordinate
determinant. There is no discarded lattice-index factor. -/
theorem nativeFrameCombination_gram_det [DecidableEq I]
    (v : I → E) (C : Matrix I I ℝ) :
    (Matrix.gram ℝ (nativeFrameCombination v C)).det =
      C.det ^ 2 * (Matrix.gram ℝ v).det := by
  rw [nativeFrameCombination_gram, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  ring

end Frame

section Hadamard

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Hadamard's inequality, proved by the actual Gram--Schmidt orthonormal
frame. This has no factorial, dimension-power or coefficient-norm loss. -/
theorem nativeGramDet_le_prod_norm_sq {n : ℕ}
    (hdim : finrank ℝ E = Fintype.card (Fin n)) (v : Fin n → E) :
    (Matrix.gram ℝ v).det ≤ ∏ i : Fin n, ‖v i‖ ^ 2 := by
  let u := InnerProductSpace.gramSchmidtOrthonormalBasis hdim v
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => u.repr (v j) i
  have hG : Matrix.gram ℝ v = M.conjTranspose * M :=
    Matrix.gram_eq_conjTranspose_mul u v
  have hM : M = u.toBasis.toMatrix v := by
    ext i j
    exact (u.coe_toBasis_repr_apply (v j) i).symm
  rw [hM] at hG
  have hdet : (Matrix.gram ℝ v).det = (u.toBasis.det v) ^ 2 := by
    rw [hG, Matrix.det_mul, Matrix.det_conjTranspose, star_trivial,
      Basis.det_apply]
    ring
  have hdiag : u.toBasis.det v = ∏ i : Fin n, inner ℝ (u i) (v i) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hdim v
  have hentry (i : Fin n) : |inner ℝ (u i) (v i)| ≤ ‖v i‖ := by
    simpa only [Real.norm_eq_abs, u.norm_eq_one, one_mul] using
      (norm_inner_le_norm (𝕜 := ℝ) (u i) (v i))
  have hprod : |∏ i : Fin n, inner ℝ (u i) (v i)| ≤
      ∏ i : Fin n, ‖v i‖ := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      (fun i _ => hentry i)
  have hp0 : 0 ≤ ∏ i : Fin n, ‖v i‖ :=
    Finset.prod_nonneg fun i _ => norm_nonneg _
  rw [hdet, hdiag, Finset.prod_pow]
  nlinarith [sq_abs (∏ i : Fin n, inner ℝ (u i) (v i)),
    abs_nonneg (∏ i : Fin n, inner ℝ (u i) (v i))]

end Hadamard

section CoordinateDescent

variable {U V I : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [Fintype I] [DecidableEq I]

/-- Reindexing the finite Hadamard inequality loses no constant. -/
theorem nativeGramDet_le_prod_norm_sq_fintype
    (hdim : finrank ℝ V = Fintype.card I) (v : I → V) :
    (Matrix.gram ℝ v).det ≤ ∏ i : I, ‖v i‖ ^ 2 := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have h := nativeGramDet_le_prod_norm_sq (by simpa using hdim) (v ∘ e)
  have hG : Matrix.gram ℝ (v ∘ e) = (Matrix.gram ℝ v).submatrix e e := rfl
  rw [hG, Matrix.det_submatrix_equiv_self] at h
  have hp : (∏ i : Fin (Fintype.card I), ‖v (e i)‖ ^ 2) =
      ∏ i : I, ‖v i‖ ^ 2 := e.prod_comp (fun i => ‖v i‖ ^ 2)
  simpa only [Function.comp_apply, hp] using h

/-- Coordinates in an arbitrary lattice basis preserve its actual Gram
determinant, rather than replacing that determinant by basis lengths. -/
omit [FiniteDimensional ℝ V] in
theorem nativeGramDet_basis_coordinates (b : Basis I ℝ V) (v : I → V) :
    (Matrix.gram ℝ v).det =
      (b.toMatrix v).det ^ 2 * (Matrix.gram ℝ (b : I → V)).det := by
  have hv : nativeFrameCombination b (b.toMatrix v) = v := by
    funext i
    simp [nativeFrameCombination]
  simpa only [hv] using nativeFrameCombination_gram_det (b : I → V) (b.toMatrix v)

/-- The source metric enters through its full Gram determinant. This
identity is valid before imposing any integrality or norm estimate. -/
omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] in
theorem nativeMap_gramDet_source (a : Basis I ℝ U)
    (u : OrthonormalBasis I ℝ U) (f : U →ₗ[ℝ] V) :
    (Matrix.gram ℝ (fun i => f (a i))).det =
      (Matrix.gram ℝ (a : I → U)).det *
        (Matrix.gram ℝ (fun i => f (u i))).det := by
  let M := u.toBasis.toMatrix (a : I → U)
  have hfa : nativeFrameCombination (fun i => f (u i)) M =
      (fun i => f (a i)) := by
    funext j
    change (∑ i : I, M i j • f (u i)) = f (a j)
    have hs : (∑ i : I, M i j • u i) = a j := by
      change (∑ i : I, u.toBasis.toMatrix (a : I → U) i j • u.toBasis i) = a j
      exact u.toBasis.sum_toMatrix_smul_self
    calc
      (∑ i : I, M i j • f (u i)) = f (∑ i : I, M i j • u i) := by
        simp only [map_sum, map_smul]
      _ = f (a j) := congrArg f hs
  have ha := nativeGramDet_basis_coordinates u.toBasis (a : I → U)
  have hu : Matrix.gram ℝ (u.toBasis : I → U) = 1 :=
    Matrix.gram_eq_one_iff_orthonormal.mpr u.orthonormal
  rw [hu, Matrix.det_one, mul_one] at ha
  have h := nativeFrameCombination_gram_det (fun i => f (u i)) M
  rw [hfa] at h
  change (Matrix.gram ℝ (fun i => f (a i))).det =
    (u.toBasis.toMatrix (a : I → U)).det ^ 2 *
      (Matrix.gram ℝ (fun i => f (u i))).det at h
  rwa [← ha] at h

/-- Quantitative integral-map theorem for arbitrary source and target
metrics. The source covolume, target covolume and the exact integer index
are all retained. Bounds are checked on an actual orthonormal frame.
-/
omit [FiniteDimensional ℝ U] in
theorem nativeIntegralMap_gram_bound
    (a : Basis I ℝ U) (b : Basis I ℝ V)
    (u : OrthonormalBasis I ℝ U) (f : U →ₗ[ℝ] V)
    (C : Matrix I I ℤ)
    (hC : b.toMatrix (fun i => f (a i)) = C.map (fun z : ℤ => (z : ℝ)))
    (H : I → ℝ) (hH : ∀ i, ‖f (u i)‖ ≤ H i) :
    (C.det : ℝ) ^ 2 * (Matrix.gram ℝ (b : I → V)).det ≤
      (Matrix.gram ℝ (a : I → U)).det * ∏ i : I, (H i) ^ 2 := by
  have ht := nativeGramDet_basis_coordinates b (fun i => f (a i))
  rw [hC, ← Int.cast_det] at ht
  have hs := nativeMap_gramDet_source a u f
  have hh := nativeGramDet_le_prod_norm_sq_fintype (Module.finrank_eq_card_basis b)
    (fun i => f (u i))
  have hp : (∏ i : I, ‖f (u i)‖ ^ 2) ≤ ∏ i : I, (H i) ^ 2 := by
    apply Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
    intro i _hi
    have h0 := norm_nonneg (f (u i))
    have h1 := hH i
    nlinarith
  have ha0 : 0 ≤ (Matrix.gram ℝ (a : I → U)).det :=
    (Matrix.posSemidef_gram ℝ (a : I → U)).det_nonneg
  calc
    (C.det : ℝ) ^ 2 * (Matrix.gram ℝ (b : I → V)).det =
        (Matrix.gram ℝ (fun i => f (a i))).det := ht.symm
    _ = (Matrix.gram ℝ (a : I → U)).det *
        (Matrix.gram ℝ (fun i => f (u i))).det := hs
    _ ≤ _ := mul_le_mul_of_nonneg_left (hh.trans hp) ha0

end CoordinateDescent

section Completion

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]

/-- The source is enlarged by a standard orthogonal integral lattice.
Its auxiliary factor has covolume one in its stated metric. -/
def nativeCompletionBasis {r d : ℕ} (a : Basis (Fin r) ℝ U) :
    Basis (Fin r ⊕ Fin d) ℝ (WithLp 2 (U × EuclideanSpace ℝ (Fin d))) :=
  (a.prod (EuclideanSpace.basisFun (Fin d) ℝ).toBasis).map
    (WithLp.linearEquiv 2 ℝ (U × EuclideanSpace ℝ (Fin d))).symm

/-- An explicitly constructed full map: the original map on the source
and the supplied completion vectors on the auxiliary standard basis. -/
def nativeCompletionMap {d : ℕ} (f : U →ₗ[ℝ] V) (w : Fin d → V) :
    WithLp 2 (U × EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] V :=
  (f.coprod ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.constr ℝ w)).comp
    (WithLp.linearEquiv 2 ℝ (U × EuclideanSpace ℝ (Fin d))).toLinearMap

theorem nativeCompletionMap_basis {r d : ℕ} (a : Basis (Fin r) ℝ U)
    (f : U →ₗ[ℝ] V) (w : Fin d → V) (i : Fin r ⊕ Fin d) :
    nativeCompletionMap f w (nativeCompletionBasis a i) =
      Sum.elim (fun j => f (a j)) w i := by
  cases i <;>
    simp [nativeCompletionMap, nativeCompletionBasis, Basis.prod_apply]

theorem nativeCompletionMap_orthonormal {r d : ℕ}
    (u : OrthonormalBasis (Fin r) ℝ U)
    (f : U →ₗ[ℝ] V) (w : Fin d → V) (i : Fin r ⊕ Fin d) :
    nativeCompletionMap f w (u.prod (EuclideanSpace.basisFun (Fin d) ℝ) i) =
      Sum.elim (fun j => f (u j)) w i := by
  cases i <;>
    simp [nativeCompletionMap, OrthonormalBasis.prod_apply]

/-- The auxiliary factor costs exactly zero logarithmic covolume.
This follows from its actual orthogonal unit Gram matrix. -/
theorem nativeCompletionBasis_gram_det {r d : ℕ}
    (a : Basis (Fin r) ℝ U) :
    (Matrix.gram ℝ (nativeCompletionBasis (d := d) a)).det =
      (Matrix.gram ℝ (a : Fin r → U)).det := by
  have hG : Matrix.gram ℝ (nativeCompletionBasis (d := d) a) =
      Matrix.fromBlocks (Matrix.gram ℝ (a : Fin r → U))
        (0 : Matrix (Fin r) (Fin d) ℝ) 0 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.gram_apply, nativeCompletionBasis, Basis.prod_apply,
        WithLp.prod_inner_apply, OrthonormalBasis.inner_eq_ite, Matrix.one_apply]
  rw [hG, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- Finite integral-map descent with genuinely constructed completion.

The source rank is `r`, the target rank is `r+d`. The full `r+d` square
integer matrix is made from the image of the original source basis and
the supplied `d` target completion vectors. Its determinant, the original
source metric, the joint map norm and all completion costs remain visible.

For a family of maps into `B`, apply this to their joint map into `B^q`.
Producing short completion vectors and a nonzero integral determinant for
the actual theta-lift source is a separate, concrete construction problem.
-/
theorem nativeIntegralDescent_with_completion {r d : ℕ}
    (a : Basis (Fin r) ℝ U) (b : Basis (Fin r ⊕ Fin d) ℝ V)
    (f : U →ₗ[ℝ] V) (w : Fin d → V)
    (C : Matrix (Fin r ⊕ Fin d) (Fin r ⊕ Fin d) ℤ)
    (hC : b.toMatrix (Sum.elim (fun i => f (a i)) w) =
      C.map (fun z : ℤ => (z : ℝ)))
    (P Λ : ℝ)
    (hf : ∀ x : U, ‖f x‖ ≤ Real.exp P * ‖x‖)
    (hw : ∀ j : Fin d, ‖w j‖ ≤ Real.exp Λ) :
    (C.det : ℝ) ^ 2 * (Matrix.gram ℝ (b : (Fin r ⊕ Fin d) → V)).det ≤
      (Matrix.gram ℝ (a : Fin r → U)).det *
        Real.exp (2 * (r : ℝ) * P + 2 * (d : ℝ) * Λ) := by
  let u := InnerProductSpace.gramSchmidtOrthonormalBasis
    (Module.finrank_eq_card_basis a) (a : Fin r → U)
  let H : (Fin r ⊕ Fin d) → ℝ :=
    Sum.elim (fun _ : Fin r => Real.exp P) (fun _ : Fin d => Real.exp Λ)
  have hcoords : b.toMatrix
      (fun i => nativeCompletionMap f w (nativeCompletionBasis a i)) =
      C.map (fun z : ℤ => (z : ℝ)) := by
    simpa only [nativeCompletionMap_basis] using hC
  have hnorm : ∀ i : Fin r ⊕ Fin d,
      ‖nativeCompletionMap f w (u.prod (EuclideanSpace.basisFun (Fin d) ℝ) i)‖ ≤
        H i := by
    intro i
    rw [nativeCompletionMap_orthonormal]
    cases i with
    | inl i => simpa [H] using hf (u i)
    | inr j => exact hw j
  have h := nativeIntegralMap_gram_bound (nativeCompletionBasis a) b
    (u.prod (EuclideanSpace.basisFun (Fin d) ℝ)) (nativeCompletionMap f w)
    C hcoords H hnorm
  rw [nativeCompletionBasis_gram_det] at h
  have hprod : (∏ i : Fin r ⊕ Fin d, (H i) ^ 2) =
      Real.exp (2 * (r : ℝ) * P + 2 * (d : ℝ) * Λ) := by
    simp only [Fintype.prod_sum_type, H, Sum.elim_inl, Sum.elim_inr,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rwa [hprod] at h

end Completion

section IntegralFrame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The frame is built from an integer matrix, in the original real metric.
In particular the target is the integral span of `b`, not a freely rescaled
ambient lattice. -/
def nativeIntegralFrame {n : ℕ} (b : Basis (Fin n) ℝ E)
    (C : Matrix (Fin n) (Fin n) ℤ) : Fin n → E :=
  nativeFrameCombination b (C.map fun z : ℤ => (z : ℝ))

/-- The actual integral frame's squared volume is bounded by its column
energies, with its integer determinant credit still present. -/
theorem nativeIntegralFrame_det_sq_mul_gram_le {n : ℕ}
    (b : Basis (Fin n) ℝ E) (C : Matrix (Fin n) (Fin n) ℤ) :
    (C.det : ℝ) ^ 2 * (Matrix.gram ℝ (b : Fin n → E)).det ≤
      ∏ j : Fin n, ‖nativeIntegralFrame b C j‖ ^ 2 := by
  have h := nativeGramDet_le_prod_norm_sq (Module.finrank_eq_card_basis b)
    (nativeIntegralFrame b C)
  rw [nativeIntegralFrame, nativeFrameCombination_gram_det] at h
  simpa only [← Int.cast_det, nativeIntegralFrame] using h

/-- A nonzero integral determinant is at least one in absolute value.
This is where integrality enters the geometric inequality. -/
theorem nativeIntegralFrame_gram_le {n : ℕ}
    (b : Basis (Fin n) ℝ E) (C : Matrix (Fin n) (Fin n) ℤ)
    (hC : C.det ≠ 0) :
    (Matrix.gram ℝ (b : Fin n → E)).det ≤
      ∏ j : Fin n, ‖nativeIntegralFrame b C j‖ ^ 2 := by
  have hc : (1 : ℝ) ≤ |(C.det : ℝ)| := by
    exact_mod_cast Int.one_le_abs hC
  have hc2 : (1 : ℝ) ≤ (C.det : ℝ) ^ 2 := by
    nlinarith [sq_abs (C.det : ℝ)]
  have hg : 0 ≤ (Matrix.gram ℝ (b : Fin n → E)).det :=
    (Matrix.posSemidef_gram ℝ (b : Fin n → E)).det_nonneg
  calc
    (Matrix.gram ℝ (b : Fin n → E)).det ≤
        (C.det : ℝ) ^ 2 * (Matrix.gram ℝ (b : Fin n → E)).det := by
      nlinarith
    _ ≤ _ := nativeIntegralFrame_det_sq_mul_gram_le b C

/-- An explicit rank split: `r` image columns cost `exp P`, while the `d`
completion columns cost `exp Λ`. No factor depending on `r+d` is lost.
The completion columns are the last actual columns of the integer matrix.
-/
theorem nativeIntegralFrame_split_bound {r d : ℕ}
    (b : Basis (Fin (r + d)) ℝ E)
    (C : Matrix (Fin (r + d)) (Fin (r + d)) ℤ) (P Λ : ℝ)
    (himage : ∀ i : Fin r,
      ‖nativeIntegralFrame b C (Fin.castAdd d i)‖ ≤ Real.exp P)
    (hcompletion : ∀ j : Fin d,
      ‖nativeIntegralFrame b C (Fin.natAdd r j)‖ ≤ Real.exp Λ) :
    (C.det : ℝ) ^ 2 * (Matrix.gram ℝ (b : Fin (r + d) → E)).det ≤
      Real.exp (2 * (r : ℝ) * P + 2 * (d : ℝ) * Λ) := by
  have hi : (∏ i : Fin r,
      ‖nativeIntegralFrame b C (Fin.castAdd d i)‖ ^ 2) ≤
      ∏ _i : Fin r, (Real.exp P) ^ 2 := by
    apply Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
    intro i _hi
    nlinarith [himage i, norm_nonneg (nativeIntegralFrame b C (Fin.castAdd d i)),
      Real.exp_pos P]
  have hc : (∏ j : Fin d,
      ‖nativeIntegralFrame b C (Fin.natAdd r j)‖ ^ 2) ≤
      ∏ _j : Fin d, (Real.exp Λ) ^ 2 := by
    apply Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
    intro j _hj
    nlinarith [hcompletion j, norm_nonneg (nativeIntegralFrame b C (Fin.natAdd r j)),
      Real.exp_pos Λ]
  calc
    (C.det : ℝ) ^ 2 * (Matrix.gram ℝ (b : Fin (r + d) → E)).det ≤
        ∏ j : Fin (r + d), ‖nativeIntegralFrame b C j‖ ^ 2 :=
      nativeIntegralFrame_det_sq_mul_gram_le b C
    _ = (∏ i : Fin r, ‖nativeIntegralFrame b C (Fin.castAdd d i)‖ ^ 2) *
        ∏ j : Fin d, ‖nativeIntegralFrame b C (Fin.natAdd r j)‖ ^ 2 :=
      Fin.prod_univ_add _
    _ ≤ (∏ _i : Fin r, (Real.exp P) ^ 2) *
        ∏ _j : Fin d, (Real.exp Λ) ^ 2 :=
      mul_le_mul hi hc (Finset.prod_nonneg fun _ _ => sq_nonneg _)
        (Finset.prod_nonneg fun _ _ => sq_nonneg _)
    _ = Real.exp (2 * (r : ℝ) * P + 2 * (d : ℝ) * Λ) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

end IntegralFrame

end RHLean.Geometry
