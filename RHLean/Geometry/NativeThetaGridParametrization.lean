import RHLean.Geometry.NativeThetaPairedPolynomials
import RHLean.Geometry.NativeThetaPerpendicular
import RHLean.Geometry.NativeThetaGridInterpolation

/-!
# Polynomial parametrization of the actual finite perpendicular grid

The source determinant-adjugate construction is polynomial in its integral
parameters. Its variable degree is bounded here, so interpolation proves that
the displayed finite grid spans the entire parameterized polynomial family.
This does not identify that family with all harmonic polynomials: the source
highest-weight generation theorem is a separate remaining dependency.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`SpanGridPerpVecEqOrbitSpanOfLe.lean`, Perp and Param sections, coordProd,
span_grid_coordProd, and the explicit CM-grid comparison; and
`ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/`
`PerpVecPerpSt.lean`, hMat/perpVec. The source archive/mirror states no
license; this notice preserves attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MvPolynomial Matrix NumberField

namespace RHLean.Geometry.NativeTheta.Paired

section PerpendicularDefinition

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

def hMat {p : ℕ} (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) : Matrix (Fin p) (Fin p) R :=
  Matrix.of fun a' a => h (e' a') (e a)

def perpVec {p : ℕ} (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) : V :=
  (hMat h e e').det • g - ∑ a, ∑ a', ((hMat h e e').adjugate a a' * h g (e a)) • e' a'

theorem perpVec_eq_perpVector {p : ℕ} (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) :
    perpVec h e e' g = Perpendicular.perpVector
      (fun a => (LinearMap.proj (e a)).comp h) e' g := rfl

theorem perpVec_apply_eq_zero {p : ℕ} (h : V →ₗ[R] (V → R))
    (e e' : Fin p → V) (g : V) (a : Fin p) : h (perpVec h e e' g) (e a) = 0 :=
  Perpendicular.apply_perpVector (fun a => (LinearMap.proj (e a)).comp h) e' g a

end PerpendicularDefinition

section Perp

variable {R S : Type} [CommRing R] [CommRing S] {p n : ℕ}

variable (R n) in

def dotPairing : (Fin n → R) →ₗ[R] ((Fin n → R) → R) where
  toFun x y := x ⬝ᵥ y
  map_add' x x' := funext fun y => add_dotProduct x x' y
  map_smul' r x := funext fun y => smul_dotProduct r x y

@[simp] theorem dotPairing_apply (x y : Fin n → R) : dotPairing R n x y = x ⬝ᵥ y := rfl

theorem map_perpVec_apply (f : R →+* S) (h : (Fin n → R) →ₗ[R] ((Fin n → R) → R))
    (h' : (Fin n → S) →ₗ[S] ((Fin n → S) → S)) (e e' : Fin p → Fin n → R) (g : Fin n → R)
    (ε ε' : Fin p → Fin n → S) (γ : Fin n → S) (he' : ∀ a k, f (e' a k) = ε' a k)
    (hg : ∀ k, f (g k) = γ k) (hM : ∀ a' a, f (h (e' a') (e a)) = h' (ε' a') (ε a))
    (hge : ∀ a, f (h g (e a)) = h' γ (ε a)) (k : Fin n) :
    f (perpVec h e e' g k) = perpVec h' ε ε' γ k := by
  have hm : f.mapMatrix (hMat h e e') = hMat h' ε ε' := by
    ext a' a; exact hM a' a
  have hadj (a a') : f ((hMat h e e').adjugate a a') = (hMat h' ε ε').adjugate a a' := by
    rw [← hm, ← RingHom.map_adjugate]; rfl
  simp only [perpVec, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_sub, map_mul,
    map_sum, RingHom.map_det, hm, hadj, hg, hge, he']

theorem map_perpVec_dotPairing (f : R →+* S) (ε ε' : Fin p → Fin n → R) (γ : Fin n → R) :
    f ∘ perpVec (dotPairing R n) ε ε' γ =
      perpVec (dotPairing S n) (fun a => f ∘ ε a) (fun a => f ∘ ε' a) (f ∘ γ) :=
  funext fun k => map_perpVec_apply f _ _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => by simp [dotProduct]) (fun _ => by simp [dotProduct]) k

theorem adjugate_isHomogeneous {σ : Type*} (M : Matrix (Fin p) (Fin p) (MvPolynomial σ R)) (d : ℕ)
    (hM : ∀ a b, (M a b).IsHomogeneous d) (a b : Fin p) :
    (M.adjugate a b).IsHomogeneous ((p - 1) * d) := by
  rw [adjugate_apply]
  have := det_isWeightedHomogeneous (1 : σ → ℕ) (M.updateRow b (Pi.single a 1))
    (fun i => if i = b then 0 else d) (fun i j => by
      by_cases hi : i = b
      · subst hi
        rw [updateRow_self, ite_eq_left rfl, Pi.single_apply]
        split_ifs
        · exact isWeightedHomogeneous_one _ _
        · exact isWeightedHomogeneous_zero _ _ _
      · rw [updateRow_ne hi, ite_eq_right hi]; exact hM i j)
  change IsWeightedHomogeneous 1 _ _
  convert this using 1
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem perpVec_dotPairing_isHomogeneous {σ : Type} (ε ε' : Fin p → Fin n → MvPolynomial σ R)
    (γ : Fin n → MvPolynomial σ R) (hε : ∀ a k, (ε a k).IsHomogeneous 1)
    (hε' : ∀ a k, (ε' a k).IsHomogeneous 1) (hγ : ∀ k, (γ k).IsHomogeneous 1) (k : Fin n) :
    (perpVec (dotPairing _ n) ε ε' γ k).IsHomogeneous (2 * p + 1) := by
  have hM (a' a) : (hMat (dotPairing _ n) ε ε' a' a).IsHomogeneous 2 :=
    show (∑ k, ε' a' k * ε a k).IsHomogeneous 2 from
      IsHomogeneous.sum _ _ _ fun k _ => (hε' a' k).mul (hε a k)
  have hge (a) : (dotPairing _ n γ (ε a)).IsHomogeneous 2 :=
    IsHomogeneous.sum _ _ _ fun k _ => (hγ k).mul (hε a k)
  have hdet : (hMat (dotPairing _ n) ε ε').det.IsHomogeneous (2 * p) := by
    have := det_isWeightedHomogeneous (1 : σ → ℕ) _ (fun _ => 2) hM
    simpa [mul_comm, IsHomogeneous] using this
  simp only [perpVec, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  refine (hdet.mul (hγ k)).sub (IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _
    fun a' _ => ?_)
  have := ((adjugate_isHomogeneous _ 2 hM a a').mul (hge a)).mul (hε' a' k)
  have hp := a.pos
  rwa [show (p - 1) * 2 + 2 + 1 = 2 * p + 1 by omega] at this

end Perp

section Param

variable {K : Type*} [CommRing K] {σ ω T κ : Type*} {p q : ℕ}

noncomputable def swapVars : MvPolynomial ω (MvPolynomial σ K) →+* MvPolynomial σ (MvPolynomial ω K) :=
  eval₂Hom (MvPolynomial.map C) fun v => C (X v)

theorem eval_swapVars (x : σ → K) (F : MvPolynomial ω (MvPolynomial σ K)) :
    eval (fun i => C (x i)) (swapVars F) = MvPolynomial.map (eval x) F := by
  have : (eval fun i => (C (x i) : MvPolynomial ω K)).comp swapVars = MvPolynomial.map (eval x) := by
    ext1
    · ext1
      · ext1 r; simp [swapVars]
      · simp [swapVars]
    · simp [swapVars]
  exact DFunLike.congr_fun this F

variable [Fintype κ]

theorem swapVars_rowForm_isHomogeneous (t : T) (r : Fin p ⊕ Fin q) (u : κ → MvPolynomial σ K)
    {d : ℕ} (hu : ∀ k, (u k).IsHomogeneous d) : (swapVars (rowForm t r u)).IsHomogeneous d := by
  rw [rowForm_apply, map_sum]
  refine IsHomogeneous.sum _ _ _ fun k _ => ?_
  simp only [swapVars, map_mul, eval₂Hom_C, eval₂Hom_X']
  simpa using ((hu k).map C).mul (isHomogeneous_C σ (X (t, r, k) : Poly K T p q κ))

theorem swapVars_minorProd_isHomogeneous [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → MvPolynomial σ K) (φ : T → Fin q → κ → MvPolynomial σ K) {d d' : ℕ}
    (hε : ∀ t a k, (ε t a k).IsHomogeneous d) (hφ : ∀ t b k, (φ t b k).IsHomogeneous d') :
    (swapVars (minorProd c c' ε φ)).IsHomogeneous
      (∑ t, (d * partSize (c t) + d' * partSize (c' t))) := by
  simp only [minorProd, map_prod, map_mul, map_pow]
  refine IsHomogeneous.prod _ _ _ fun t _ => IsHomogeneous.mul ?_ ?_
  · rw [partSize, Finset.mul_sum]
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    rw [← mul_assoc]
    refine IsHomogeneous.pow ?_ _
    rw [xMinor, RingHom.map_det]
    have := det_isWeightedHomogeneous (1 : σ → ℕ) (swapVars.mapMatrix (Matrix.of
      fun a b : Fin (i.val + 1) => (xForm t (lead i a) (ε t (lead i b)) : Poly _ T p q κ)))
      (fun _ => d) fun a b => swapVars_rowForm_isHomogeneous t _ _ (hε t _)
    simpa [mul_comm, IsHomogeneous] using this
  · rw [partSize, Finset.mul_sum]
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    rw [← mul_assoc]
    refine IsHomogeneous.pow ?_ _
    rw [yMinor, RingHom.map_det]
    have := det_isWeightedHomogeneous (1 : σ → ℕ) (swapVars.mapMatrix (Matrix.of
      fun a b : Fin (i.val + 1) => (yForm t (lead i a) (φ t (lead i b)) : Poly _ T p q κ)))
      (fun _ => d') fun a b => swapVars_rowForm_isHomogeneous t _ _ (hφ t _)
    simpa [mul_comm, IsHomogeneous] using this

end Param

section Field

variable {R S : Type} [CommRing R] [CommRing S] {T : Type*} [Fintype T] {ι : Type} [Fintype ι]
  {p q n : ℕ}

noncomputable def coordProd (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (w w' : T → ι → Fin n → R)
    (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → R) : Poly R T p q (Fin n) :=
  minorProd c c' (fun t a k => ∑ i, x (Sum.inl a, i) * w' t i k)
    fun t b => perpVec (dotPairing R n) (fun a k => ∑ i, x (Sum.inl a, i) * w' t i k)
      (fun a k => ∑ i, x (Sum.inr (Sum.inl a), i) * w t i k)
      fun k => ∑ i, x (Sum.inr (Sum.inr b), i) * w t i k

theorem map_coordProd (f : R →+* S) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → R) (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → R) :
    MvPolynomial.map f (coordProd c c' w w' x) =
      coordProd c c' (fun t i k => f (w t i k)) (fun t i k => f (w' t i k)) fun j => f (x j) := by
  simp only [coordProd, map_minorProd, map_perpVec_dotPairing]
  simp only [Function.comp_def, map_sum, map_mul]

variable {K : Type} [Field K]

theorem span_grid_coordProd [CharZero K] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → K) {dg : ℕ} (hdg : (2 * p + 1) * typeDegree c c' ≤ dg) :
    Submodule.span K ((fun x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → ℕ =>
      coordProd c c' w w' fun j => (x j : K)) '' {x | ∀ j, x j ≤ dg}) =
      Submodule.span K (Set.range (coordProd c c' w w')) := by
  let F : MvPolynomial ((Fin p ⊕ Fin p ⊕ Fin q) × ι) (Poly K T p q (Fin n)) :=
    swapVars (coordProd c c' (fun t i k => C (w t i k)) (fun t i k => C (w' t i k)) X)
  have hlin (r : Fin p ⊕ Fin p ⊕ Fin q) (u : ι → K) :
      (∑ i, X (r, i) * C (u i) : MvPolynomial _ K).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X K (r, i)).mul (isHomogeneous_C _ (u i))
  have hF : F.IsHomogeneous _ := swapVars_minorProd_isHomogeneous c c' _ _ (d := 1)
    (d' := 2 * p + 1) (fun t a k => hlin _ _) fun t b k =>
      perpVec_dotPairing_isHomogeneous _ _ _ (fun a k => hlin _ _) (fun a k => hlin _ _)
        (fun k => hlin _ _) k
  have hdeg : F.totalDegree ≤ dg := by
    refine hF.totalDegree_le.trans (le_trans ?_ hdg)
    rw [typeDegree, Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [mul_add]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
  have hev (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → K) :
      eval (fun j => C (x j)) F = coordProd c c' w w' x := by
    rw [eval_swapVars, map_coordProd]; simp only [eval_C, eval_X]
  have := GridInterpolation.span_grid_eval_eq_span_range (A := K) (K := K) dg F
    fun j => (degreeOf_le_totalDegree F j).trans hdeg
  simp only [Algebra.algebraMap_self, RingHom.id_apply, algebraMap_eq, hev] at this
  rw [← this]
  congr 2
  funext x
  rw [← hev]; simp only [map_natCast]

end Field

section CMGrid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K] [CharZero K]
  {T : Type*} [Fintype T] {ι : Type} [Fintype ι] {p q n : ℕ}

/-- The finite integral-parameter grid spans exactly the entire displayed
polynomial image over the independent coefficient field K. -/
theorem span_grid_perpVec_eq_span_range_coordProd (τ : T → E →+* K)
    (h : (Fin n → E) →ₗ[E] ((Fin n → E) → E))
    (hh : ∀ x y, h x y = ∑ k, x k * IsCMField.complexConj E (y k))
    (v : ι → Fin n → E) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) {dg : ℕ}
    (hdg : (2 * p + 1) * typeDegree c c' ≤ dg) :
    Submodule.span K {P | ∃ (A A' : Fin p → ι → ℕ) (B : Fin q → ι → ℕ),
      (∀ a i, A a i ≤ dg) ∧ (∀ a i, A' a i ≤ dg) ∧ (∀ b i, B b i ≤ dg) ∧
      P = minorProd c c' (fun t a k => τ t (IsCMField.complexConj E ((∑ i, (A a i : E) • v i) k)))
        fun t b k => τ t (perpVec h (fun a => ∑ i, (A a i : E) • v i)
          (fun a => ∑ i, (A' a i : E) • v i) (∑ i, (B b i : E) • v i) k)} =
      Submodule.span K (Set.range (coordProd c c'
        (fun t i k => τ t (v i k))
        (fun t i k => τ t (IsCMField.complexConj E (v i k))))) := by
  let γ : E →+* E := (IsCMField.complexConj E : E ≃ₐ[_] E)
  have hγ (x) : IsCMField.complexConj E x = γ x := rfl
  rw [← span_grid_coordProd c c' _ _ hdg]
  have key (A A' : Fin p → ι → ℕ) (B : Fin q → ι → ℕ) :
      minorProd c c' (fun t a k => τ t (IsCMField.complexConj E ((∑ i, (A a i : E) • v i) k)))
        (fun t b k => τ t (perpVec h (fun a => ∑ i, (A a i : E) • v i)
          (fun a => ∑ i, (A' a i : E) • v i) (∑ i, (B b i : E) • v i) k)) =
      coordProd c c' (fun t i k => τ t (v i k)) (fun t i k => τ t (γ (v i k)))
        fun j => ((Sum.elim A (Sum.elim A' B) j.1 j.2 : ℕ) : K) := by
    rw [coordProd]
    congr 1
    · funext t a k
      simp [hγ]
    · funext t b k
      refine map_perpVec_apply _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ k
      all_goals intros; simp [hγ, hh, dotProduct]
  congr 1
  ext P
  constructor
  · rintro ⟨A, A', B, hA, hA', hB, rfl⟩
    refine ⟨fun j => Sum.elim A (Sum.elim A' B) j.1 j.2, ?_, (key A A' B).symm⟩
    rintro ⟨a | a | b, i⟩
    exacts [hA a i, hA' a i, hB b i]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun a i => x (Sum.inl a, i), fun a i => x (Sum.inr (Sum.inl a), i),
      fun b i => x (Sum.inr (Sum.inr b), i), fun _ _ => hx _, fun _ _ => hx _, fun _ _ => hx _, ?_⟩
    rw [key]
    congr 1
    funext j
    obtain ⟨a | a | b, i⟩ := j <;> rfl

end CMGrid

end RHLean.Geometry.NativeTheta.Paired

end
