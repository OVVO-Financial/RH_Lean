import RHLean.Geometry.NativeFiniteIntegralDescent

/-!
# Constructing an integral completion from genuine spanning generators

The completion vectors are selected from the given target generators.
Their norm bounds and integral coordinates therefore survive unchanged.
No target basis of short integral vectors is assumed to exist.
-/

noncomputable section

open Module

namespace RHLean.Geometry

section Selection

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Extend an independent family using only members of an actual spanning
set. Exactly the rank defect many additional vectors are selected. -/
theorem nativeCompletionFromSpanningSetOver {r d : ℕ}
    (v : Fin r → V) (hv : LinearIndependent K v)
    (hdim : finrank K V = r + d)
    (S : Set V) (hS : Submodule.span K S = ⊤) :
    ∃ (w : Fin d → V) (B : Basis (Fin r ⊕ Fin d) K V),
      (∀ i : Fin r, B (Sum.inl i) = v i) ∧
      (∀ j : Fin d, B (Sum.inr j) = w j) ∧
      (∀ j : Fin d, w j ∈ S) := by
  classical
  let hs := hv.linearIndepOn_id
  have hst : Set.range v ⊆ Set.range v ∪ S := Set.subset_union_left
  have htop : ⊤ ≤ Submodule.span K (Set.range v ∪ S) := by
    rw [← hS]
    exact Submodule.span_mono Set.subset_union_right
  let T : Set V := hs.extend hst
  let B0 : Basis T K V := Basis.extendLe hs hst htop
  let W : Set V := T \ Set.range v
  let e : (Fin r ⊕ W) ≃ T :=
    (Equiv.sumCongr (Equiv.ofInjective v hv.injective) (Equiv.refl W)).trans
      (Equiv.Set.sumDiffSubset (hs.subset_extend hst))
  let B : Basis (Fin r ⊕ W) K V := B0.reindex e.symm
  let : Finite T := Module.Finite.finite_basis B0
  let incl : W → T := fun x => ⟨x.1, x.2.1⟩
  have hincl : Function.Injective incl := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : T => (z : V)) hxy
  let : Finite W := Finite.of_injective incl hincl
  let : Fintype W := Fintype.ofFinite W
  have hc : r + Fintype.card W = finrank K V := by
    simpa using (Module.finrank_eq_card_basis B).symm
  have hcard : Fintype.card W = d := by omega
  let eW : W ≃ Fin d := Fintype.equivFinOfCardEq hcard
  let w : Fin d → V := fun j => (eW.symm j).1
  let B' : Basis (Fin r ⊕ Fin d) K V :=
    B.reindex (Equiv.sumCongr (Equiv.refl (Fin r)) eW)
  have hleft (i : Fin r) : B (Sum.inl i) = v i := by
    change (B0.reindex e.symm) (Sum.inl i) = v i
    rw [Basis.reindex_apply]
    change (Basis.extendLe hs hst htop) (e (Sum.inl i)) = v i
    rw [Basis.extendLe_apply_self]
    rfl
  have hright (j : W) : B (Sum.inr j) = (j : V) := by
    change (B0.reindex e.symm) (Sum.inr j) = (j : V)
    rw [Basis.reindex_apply]
    change (Basis.extendLe hs hst htop) (e (Sum.inr j)) = (j : V)
    rw [Basis.extendLe_apply_self]
    rfl
  refine ⟨w, B', ?_, ?_, ?_⟩
  · intro i
    simpa [B', Basis.reindex_apply] using hleft i
  · intro j
    simpa [B', w, Basis.reindex_apply] using hright (eW.symm j)
  · intro j
    exact (hs.extend_subset hst (eW.symm j).2.1).resolve_left (eW.symm j).2.2

end Selection

section IntegralSelection

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem nativeCompletionFromSpanningSet {r d : ℕ}
    (v : Fin r → V) (hv : LinearIndependent ℝ v)
    (hdim : finrank ℝ V = r + d)
    (S : Set V) (hS : Submodule.span ℝ S = ⊤) :
    ∃ (w : Fin d → V) (B : Basis (Fin r ⊕ Fin d) ℝ V),
      (∀ i : Fin r, B (Sum.inl i) = v i) ∧
      (∀ j : Fin d, B (Sum.inr j) = w j) ∧
      (∀ j : Fin d, w j ∈ S) :=
  nativeCompletionFromSpanningSetOver v hv hdim S hS

/-- Integrality of the original image and the actual spanning set produces
a nonzero square INTEGER matrix. Nonsingularity is proved from the
constructed basis, rather than requested as a new witness assumption. -/
theorem nativeIntegralCompletionFromSpanningSet {r d : ℕ}
    (b : Basis (Fin r ⊕ Fin d) ℝ V)
    (v : Fin r → V) (hv : LinearIndependent ℝ v)
    (S : Set V) (hS : Submodule.span ℝ S = ⊤)
    (hvi : ∀ i : Fin r, ∀ k : Fin r ⊕ Fin d,
      ∃ z : ℤ, b.repr (v i) k = (z : ℝ))
    (hSi : ∀ x ∈ S, ∀ k : Fin r ⊕ Fin d,
      ∃ z : ℤ, b.repr x k = (z : ℝ)) :
    ∃ (w : Fin d → V) (C : Matrix (Fin r ⊕ Fin d) (Fin r ⊕ Fin d) ℤ),
      (∀ j : Fin d, w j ∈ S) ∧
      b.toMatrix (Sum.elim v w) = C.map (fun z : ℤ => (z : ℝ)) ∧
      C.det ≠ 0 := by
  classical
  have hdim : finrank ℝ V = r + d := by
    simpa using Module.finrank_eq_card_basis b
  obtain ⟨w, B, hl, hr, hw⟩ := nativeCompletionFromSpanningSet v hv hdim S hS
  have hBi : ∀ j k : Fin r ⊕ Fin d, ∃ z : ℤ, b.repr (B j) k = (z : ℝ) := by
    intro j k
    cases j with
    | inl j => rw [hl j]; exact hvi j k
    | inr j => rw [hr j]; exact hSi (w j) (hw j) k
  let C : Matrix (Fin r ⊕ Fin d) (Fin r ⊕ Fin d) ℤ :=
    fun k j => Classical.choose (hBi j k)
  have hcoords : b.toMatrix (B : (Fin r ⊕ Fin d) → V) =
      C.map (fun z : ℤ => (z : ℝ)) := by
    ext k j
    exact Classical.choose_spec (hBi j k)
  have hfamily : Sum.elim v w = (B : (Fin r ⊕ Fin d) → V) := by
    funext j
    cases j with
    | inl j => exact (hl j).symm
    | inr j => exact (hr j).symm
  have hdet : (C.det : ℝ) ≠ 0 := by
    have hm := b.toMatrix_mul_toMatrix_flip B
    have hd := congrArg Matrix.det hm
    rw [Matrix.det_mul, Matrix.det_one, hcoords, ← Int.cast_det] at hd
    intro hz
    rw [hz, zero_mul] at hd
    norm_num at hd
  refine ⟨w, C, hw, ?_, ?_⟩
  · rw [hfamily]
    exact hcoords
  · intro hz
    apply hdet
    simp [hz]

end IntegralSelection

section QuantitativeDescent

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]

/-- Fully constructed finite volume descent. The only target vectors
assumed short are the genuine spanning generators; the complement and
its nonzero integral determinant are constructed by the preceding theorem.
-/
theorem nativeIntegralDescent_from_generators {r d : ℕ}
    (a : Basis (Fin r) ℝ U) (b : Basis (Fin r ⊕ Fin d) ℝ V)
    (f : U →ₗ[ℝ] V) (hinj : Function.Injective f)
    (S : Set V) (hS : Submodule.span ℝ S = ⊤)
    (hfi : ∀ i : Fin r, ∀ k : Fin r ⊕ Fin d,
      ∃ z : ℤ, b.repr (f (a i)) k = (z : ℝ))
    (hSi : ∀ x ∈ S, ∀ k : Fin r ⊕ Fin d,
      ∃ z : ℤ, b.repr x k = (z : ℝ))
    (P Λ : ℝ)
    (hf : ∀ x : U, ‖f x‖ ≤ Real.exp P * ‖x‖)
    (hSnorm : ∀ x ∈ S, ‖x‖ ≤ Real.exp Λ) :
    (Matrix.gram ℝ (b : (Fin r ⊕ Fin d) → V)).det ≤
      (Matrix.gram ℝ (a : Fin r → U)).det *
        Real.exp (2 * (r : ℝ) * P + 2 * (d : ℝ) * Λ) := by
  have hli : LinearIndependent ℝ (fun i => f (a i)) :=
    a.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hinj)
  obtain ⟨w, C, hw, hC, hdet⟩ :=
    nativeIntegralCompletionFromSpanningSet b (fun i => f (a i)) hli S hS hfi hSi
  have h := nativeIntegralDescent_with_completion a b f w C hC P Λ hf
    (fun j => hSnorm (w j) (hw j))
  have hc : (1 : ℝ) ≤ |(C.det : ℝ)| := by
    exact_mod_cast Int.one_le_abs hdet
  have hc2 : (1 : ℝ) ≤ (C.det : ℝ) ^ 2 := by
    nlinarith [sq_abs (C.det : ℝ)]
  have hb0 : 0 ≤ (Matrix.gram ℝ (b : (Fin r ⊕ Fin d) → V)).det :=
    (Matrix.posSemidef_gram ℝ (b : (Fin r ⊕ Fin d) → V)).det_nonneg
  exact (show (Matrix.gram ℝ (b : (Fin r ⊕ Fin d) → V)).det ≤
    (C.det : ℝ) ^ 2 * (Matrix.gram ℝ (b : (Fin r ⊕ Fin d) → V)).det by
      nlinarith).trans h

/-- Squared-covolume slope of the integral span of an actual real basis.
This is the Euclidean Z-lattice normalization, not an identification with
Alpoge's number-field `slope_sq`. -/
def nativeIntegralSquareSlope {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I] [DecidableEq I]
    (b : Basis I ℝ E) : ℝ :=
  -Real.log (Matrix.gram ℝ (b : I → E)).det / Fintype.card I

/-- The exact finite rank-defect descent inequality follows from the
constructed integral frame and its proved volume bound. No slope estimate
is an input: only the original map, integer coordinates and generators.
-/
theorem nativeIntegralDescent_slope {r d : ℕ} (hr : 0 < r)
    (a : Basis (Fin r) ℝ U) (b : Basis (Fin r ⊕ Fin d) ℝ V)
    (f : U →ₗ[ℝ] V) (hinj : Function.Injective f)
    (S : Set V) (hS : Submodule.span ℝ S = ⊤)
    (hfi : ∀ i : Fin r, ∀ k : Fin r ⊕ Fin d,
      ∃ z : ℤ, b.repr (f (a i)) k = (z : ℝ))
    (hSi : ∀ x ∈ S, ∀ k : Fin r ⊕ Fin d,
      ∃ z : ℤ, b.repr x k = (z : ℝ))
    (P Λ : ℝ)
    (hf : ∀ x : U, ‖f x‖ ≤ Real.exp P * ‖x‖)
    (hSnorm : ∀ x ∈ S, ‖x‖ ≤ Real.exp Λ) :
    ((r : ℝ) / ((r : ℝ) + d)) * (nativeIntegralSquareSlope a - 2 * P) -
      (2 * (d : ℝ) * Λ) / ((r : ℝ) + d) ≤ nativeIntegralSquareSlope b := by
  have hvol := nativeIntegralDescent_from_generators a b f hinj S hS hfi hSi P Λ hf hSnorm
  have ha : 0 < (Matrix.gram ℝ (a : Fin r → U)).det :=
    (Matrix.posDef_gram_of_linearIndependent a.linearIndependent).det_pos
  have hb : 0 < (Matrix.gram ℝ (b : (Fin r ⊕ Fin d) → V)).det :=
    (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos
  have hlog := Real.log_le_log hb hvol
  rw [Real.log_mul ha.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hN : (0 : ℝ) < (r : ℝ) + d := by positivity
  have hmuA : (r : ℝ) * nativeIntegralSquareSlope a =
      -Real.log (Matrix.gram ℝ (a : Fin r → U)).det := by
    simp only [nativeIntegralSquareSlope, Fintype.card_fin]
    field_simp [ne_of_gt hrR]
  have hmuB : ((r : ℝ) + d) * nativeIntegralSquareSlope b =
      -Real.log (Matrix.gram ℝ (b : (Fin r ⊕ Fin d) → V)).det := by
    simp only [nativeIntegralSquareSlope, Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
    field_simp [ne_of_gt hN]
  have hnum : (r : ℝ) * (nativeIntegralSquareSlope a - 2 * P) -
      2 * (d : ℝ) * Λ ≤ ((r : ℝ) + d) * nativeIntegralSquareSlope b := by
    nlinarith
  have hfrac : ((r : ℝ) / ((r : ℝ) + d)) * (nativeIntegralSquareSlope a - 2 * P) -
      (2 * (d : ℝ) * Λ) / ((r : ℝ) + d) =
      ((r : ℝ) * (nativeIntegralSquareSlope a - 2 * P) - 2 * (d : ℝ) * Λ) /
        ((r : ℝ) + d) := by ring
  rw [hfrac]
  exact (div_le_iff₀ hN).mpr (by simpa only [mul_comm] using hnum)

end QuantitativeDescent

end RHLean.Geometry
