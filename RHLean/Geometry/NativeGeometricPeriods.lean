import RHLean.Geometry.NativeGeometricDatum

/-!
# The original period predicate and the positive Hermitian form it requires

The predicates below retain the source's complete IsTypeFn and IsPeriod
statements. In particular the period range must be discrete and span the
whole real vector space, and the Hermitian form's imaginary part must be
the SAME integral alternating form. The source Hermitian form is linear
in its FIRST argument, whereas the prescribed field form conjugates its
first argument; the positive convention is EF(J x,x)>0 in both constructions.

The supplying lemma constructs the period map and its range from a real
coordinate equivalence. It proves injectivity, discreteness, full span and
the positive Hermitian form, rather than taking any of these conclusions
as a premise. NativePrescribedGeometricPeriod supplies that equivalence
and every compatibility on the actual prescribed lattice.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/
ToroidalCompactification/IsHolPeriods.lean, IsTypeFn and IsPeriod;
ThetaUnifAV.lean, hermForm;
src/Development/AbelianVarietyTheory/Proofs/ToricGeometry/
ExistsEquivOfSumEq.lean, exists_herm and the lattice part of exists_isPeriod.
The source mirror states no license; attribution is retained without
assigning one. No Moduli, SAB, terminal RH theorem or compiled source
artifact is imported or assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField Matrix
open scoped Classical BigOperators TensorProduct ComplexConjugate

namespace RHLean.Geometry.NativeGeometricPeriods

/-- Literal source convention: linear in the first variable. -/
def hermForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (z w : Fin g → ℂ) : ℂ := z ⬝ᵥ Hm.mulVec (star w)

section Predicates

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsTypeFn (H : NativeGeometricHost E) (p q : ℕ) {g : ℕ}
    (ty : Fin g → (E →+* ℂ)) : Prop :=
  ∀ τ : E →+* ℂ,
    (τ (H.rt : E) = H.rt0 → Nat.card {i // ty i = τ} = p) ∧
    (τ (H.rt : E) ≠ H.rt0 → Nat.card {i // ty i = τ} = q)

def IsPeriod {H : NativeGeometricHost E} (D : NativeGeometricDatum H)
    {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) : Prop :=
  (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) ∧
    Function.Injective P ∧ DiscreteTopology P.range ∧
    Submodule.span ℝ (Set.range P) = ⊤ ∧
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y

end Predicates

/-- The source's actual positive Hermitian form, with its exact imaginary
part. The sign is fixed by the original EF(J x,x)>0 convention. -/
theorem exists_herm {g : ℕ} (B : LinearMap.BilinForm ℝ (Fin g → ℂ))
    (halt : ∀ x y, B x y = -B y x)
    (hI : ∀ x y, B (Complex.I • x) (Complex.I • y) = B x y)
    (hpos : ∀ x, x ≠ 0 → 0 < B (Complex.I • x) x) :
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm x y).im = B x y := by
  have hII : ∀ x : Fin g → ℂ, Complex.I • Complex.I • x = -x := fun x => by
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  let h : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun x y =>
    B (Complex.I • x) y + B x y * Complex.I
  have hconj : ∀ x y, h x y = conj (h y x) := fun x y => by
    have h1 : B (Complex.I • x) y = B (Complex.I • y) x := by
      rw [← hI, hII, halt]
      simp
    apply Complex.ext
    · simp [h, h1]
    · simp [h, halt x y]
  have hsm : ∀ (c : ℂ) (x : Fin g → ℂ),
      c • x = c.re • x + c.im • (Complex.I • x) := fun c x => by
    funext k
    apply Complex.ext
    · simp [sub_eq_add_neg]
    · simp
  let hl : (Fin g → ℂ) → ((Fin g → ℂ) →ₗ[ℂ] ℂ) := fun y =>
    { toFun := fun x => h x y
      map_add' := fun x x' => by simp [h]; ring
      map_smul' := fun c x => by
        simp only [h]
        rw [smul_comm Complex.I c x, hsm c x, hsm c (Complex.I • x), hII]
        apply Complex.ext
        · simp [sub_eq_add_neg]
        · simp }
  have hsum : ∀ x y, h x y = ∑ i, x i * h (Pi.single i 1) y := fun x y => by
    change hl y x = ∑ i, x i • hl y (Pi.single i 1)
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  have key : ∀ x y,
      hermForm (Matrix.of fun i j => h (Pi.single i 1) (Pi.single j 1)) x y =
        h x y := fun x y => by
    rw [hsum x y]
    unfold hermForm dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [hconj, hsum y, map_sum (starRingEnd ℂ)]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← hconj, mul_comm]
    rfl
  refine ⟨Matrix.of fun i j => h (Pi.single i 1) (Pi.single j 1), ?_,
    fun z hz => ?_, fun x y => ?_⟩
  · ext i j
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply,
      hconj (Pi.single i 1)]
    rfl
  · rw [key]
    simpa [h] using hpos z hz
  · rw [key]
    simp [h]

/-- Apply an actual real tensor equivalence to the original integer lattice. -/
def periodOfRealEquiv {La : Type} [AddCommGroup La] {g : ℕ}
    (e : (ℝ ⊗[ℤ] La) ≃ₗ[ℝ] (Fin g → ℂ)) : La →+ (Fin g → ℂ) where
  toFun x := e (1 ⊗ₜ x)
  map_zero' := by simp
  map_add' x y := by rw [TensorProduct.tmul_add, map_add]

theorem periodOfRealEquiv_apply {La : Type} [AddCommGroup La] {g : ℕ}
    (e : (ℝ ⊗[ℤ] La) ≃ₗ[ℝ] (Fin g → ℂ)) (x : La) :
    periodOfRealEquiv e x = e (1 ⊗ₜ x) := rfl

section Construction

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : NativeGeometricHost E} (D : NativeGeometricDatum H)
    [Module.Free ℤ D.La] [Module.Finite ℤ D.La]

/-- Construct every original period condition from actual coordinates and
the already proved positive complex structure on the SAME lattice. -/
theorem periodOfRealEquiv_isPeriod {g : ℕ}
    (ty : Fin g → (E →+* ℂ))
    (e : (ℝ ⊗[ℤ] D.La) ≃ₗ[ℝ] (Fin g → ℂ))
    (J : (ℝ ⊗[ℤ] D.La) →ₗ[ℝ] (ℝ ⊗[ℤ] D.La))
    (heJ : ∀ x, e (J x) = Complex.I • e x)
    (hinv : ∀ x y, D.EF.baseChange ℝ (J x) (J y) = D.EF.baseChange ℝ x y)
    (hpos : ∀ x, x ≠ 0 → 0 < D.EF.baseChange ℝ (J x) x)
    (hact : ∀ (a : 𝓞 E) x i,
      e (1 ⊗ₜ (a • x)) i = ty i (a : E) * e (1 ⊗ₜ x) i) :
    IsPeriod D ty (periodOfRealEquiv e) := by
  let P := periodOfRealEquiv e
  have hP : ∀ x, P x = e (1 ⊗ₜ x) := fun _ => rfl
  let b := Module.Free.chooseBasis ℤ D.La
  let c := (b.baseChange ℝ).map e
  have hc : ∀ i, c i = P (b i) := fun i => by simp [c, hP]
  have hrange : P.range = (Submodule.span ℤ (Set.range c)).toAddSubgroup := by
    have h1 : Set.range c = P.toIntLinearMap '' Set.range b := by
      rw [← Set.range_comp]
      congr 1
      funext i
      exact hc i
    rw [h1, ← Submodule.map_span, b.span_eq]
    ext z
    simp
  change IsPeriod D ty P
  refine ⟨hact, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hP, e.map_eq_zero_iff] at hx
    apply b.ext_elem
    intro i
    have := congrArg (fun v => (b.baseChange ℝ).repr v i) hx
    simpa using this
  · rw [hrange]
    infer_instance
  · rw [eq_top_iff, ← c.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hc i).symm⟩
  · have halt0 : ∀ x y, D.EF x y = -D.EF y x := fun x y => by
      have := D.alt (x + y)
      simp only [map_add, LinearMap.add_apply, D.alt] at this
      linarith
    have halt : ∀ x y, D.EF.baseChange ℝ x y = -D.EF.baseChange ℝ y x := fun x y => by
      induction x using TensorProduct.inductionOn with
      | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
      | tmul r x =>
        induction y using TensorProduct.inductionOn with
        | add y y' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
        | tmul r' y => simp [halt0 x y, mul_comm]
    have hs : ∀ z, e.symm (Complex.I • z) = J (e.symm z) := fun z => by
      rw [e.symm_apply_eq, heJ, e.apply_symm_apply]
    obtain ⟨Hm, h1, h2, h3⟩ := exists_herm
      ((D.EF.baseChange ℝ).comp e.symm.toLinearMap e.symm.toLinearMap)
      (fun x y => halt _ _) (fun x y => by simp [hs, hinv])
      (fun x hx => by simpa [hs] using hpos (e.symm x) (by simpa using hx))
    refine ⟨Hm, h1, h2, fun x y => ?_⟩
    rw [h3]
    simp [hP]

end Construction
end RHLean.Geometry.NativeGeometricPeriods

end
