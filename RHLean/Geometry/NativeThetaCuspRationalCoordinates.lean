import RHLean.Geometry.NativeThetaCuspNativeVacuum

/-!
# Shared rational coordinates and the actual common half-root phase

The ambient space is the rationalization of the original integral trace
lattice. Its form is the base change of the original integer polarization,
and its half-root operator is the base change of the original CM action.
A single rational phase is defined on the entire ambient space, rather than
by an inverse to the integral-coordinate map. Its restriction is proved to
be the canonical native integral semicharacter.

These common coordinates and phase are the input needed to compare vacua
of distinct shifted lattices. A vacuum separately expressed in its own
integral basis does not provide that comparison.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/
HMatMulVecPerCrd.lean (`vecQ`, `crd`, `EF_vecQ`) and
TensorLatticeSelfDualSemicharacterIndex.lean (`epsW_semichar`).
The native tensor rationalization constructs these coordinates directly.
The source archive states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module Matrix
open scoped TensorProduct BigOperators

namespace RHLean.Geometry.NativeTheta.Cusp.RationalCoordinates

open NativeIntegralSymplectic NativeVacuum AppellHumbert

section Coordinates

variable {M κ ι : Type} [AddCommGroup M] [Module ℤ M] [Fintype ι]

/-- The actual rationalization of the integral module. -/
abbrev Space (M : Type) [AddCommGroup M] [Module ℤ M] := ℚ ⊗[ℤ] M

/-- Rational coordinates in the base change of the same integral basis. -/
def coord (b : Basis (ι ⊕ ι) ℤ M) :
    (κ → Space M) ≃ₗ[ℚ] (Matrix κ ι ℚ × Matrix κ ι ℚ) where
  toFun x :=
    (fun k i => (b.baseChange ℚ).equivFun (x k) (Sum.inl i),
      fun k i => (b.baseChange ℚ).equivFun (x k) (Sum.inr i))
  invFun p := fun k => (b.baseChange ℚ).equivFun.symm (Sum.elim (p.1 k) (p.2 k))
  left_inv x := by
    funext k
    apply (b.baseChange ℚ).equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext j
    cases j <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext k i
      exact congrFun ((b.baseChange ℚ).equivFun.apply_symm_apply
        (Sum.elim (p.1 k) (p.2 k))) (Sum.inl i)
    · funext k i
      exact congrFun ((b.baseChange ℚ).equivFun.apply_symm_apply
        (Sum.elim (p.1 k) (p.2 k))) (Sum.inr i)
  map_add' x y := by
    apply Prod.ext
    · funext k i
      change (b.baseChange ℚ).equivFun (x k + y k) (Sum.inl i) =
        (b.baseChange ℚ).equivFun (x k) (Sum.inl i) +
          (b.baseChange ℚ).equivFun (y k) (Sum.inl i)
      simp only [map_add, Pi.add_apply]
    · funext k i
      change (b.baseChange ℚ).equivFun (x k + y k) (Sum.inr i) =
        (b.baseChange ℚ).equivFun (x k) (Sum.inr i) +
          (b.baseChange ℚ).equivFun (y k) (Sum.inr i)
      simp only [map_add, Pi.add_apply]
  map_smul' a x := by
    apply Prod.ext
    · funext k i
      change (b.baseChange ℚ).equivFun (a • x k) (Sum.inl i) =
        a * (b.baseChange ℚ).equivFun (x k) (Sum.inl i)
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    · funext k i
      change (b.baseChange ℚ).equivFun (a • x k) (Sum.inr i) =
        a * (b.baseChange ℚ).equivFun (x k) (Sum.inr i)
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]

/-- The rational coordinate map agrees with the previously constructed
integral coordinates on every element of the original lattice. -/
theorem coord_integral (b : Basis (ι ⊕ ι) ℤ M) (x : κ → M) :
    coord b (fun k => (1 : ℚ) ⊗ₜ[ℤ] x k) = coordinates b x := by
  apply Prod.ext
  · funext k i
    change (b.baseChange ℚ).repr ((1 : ℚ) ⊗ₜ[ℤ] x k) (Sum.inl i) =
      (b.repr (x k) (Sum.inl i) : ℚ)
    simp
  · funext k i
    change (b.baseChange ℚ).repr ((1 : ℚ) ⊗ₜ[ℤ] x k) (Sum.inr i) =
      (b.repr (x k) (Sum.inr i) : ℚ)
    simp

/-- No denominators or arbitrary inverse choices enter the inclusion of
the original integral module into its rationalization. -/
theorem integral_injective (b : Basis (ι ⊕ ι) ℤ M) :
    Function.Injective (fun x : M => (1 : ℚ) ⊗ₜ[ℤ] x) := by
  intro x y h
  apply b.ext_elem
  intro i
  have he := congrArg (fun z => (b.baseChange ℚ).repr z i) h
  simpa using he

end Coordinates

section Symplectic

private theorem form_eq_sum {R M ι : Type} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype ι] {B : LinearMap.BilinForm R M} (hB : B.IsAlt)
    (b : Basis (ι ⊕ ι) R M) (hb : IsSymplecticBasis B b) (x y : M) :
    B x y = ∑ i, (b.repr x (Sum.inl i) * b.repr y (Sum.inr i) -
      b.repr y (Sum.inl i) * b.repr x (Sum.inr i)) := by
  classical
  have he : Sum.elim (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i)) = b := by
    funext i; cases i <;> rfl
  have hl (i : ι) : B (b (Sum.inl i)) y = b.repr y (Sum.inr i) := by
    have h := IsSymplecticFamily.apply_left_sum hb (fun i => b.repr y i) i
    simpa only [he, b.sum_repr, mul_one] using h
  have hr (i : ι) : B (b (Sum.inr i)) y = -b.repr y (Sum.inl i) := by
    have h := IsSymplecticFamily.apply_sum_right hb (fun i => b.repr y i) i
    rw [he, b.sum_repr, mul_one] at h
    rw [← hB.neg_eq, h]
  calc
    B x y = ∑ i, b.repr x i * B (b i) y := by
      conv_lhs => rw [← b.sum_repr x]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    _ = _ := by
      rw [Fintype.sum_sum_type, Finset.sum_sub_distrib]
      simp only [hl, hr, mul_neg, Finset.sum_neg_distrib]
      have heq : (∑ i, b.repr x (Sum.inr i) * b.repr y (Sum.inl i)) =
          ∑ i, b.repr y (Sum.inl i) * b.repr x (Sum.inr i) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [heq]
      ring

end Symplectic

section Native

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {H : NativeGeometricHost E} (D : NativeGeometricDatum H)

/-- The original polarization, base changed without a scalar correction. -/
abbrev form : LinearMap.BilinForm ℚ (Space D.La) := D.EF.baseChange ℚ

/-- The original integral CM action, base changed to the rational space. -/
def action (a : 𝓞 E) : Space D.La →ₗ[ℚ] Space D.La :=
  ((LinearMap.lsmul (𝓞 E) D.La a).restrictScalars ℤ).baseChange ℚ

@[simp] theorem action_tmul (a : 𝓞 E) (q : ℚ) (x : D.La) :
    action D a (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] (a • x) := by
  simp [action, LinearMap.baseChange_tmul]

@[simp] theorem form_integral (x y : D.La) :
    form D ((1 : ℚ) ⊗ₜ[ℤ] x) ((1 : ℚ) ⊗ₜ[ℤ] y) = (D.EF x y : ℚ) := by
  simp [form, LinearMap.BilinForm.baseChange_tmul]

theorem form_skew (x y : Space D.La) : form D y x = -form D x y := by
  induction x using TensorProduct.inductionOn with
  | zero => simp
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx', neg_add]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | zero => simp
    | add y y' hy hy' =>
      simp only [map_add, LinearMap.add_apply, hy, hy', neg_add]
    | tmul a' y =>
      simp only [form, LinearMap.BilinForm.baseChange_tmul, AppellHumbert.form_skew,
        Int.cast_neg, zsmul_eq_mul]
      ring

theorem form_alt : (form D).IsAlt := by
  intro x
  have h := form_skew D x x
  linarith

/-- Adjointness holds on all rational vectors, not only on the integral image. -/
theorem action_adjoint (a : 𝓞 E) (x y : Space D.La) :
    form D (action D a x) y = form D x (action D (H.bar a) y) := by
  induction x using TensorProduct.inductionOn with
  | zero => simp
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | zero => simp
    | add y y' hy hy' =>
      simp only [map_add, hy, hy']
    | tmul q' y =>
      rw [action_tmul, action_tmul]
      simp only [form, LinearMap.BilinForm.baseChange_tmul, D.adj]

/-- The same half-root identity on the rationalized module. -/
theorem action_halfRoot (x : Space D.La) :
    action D H.w0 x + action D (H.bar H.w0) x = x := by
  induction x using TensorProduct.inductionOn with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add]
    calc
      _ = (action D H.w0 x + action D (H.bar H.w0) x) +
          (action D H.w0 y + action D (H.bar H.w0) y) := by abel
      _ = x + y := by rw [hx, hy]
  | tmul q x =>
    rw [action_tmul, action_tmul, ← TensorProduct.tmul_add, ← add_smul,
      weight_add_bar, one_smul]

theorem baseChange_symplectic {ι : Type} [Fintype ι]
    (b : Basis (ι ⊕ ι) ℤ D.La) (hb : IsSymplecticBasis D.EF b) :
    IsSymplecticBasis (form D) (b.baseChange ℚ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [Basis.baseChange_apply, form, LinearMap.BilinForm.baseChange_tmul,
      hb.left_left, zero_smul]
  · intro i j
    simp only [Basis.baseChange_apply, form, LinearMap.BilinForm.baseChange_tmul,
      hb.right_right, zero_smul]
  · intro i
    simp [Basis.baseChange_apply, form, LinearMap.BilinForm.baseChange_tmul,
      hb.left_right_self]
  · intro i j hij
    simp only [Basis.baseChange_apply, form, LinearMap.BilinForm.baseChange_tmul,
      hb.left_right_ne i j hij, zero_smul]

/-- The shared rational coordinates preserve the actual native trace form. -/
theorem coord_pairing {κ ι : Type} [Fintype κ] [Fintype ι]
    (b : Basis (ι ⊕ ι) ℤ D.La) (hb : IsSymplecticBasis D.EF b)
    (x y : κ → Space D.La) :
    (∑ k, ((coord b x).1 k ⬝ᵥ (coord b y).2 k -
      (coord b y).1 k ⬝ᵥ (coord b x).2 k)) = ∑ k, form D (x k) (y k) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  change (∑ i, (b.baseChange ℚ).repr (x k) (Sum.inl i) *
      (b.baseChange ℚ).repr (y k) (Sum.inr i)) -
    (∑ i, (b.baseChange ℚ).repr (y k) (Sum.inl i) *
      (b.baseChange ℚ).repr (x k) (Sum.inr i)) = _
  rw [form_eq_sum (form_alt D) _ (baseChange_symplectic D b hb),
    Finset.sum_sub_distrib]

/-- The rational quadratic refinement uses the actual half-root operator. -/
def quadratic (x : Space D.La) : ℚ := form D x (action D H.w0 x)

@[simp] theorem quadratic_integral (x : D.La) :
    quadratic D ((1 : ℚ) ⊗ₜ[ℤ] x) = (quadraticRefinement D x : ℚ) := by
  rw [quadratic, action_tmul, form_integral]
  rfl

theorem quadratic_add (x y : Space D.La) :
    quadratic D (x + y) = quadratic D x + quadratic D y + form D x y -
      2 * form D x (action D (H.bar H.w0) y) := by
  have h1 : form D y (action D H.w0 x) = -form D x (action D (H.bar H.w0) y) := by
    rw [form_skew, action_adjoint]
  have h2 : form D x (action D H.w0 y) + form D x (action D (H.bar H.w0) y) =
      form D x y := by
    rw [← map_add, action_halfRoot]
  simp only [quadratic, map_add, LinearMap.add_apply]
  linarith

variable {κ : Type} [Fintype κ]

/-- One common phase, defined on the entire rational ambient space. -/
def commonPhase (x : κ → Space D.La) : ℂ :=
  Complex.exp (Real.pi * Complex.I * ((∑ k, quadratic D (x k) : ℚ) : ℂ))

theorem norm_commonPhase (x : κ → Space D.La) : ‖commonPhase D x‖ = 1 := by
  rw [commonPhase, Complex.norm_exp]
  simp

/-- On the actual integral lattice this is the canonical native phase,
with the original sign and half-root normalization. -/
theorem commonPhase_integral (x : κ → D.La) :
    commonPhase D (fun k => (1 : ℚ) ⊗ₜ[ℤ] x k) = ∏ k, phase D (x k) := by
  simp only [commonPhase, quadratic_integral, Rat.cast_sum, Rat.cast_intCast,
    Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [phase, intSign_eq_exp]
  congr 1
  ring

/-- The common phase satisfies the required cocycle whenever the actual
cross-pairings with the conjugate half-root are integral. Self-duality and
stability of a shifted lattice supply precisely these integer pairings. -/
theorem commonPhase_add_of_integral (x y : κ → Space D.La)
    (hint : ∀ k, ∃ m : ℤ, form D (x k) (action D (H.bar H.w0) (y k)) = m) :
    commonPhase D (x + y) = commonPhase D x * commonPhase D y *
      Complex.exp (Real.pi * Complex.I * ((∑ k, form D (x k) (y k) : ℚ) : ℂ)) := by
  choose m hm using hint
  have hq : (∑ k, quadratic D ((x + y) k)) =
      (∑ k, quadratic D (x k)) + (∑ k, quadratic D (y k)) +
        (∑ k, form D (x k) (y k)) - 2 * ((∑ k, m k : ℤ) : ℚ) := by
    simp only [Pi.add_apply, quadratic_add, hm, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Int.cast_sum, Finset.mul_sum]
  rw [commonPhase, hq]
  have he : Real.pi * Complex.I *
      (((∑ k, quadratic D (x k)) + (∑ k, quadratic D (y k)) +
        (∑ k, form D (x k) (y k)) - 2 * ((∑ k, m k : ℤ) : ℚ) : ℚ) : ℂ) =
      Real.pi * Complex.I * ((∑ k, quadratic D (x k) : ℚ) : ℂ) +
      Real.pi * Complex.I * ((∑ k, quadratic D (y k) : ℚ) : ℂ) +
      Real.pi * Complex.I * ((∑ k, form D (x k) (y k) : ℚ) : ℂ) +
      ((-(∑ k, m k) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
    Complex.exp_add, Complex.exp_add]
  rfl

end Native

end RHLean.Geometry.NativeTheta.Cusp.RationalCoordinates
