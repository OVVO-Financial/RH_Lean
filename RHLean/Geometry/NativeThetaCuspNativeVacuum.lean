import RHLean.Geometry.NativeThetaCuspVacuum
import RHLean.Geometry.NativeGeometricSymplecticBasis
import RHLean.Geometry.NativeThetaAppellHumbert

/-!
# The normalized finite-adelic vacuum of the actual native trace lattice

The original projective O(E)-module and perfect trace polarization determine
integral symplectic coordinates. The canonical half-root semicharacter is
transported through those proved coordinates. The rational Schwartz–Bruhat
vacuum is then constructed, with its exact Haar norm one and unique fixed
line. Neither a vacuum nor a fixed-vector existence statement is an input.

The lattice is not replaced by a free O(E)-module: only the integral
symplectic coordinates already proved for the same lattice are used.
This is the finite-adelic vacuum primitive used by Alpöge's
`TensorLatticeVacuaExistUnique` and `ExistsVacuaAndMultipliers`. Level test
functions, Weil covariance, isotropic no-coinvariants, the doubled kernel,
and the global cusp span remain distinct subsequent constructions.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/
TensorLatticeVacuaExistUnique.lean (`Good.vac`), specialized to the native
trace lattice by its constructed integral symplectic basis. The source
mirror states no license; attribution is preserved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Matrix Module
open scoped BigOperators ComplexConjugate Pointwise

namespace RHLean.Geometry.NativeTheta.Cusp.NativeVacuum

open NativeIntegralSymplectic NativeGeometricSymplectic AppellHumbert

section Coordinates

variable {M κ ι : Type} [AddCommGroup M] [Module ℤ M]
  [Fintype κ] [Fintype ι]

/-- Rational coordinates of rows in the same integral lattice. -/
def coordinates (b : Basis (ι ⊕ ι) ℤ M) :
    (κ → M) →+ (Matrix κ ι ℚ × Matrix κ ι ℚ) where
  toFun x := (fun k i => (b.repr (x k) (Sum.inl i) : ℚ),
    fun k i => (b.repr (x k) (Sum.inr i) : ℚ))
  map_zero' := by simp
  map_add' x y := by
    apply Prod.ext <;> funext k i <;> simp

omit [Fintype κ] [Fintype ι] in
theorem coordinates_injective (b : Basis (ι ⊕ ι) ℤ M) :
    Function.Injective (coordinates (κ := κ) b) := by
  intro x y h
  funext k
  apply b.repr.injective
  ext i
  cases i with
  | inl i =>
    exact_mod_cast congrFun (congrFun (congrArg Prod.fst h) k) i
  | inr i =>
    exact_mod_cast congrFun (congrFun (congrArg Prod.snd h) k) i

omit [Fintype κ] in
theorem mem_coordinates_range (b : Basis (ι ⊕ ι) ℤ M)
    (p : Matrix κ ι ℚ × Matrix κ ι ℚ) :
    p ∈ (coordinates (κ := κ) b).range ↔ IntM p.1 ∧ IntM p.2 := by
  classical
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun _ _ => isIntegral_algebraMap, fun _ _ => isIntegral_algebraMap⟩
  · rintro ⟨h1, h2⟩
    have he (x : ℚ) (hx : IsIntegral ℤ x) : ∃ z : ℤ, (z : ℚ) = x := by
      obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hx
      exact ⟨z, by simpa using hz⟩
    choose a ha using fun k i => he (p.1 k i) (h1 k i)
    choose c hc using fun k i => he (p.2 k i) (h2 k i)
    let x : κ → M := fun k => b.equivFun.symm (Sum.elim (a k) (c k))
    have hx (k) : (fun i => b.repr (x k) i) = Sum.elim (a k) (c k) :=
      b.equivFun.apply_symm_apply _
    refine ⟨x, Prod.ext (funext fun k => funext fun i => ?_)
      (funext fun k => funext fun i => ?_)⟩
    · change (b.repr (x k) (Sum.inl i) : ℚ) = p.1 k i
      rw [congrFun (hx k) (Sum.inl i)]
      exact ha k i
    · change (b.repr (x k) (Sum.inr i) : ℚ) = p.2 k i
      rw [congrFun (hx k) (Sum.inr i)]
      exact hc k i

/-- Exact self-duality of the rational image of the same integral lattice. -/
theorem coordinates_selfDual (b : Basis (ι ⊕ ι) ℤ M)
    (p : Matrix κ ι ℚ × Matrix κ ι ℚ) :
    p ∈ (coordinates (κ := κ) b).range ↔
      ∀ p' ∈ (coordinates (κ := κ) b).range,
        ∃ m : ℤ, (∑ k, (p.1 k ⬝ᵥ p'.2 k - p'.1 k ⬝ᵥ p.2 k) : ℚ) = m := by
  classical
  rw [mem_coordinates_range]
  constructor
  · rintro ⟨h1, h2⟩ p' hp'
    obtain ⟨h1', h2'⟩ := (mem_coordinates_range b p').1 hp'
    obtain ⟨m, hm⟩ := Vac.pr_int h1 h2'
    obtain ⟨m', hm'⟩ := Vac.pr_int h1' h2
    exact ⟨m - m', by rw [Vac.om_eq, hm, hm']; push_cast; rfl⟩
  · intro h
    constructor
    · intro k i
      have hp' : ((0 : Matrix κ ι ℚ), Matrix.single k i 1) ∈
          (coordinates (κ := κ) b).range := by
        apply (mem_coordinates_range b _).2
        constructor
        · intro a c; simp [IntM]
        · intro a c
          by_cases ha : a = k <;> by_cases hc : c = i <;>
            simp [Matrix.single, Pi.single_apply, ha, hc]
      obtain ⟨m, hm⟩ := h _ hp'
      have hm' : p.1 k i = m := by
        simpa [Vac.om_eq, Vac.pr, dotProduct, Matrix.single, Pi.single_apply] using hm
      rw [hm']
      exact isIntegral_algebraMap
    · intro k i
      have hp' : (Matrix.single k i 1, (0 : Matrix κ ι ℚ)) ∈
          (coordinates (κ := κ) b).range := by
        apply (mem_coordinates_range b _).2
        constructor
        · intro a c
          by_cases ha : a = k <;> by_cases hc : c = i <;>
            simp [Matrix.single, Pi.single_apply, ha, hc]
        · intro a c; simp [IntM]
      obtain ⟨m, hm⟩ := h _ hp'
      have hm' : -p.2 k i = m := by
        simpa [Vac.om_eq, Vac.pr, dotProduct, Matrix.single, Pi.single_apply] using hm
      have he : p.2 k i = (-m : ℤ) := by push_cast; linarith
      rw [he]
      exact isIntegral_algebraMap

/-- The exact alternating pairing in these integral coordinates. -/
theorem form_coordinates {B : LinearMap.BilinForm ℤ M} (hB : B.IsAlt)
    (b : Basis (ι ⊕ ι) ℤ M) (hb : IsSymplecticBasis B b) (x y : M) :
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

theorem coordinates_pairing {B : LinearMap.BilinForm ℤ M} (hB : B.IsAlt)
    (b : Basis (ι ⊕ ι) ℤ M) (hb : IsSymplecticBasis B b) (x y : κ → M) :
    (∑ k, ((coordinates b x).1 k ⬝ᵥ (coordinates b y).2 k -
      (coordinates b y).1 k ⬝ᵥ (coordinates b x).2 k) : ℚ) =
        ((∑ k, B (x k) (y k) : ℤ) : ℚ) := by
  simp only [Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [form_coordinates hB b hb]
  simp only [coordinates, AddMonoidHom.coe_mk, AddHom.coe_mk, dotProduct,
    Int.cast_sum, Int.cast_sub, Int.cast_mul, Finset.sum_sub_distrib]

end Coordinates

section Native

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {H : NativeGeometricHost E} (D : NativeGeometricDatum H)
  {κ ι : Type} [Fintype κ] [Fintype ι]

/-- The canonical half-root phase transported through actual integral
coordinates. Values outside the integral image have no role. -/
def nativePhase (b : Basis (ι ⊕ ι) ℤ D.La)
    (p : Matrix κ ι ℚ × Matrix κ ι ℚ) : ℂ :=
  ∏ k, phase D ((Function.invFun (coordinates (κ := κ) b)) p k)

omit [Fintype ι] in
@[simp] theorem nativePhase_coordinates (b : Basis (ι ⊕ ι) ℤ D.La) (x : κ → D.La) :
    nativePhase D b (coordinates b x) = ∏ k, phase D (x k) := by
  simp only [nativePhase, Function.leftInverse_invFun (coordinates_injective b)]

/-- Construct the normalized rational vacuum on the original native lattice.
The finite-adelic Haar norm is exactly one. -/
theorem exists_native_vacuum (n : ℕ) :
    let g := Module.finrank ℚ E / 2 * (D.p + D.q)
    ∃ b : Basis (Fin g ⊕ Fin g) ℤ D.La, IsSymplecticBasis D.EF b ∧
      ∃ v : Matrix (Fin n) (Fin g) ℚ → ℂ,
        IsSB v ∧ ip v v = 1 ∧ v ≠ 0 ∧
        (∀ x : Fin n → D.La, (∏ k, phase D (x k)) •
          heisS (coordinates b x).1 (coordinates b x).2 v = v) ∧
        ∀ w : Matrix (Fin n) (Fin g) ℚ → ℂ, IsSB w →
          (∀ x : Fin n → D.La, (∏ k, phase D (x k)) •
            heisS (coordinates b x).1 (coordinates b x).2 w = w) →
          ∃ c : ℂ, w = c • v := by
  classical
  have := D.fin
  have := D.proj
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  haveI : Module.Free ℤ D.La := inferInstance
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank D.alt D.unimod
    (finrank_int_lattice D)
  let A := (coordinates (κ := Fin n) b).range
  let ε := nativePhase D (κ := Fin n) b
  haveI : AddGroup.FG (Fin n → D.La) := Module.Finite.iff_addGroup_fg.1 inferInstance
  have hfg : A.FG := (AddGroup.fg_iff_addSubgroup_fg _).1
    (AddGroup.fg_range (coordinates (κ := Fin n) b))
  have hn : ∀ p ∈ A, ‖ε p‖ = 1 := by
    rintro p ⟨x, rfl⟩
    simp [ε, nativePhase_coordinates, norm_prod]
  have hsemi : ∀ p ∈ A, ∀ p' ∈ A,
      ε (p + p') = ε p * ε p' * Complex.exp (Real.pi * Complex.I *
        ((∑ k, (p.1 k ⬝ᵥ p'.2 k - p'.1 k ⬝ᵥ p.2 k) : ℚ) : ℂ)) := by
    rintro p ⟨x, rfl⟩ p' ⟨y, rfl⟩
    rw [← map_add, coordinates_pairing D.alt b hb]
    simp only [ε, nativePhase_coordinates, Pi.add_apply, phase_add,
      Finset.prod_mul_distrib]
    congr 1
    push_cast
    rw [Finset.mul_sum, ← Complex.exp_sum]
  have hord : ∀ p ∈ A, ε (2 • p) = 1 := by
    rintro p ⟨x, rfl⟩
    rw [← map_nsmul]
    simp only [ε, nativePhase_coordinates, Pi.nsmul_apply]
    have he (k : Fin n) : phase D (2 • x k) = 1 := by
      simpa only [two_nsmul, two_zsmul] using phase_two_smul D (x k)
    simp only [he, Finset.prod_const_one]
  obtain ⟨v, hv, hip, hfix, huniq⟩ := Vac.vacuum (Fin n) _ A ε hfg
    (coordinates_selfDual b) hn hsemi ⟨2, two_pos, hord⟩
  have hv0 : v ≠ 0 := by
    intro h0
    have h := hip
    simp [h0, ip, haar, haarAt, isSB_zero] at h
  refine ⟨b, hb, v, hv, hip, hv0, fun x => ?_, fun w hw hfw => ?_⟩
  · simpa only [ε, nativePhase_coordinates] using hfix _ ⟨x, rfl⟩
  · apply huniq w hw
    rintro p ⟨x, rfl⟩
    simpa only [ε, nativePhase_coordinates] using hfw x

end Native

end RHLean.Geometry.NativeTheta.Cusp.NativeVacuum

end
