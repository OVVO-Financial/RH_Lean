import RHLean.Geometry.NativeCMIdealClassModels
import RHLean.Geometry.NativeCMWeierstrassTangentCoordinatePeriods
import RHLean.Geometry.NativeCMWeierstrassRationalGlobal

/-!
# Integral models of the literal inverse-ideal periods

The analytic class mean uses the periods of the integral representatives b.
The arithmetic ideal-isogeny family uses b⁻¹. This file constructs those
inverse-ideal periods and actual discriminant-one models over one common
finite field, preserving the original principal seed and comparison. The
two period-inclusion directions are proved on the literal fractional ideals.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsCmCurvesOfWeierstrassCurves.lean.
The native construction uses the preceding actual equation constructor,
without an abstract polarized-variety supplier. The source archive states
no license; attribution is retained without assigning one. Integral
isogeny morphisms and their derivative integrality remain separate proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField PeriodPair Polynomial
open scoped Classical nonZeroDivisors

namespace RHLean.Geometry.NativeCM

theorem inverseIdeal_mem_iff {K : Type} [Field K] [NumberField K]
    (b : (Ideal (𝓞 K))⁰) (x : K) :
    x ∈ ((FractionalIdeal.mk0 K b)⁻¹).1 ↔
      ∀ y ∈ (b : Ideal (𝓞 K)), IsIntegral ℤ (x * (y : K)) := by
  have hn : ((FractionalIdeal.mk0 K b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := Units.ne_zero _
  rw [Units.val_inv_eq_inv_val, FractionalIdeal.mem_inv_iff hn, FractionalIdeal.coe_mk0]
  constructor
  · intro h y hy
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp
      (h _ ((FractionalIdeal.mem_coeIdeal _).mpr ⟨y, hy, rfl⟩))
    have hi : IsIntegral ℤ (algebraMap (𝓞 K) K a) := a.isIntegral_coe
    rwa [ha] at hi
  · intro h y hy
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨_, h a ha⟩, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)

theorem fractionalIdealPeriod_j_integral
    (I : (FractionalIdeal (𝓞 (quadraticField G))⁰ (quadraticField G))ˣ)
    (L : PeriodPair)
    (hL : (L.lattice : Set ℂ) = quadraticEmbedding G τ '' I.1) :
    IsIntegral ℤ (Weierstrass.latticeCurve L).j := by
  apply Weierstrass.latticeCurve_j_integral_of_order_stable
    (quadraticField_finrank G) (quadraticEmbedding G τ)
  intro a z hz
  change z ∈ (L.lattice : Set ℂ) at hz
  rw [hL] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  change _ ∈ (L.lattice : Set ℂ)
  rw [hL]
  refine ⟨(a : quadraticField G) * x, ?_, map_mul _ _ _⟩
  simpa only [Algebra.smul_def] using!
    Submodule.smul_mem (I.1 : Submodule (𝓞 (quadraticField G)) (quadraticField G)) a hx

/-- The arithmetic targets are models of the actual inverse ideals. The
original integral seed is retained at the principal index. -/
theorem exists_inverseIdealClassModels_preserving_seed
    (b : ClassGroup (𝓞 (quadraticField G)) → (Ideal (𝓞 (quadraticField G)))⁰)
    (hb₁ : b 1 = 1)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W₀ : _root_.WeierstrassCurve (𝓞 M)) (hΔ₀ : W₀.Δ = 1)
    (C₀ : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC₀ : C₀ • W₀.baseChange ℂ = Weierstrass.latticeCurve (EllipticSeed.periodPair G τ)) :
    ∃ (L : ClassGroup (𝓞 (quadraticField G)) → PeriodPair)
      (F : IntermediateField ℚ ℂ) (_ : NumberField F) (hMF : M ≤ F)
      (W : ClassGroup (𝓞 (quadraticField G)) → _root_.WeierstrassCurve (𝓞 F))
      (C : ClassGroup (𝓞 (quadraticField G)) → _root_.WeierstrassCurve.VariableChange ℂ),
      (∀ c, ((L c).lattice : Set ℂ) = quadraticEmbedding G τ ''
        ((FractionalIdeal.mk0 (quadraticField G) (b c))⁻¹).1) ∧
      L 1 = EllipticSeed.periodPair G τ ∧
      (∀ c, (W c).Δ = 1) ∧
      (∀ c, C c • (W c).baseChange ℂ = Weierstrass.latticeCurve (L c)) ∧
      W 1 = W₀.map (Weierstrass.integerFieldInclusion hMF) ∧ C 1 = C₀ := by
  have hp : ∀ c : ClassGroup (𝓞 (quadraticField G)), ∃ L : PeriodPair,
      (L.lattice : Set ℂ) = quadraticEmbedding G τ ''
        ((FractionalIdeal.mk0 (quadraticField G) (b c))⁻¹).1 ∧
      (c = 1 → L = EllipticSeed.periodPair G τ) := by
    intro c
    by_cases hc : c = 1
    · subst c
      exact ⟨EllipticSeed.periodPair G τ, by
        simpa only [hb₁, map_one, inv_one, Units.val_one] using! seedPeriod_eq_image_one G τ,
        fun _ => rfl⟩
    · obtain ⟨L, hL⟩ := PeriodArithmetic.QuadraticZeta.exists_periodPair
        (quadraticField_finrank G) (quadraticField_discr G) (quadraticEmbedding G τ)
        (FractionalIdeal.mk0 (quadraticField G) (b c))⁻¹
      exact ⟨L, hL, fun h => (hc h).elim⟩
  choose L hL hOne using hp
  have hL₁ := hOne 1 rfl
  have hcomp : C₀ • W₀.baseChange ℂ = Weierstrass.latticeCurve (L 1) := by
    rw [hL₁]
    exact hC₀
  obtain ⟨F, hF, hMF, W, C, hΔ, hC, hW₁, hC₁⟩ :=
    Weierstrass.exists_common_integral_models_preserving_seed 1 L M W₀ hΔ₀ C₀ hcomp
      (fun c => fractionalIdealPeriod_j_integral G τ _ _ (hL c))
  exact ⟨L, F, hF, hMF, W, C, hL, hL₁, hΔ, hC, hW₁, hC₁⟩

/-- The forward ideal inclusion on the actual unscaled periods. -/
theorem inverseIdealPeriod_forward
    (b : (Ideal (𝓞 (quadraticField G)))⁰) (L : PeriodPair)
    (hL : (L.lattice : Set ℂ) = quadraticEmbedding G τ ''
      ((FractionalIdeal.mk0 (quadraticField G) b)⁻¹).1)
    (x : quadraticField G)
    (hx : ∀ y ∈ (b : Ideal (𝓞 (quadraticField G))), IsIntegral ℤ (x * (y : quadraticField G)))
    (z : ℂ) (hz : z ∈ (EllipticSeed.periodPair G τ).lattice) :
    quadraticEmbedding G τ x * z ∈ L.lattice := by
  change z ∈ ((EllipticSeed.periodPair G τ).lattice : Set ℂ) at hz
  rw [seedPeriod_eq_image_one] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hy
  have hx' := (inverseIdeal_mem_iff b x).mpr hx
  change _ ∈ (L.lattice : Set ℂ)
  rw [hL]
  refine ⟨x * (a : quadraticField G), ?_, map_mul _ _ _⟩
  simpa only [Algebra.smul_def, mul_comm] using!
    Submodule.smul_mem (((FractionalIdeal.mk0 (quadraticField G) b)⁻¹).1 :
      Submodule (𝓞 (quadraticField G)) (quadraticField G)) a hx'

/-- The reverse inclusion uses the same ideal and the same lattice. -/
theorem inverseIdealPeriod_reverse
    (b : (Ideal (𝓞 (quadraticField G)))⁰) (L : PeriodPair)
    (hL : (L.lattice : Set ℂ) = quadraticEmbedding G τ ''
      ((FractionalIdeal.mk0 (quadraticField G) b)⁻¹).1)
    (a : 𝓞 (quadraticField G)) (ha : a ∈ (b : Ideal (𝓞 (quadraticField G))))
    (z : ℂ) (hz : z ∈ L.lattice) :
    quadraticEmbedding G τ (a : quadraticField G) * z ∈ (EllipticSeed.periodPair G τ).lattice := by
  change z ∈ (L.lattice : Set ℂ) at hz
  rw [hL] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hi := (inverseIdeal_mem_iff b x).mp hx a ha
  change _ ∈ ((EllipticSeed.periodPair G τ).lattice : Set ℂ)
  rw [seedPeriod_eq_image_one]
  refine ⟨x * (a : quadraticField G), (FractionalIdeal.mem_one_iff _).mpr ⟨⟨_, hi⟩, rfl⟩, ?_⟩
  rw [map_mul, mul_comm]


/-- Apply the original two ideal inclusions in the integral tangent coordinates
of the same two comparisons. The homothety is forced, not chosen afresh.
This is the native lattice part of the pinned
`exists_cm_curves_of_weierstrass_curves` proof, with the original seed retained. -/
theorem inverseIdealPeriod_normalized_maps
    (b : (Ideal (𝓞 (quadraticField G)))⁰) (L : PeriodPair)
    (hL : (L.lattice : Set ℂ) = quadraticEmbedding G τ ''
      ((FractionalIdeal.mk0 (quadraticField G) b)⁻¹).1)
    (C₀ C : _root_.WeierstrassCurve.VariableChange ℂ) :
    let β := (C₀.u : ℂ) / (C.u : ℂ)
    β ≠ 0 ∧
    (∀ (x : quadraticField G),
      (∀ y ∈ (b : Ideal (𝓞 (quadraticField G))),
        IsIntegral ℤ (x * (y : quadraticField G))) →
      ∀ z ∈ (Weierstrass.tangentCoordinatePeriods (EllipticSeed.periodPair G τ) C₀).lattice,
        β * quadraticEmbedding G τ x * z ∈
          (Weierstrass.tangentCoordinatePeriods L C).lattice) ∧
    (∀ a ∈ (b : Ideal (𝓞 (quadraticField G))),
      ∀ z ∈ (Weierstrass.tangentCoordinatePeriods L C).lattice,
        β⁻¹ * quadraticEmbedding G τ (a : quadraticField G) * z ∈
          (Weierstrass.tangentCoordinatePeriods (EllipticSeed.periodPair G τ) C₀).lattice) := by
  dsimp only
  refine ⟨div_ne_zero C₀.u.ne_zero C.u.ne_zero, ?_, ?_⟩
  · intro x hx z hz
    apply (Weierstrass.tangentCoordinatePeriods_mem L C _).2
    have h := inverseIdealPeriod_forward G τ b L hL x hx ((C₀.u : ℂ) * z)
      ((Weierstrass.tangentCoordinatePeriods_mem
        (EllipticSeed.periodPair G τ) C₀ z).1 hz)
    have he : (C.u : ℂ) * ((C₀.u : ℂ) / (C.u : ℂ) *
        quadraticEmbedding G τ x * z) =
        quadraticEmbedding G τ x * ((C₀.u : ℂ) * z) := by
      field_simp [C.u.ne_zero] <;> ring
    rwa [he]
  · intro a ha z hz
    apply (Weierstrass.tangentCoordinatePeriods_mem
      (EllipticSeed.periodPair G τ) C₀ _).2
    have h := inverseIdealPeriod_reverse G τ b L hL a ha ((C.u : ℂ) * z)
      ((Weierstrass.tangentCoordinatePeriods_mem L C z).1 hz)
    have he : (C₀.u : ℂ) * (((C₀.u : ℂ) / (C.u : ℂ))⁻¹ *
        quadraticEmbedding G τ (a : quadraticField G) * z) =
        quadraticEmbedding G τ (a : quadraticField G) * ((C.u : ℂ) * z) := by
      rw [inv_div]
      field_simp [C₀.u.ne_zero] <;> ring
    rwa [he]

/-- Instantiate the two normalized inclusions on the actual constructed
class family over one common field, keeping the original seed and comparison.
This is at the distinguished complex embedding; algebraicity, transport to
all embeddings and reverse derivative integrality are separate obligations. -/
theorem exists_inverseIdealTangentClassModels_preserving_seed
    (b : ClassGroup (𝓞 (quadraticField G)) → (Ideal (𝓞 (quadraticField G)))⁰)
    (hb₁ : b 1 = 1)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W₀ : _root_.WeierstrassCurve (𝓞 M)) (hΔ₀ : W₀.Δ = 1)
    (C₀ : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC₀ : C₀ • W₀.baseChange ℂ = Weierstrass.latticeCurve (EllipticSeed.periodPair G τ)) :
    ∃ (L : ClassGroup (𝓞 (quadraticField G)) → PeriodPair)
      (F : IntermediateField ℚ ℂ) (_ : NumberField F) (hMF : M ≤ F)
      (W : ClassGroup (𝓞 (quadraticField G)) → _root_.WeierstrassCurve (𝓞 F))
      (C : ClassGroup (𝓞 (quadraticField G)) → _root_.WeierstrassCurve.VariableChange ℂ),
      (∀ c, ((L c).lattice : Set ℂ) = quadraticEmbedding G τ ''
        ((FractionalIdeal.mk0 (quadraticField G) (b c))⁻¹).1) ∧
      L 1 = EllipticSeed.periodPair G τ ∧
      (∀ c, (W c).Δ = 1) ∧
      (∀ c, C c • (W c).baseChange ℂ = Weierstrass.latticeCurve (L c)) ∧
      W 1 = W₀.map (Weierstrass.integerFieldInclusion hMF) ∧ C 1 = C₀ ∧
      (∀ c, let β := (C₀.u : ℂ) / ((C c).u : ℂ)
        β ≠ 0 ∧
        (∀ (x : quadraticField G),
          (∀ y ∈ (b c : Ideal (𝓞 (quadraticField G))),
            IsIntegral ℤ (x * (y : quadraticField G))) →
          ∀ z ∈ (Weierstrass.tangentCoordinatePeriods (EllipticSeed.periodPair G τ) C₀).lattice,
            β * quadraticEmbedding G τ x * z ∈
              (Weierstrass.tangentCoordinatePeriods (L c) (C c)).lattice) ∧
        (∀ a ∈ (b c : Ideal (𝓞 (quadraticField G))),
          ∀ z ∈ (Weierstrass.tangentCoordinatePeriods (L c) (C c)).lattice,
            β⁻¹ * quadraticEmbedding G τ (a : quadraticField G) * z ∈
              (Weierstrass.tangentCoordinatePeriods (EllipticSeed.periodPair G τ) C₀).lattice)) := by
  obtain ⟨L, F, hF, hMF, W, C, hL, hL₁, hΔ, hC, hW₁, hC₁⟩ :=
    exists_inverseIdealClassModels_preserving_seed G τ b hb₁ M W₀ hΔ₀ C₀ hC₀
  exact ⟨L, F, hF, hMF, W, C, hL, hL₁, hΔ, hC, hW₁, hC₁,
    fun c => inverseIdealPeriod_normalized_maps G τ (b c) (L c) (hL c) C₀ (C c)⟩


/-- Apply the existing finite-field rational-isogeny supplier to the
actual reverse map of one inverse-ideal class model. The multiplier is
the previously proved normalized ratio times the nonzero ideal element.
The finite extension contains the original equations. The rational
formula and its kernel degree are those of this literal lattice map,
not a chosen map with a stipulated tangent value. -/
theorem exists_inverseIdeal_reverse_rational_isogeny
    (b : (Ideal (𝓞 (quadraticField G)))⁰) (L : PeriodPair)
    (hL : (L.lattice : Set ℂ) = quadraticEmbedding G τ ''
      ((FractionalIdeal.mk0 (quadraticField G) b)⁻¹).1)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W₀ W : _root_.WeierstrassCurve (𝓞 M))
    (C₀ C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC₀ : C₀ • W₀.baseChange ℂ = Weierstrass.latticeCurve (EllipticSeed.periodPair G τ))
    (hC : C • W.baseChange ℂ = Weierstrass.latticeCurve L)
    (a : 𝓞 (quadraticField G)) (ha : a ∈ (b : Ideal (𝓞 (quadraticField G)))) (ha0 : a ≠ 0) :
    let Ls := Weierstrass.tangentCoordinatePeriods L C
    let Lt := Weierstrass.tangentCoordinatePeriods (EllipticSeed.periodPair G τ) C₀
    let α := ((C₀.u : ℂ) / (C.u : ℂ))⁻¹ * quadraticEmbedding G τ (a : quadraticField G)
    ∃ (hα : ∀ l ∈ Ls.lattice, α * l ∈ Lt.lattice)
      (F : IntermediateField ℚ ℂ) (_ : NumberField F) (A D : ℂ[X]),
      M ≤ F ∧ α ∈ F ∧
      (∀ i, A.coeff i ∈ F) ∧ (∀ i, D.coeff i ∈ F) ∧ D.Monic ∧
      A.leadingCoeff = (α ^ 2)⁻¹ ∧ IsCoprime A D ∧
      A.natDegree = Nat.card (Weierstrass.latticeIsogeny α hα).ker ∧
      A.natDegree =
        ((Weierstrass.phiPeriodLattice Ls).map (RHLean.Analysis.complexRealPairMulHom α)).relIndex
          (Weierstrass.phiPeriodLattice Lt) ∧
      D.natDegree + 1 = A.natDegree ∧
      (∀ (x y : ℂ) (h : (Weierstrass.latticeCurve Ls).toAffine.Nonsingular x y),
        (D.eval x = 0 → Weierstrass.latticeIsogeny α hα (.some x y h) = 0) ∧
        (D.eval x ≠ 0 → ∃ h', Weierstrass.latticeIsogeny α hα (.some x y h) =
          .some (A.eval x / D.eval x)
            (α⁻¹ * ((Polynomial.derivative A * D - A * Polynomial.derivative D).eval x /
              D.eval x ^ 2) * y) h')) := by
  dsimp only
  let Ls := Weierstrass.tangentCoordinatePeriods L C
  let Lt := Weierstrass.tangentCoordinatePeriods (EllipticSeed.periodPair G τ) C₀
  let α := ((C₀.u : ℂ) / (C.u : ℂ))⁻¹ * quadraticEmbedding G τ (a : quadraticField G)
  have hα : ∀ l ∈ Ls.lattice, α * l ∈ Lt.lattice :=
    (inverseIdealPeriod_normalized_maps G τ b L hL C₀ C).2.2 a ha
  have haK : (a : quadraticField G) ≠ 0 := by exact_mod_cast ha0
  have hα0 : α ≠ 0 := mul_ne_zero
    (inv_ne_zero (div_ne_zero C₀.u.ne_zero C.u.ne_zero)) ((map_ne_zero _).2 haK)
  have h₂ (V : _root_.WeierstrassCurve (𝓞 M)) (P : PeriodPair)
      (B : _root_.WeierstrassCurve.VariableChange ℂ)
      (hB : B • V.baseChange ℂ = Weierstrass.latticeCurve P) :
      (Weierstrass.tangentCoordinatePeriods P B).g₂ ∈ M := by
    rw [Weierstrass.tangentCoordinatePeriods_g₂_eq_invariant P B (V.baseChange ℂ) hB,
      _root_.WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_c₄]
    change (((V.c₄ : M) : ℂ) / 12) ∈ M
    exact div_mem (V.c₄ : M).property (ofNat_mem M 12)
  have h₃ (V : _root_.WeierstrassCurve (𝓞 M)) (P : PeriodPair)
      (B : _root_.WeierstrassCurve.VariableChange ℂ)
      (hB : B • V.baseChange ℂ = Weierstrass.latticeCurve P) :
      (Weierstrass.tangentCoordinatePeriods P B).g₃ ∈ M := by
    rw [Weierstrass.tangentCoordinatePeriods_g₃_eq_invariant P B (V.baseChange ℂ) hB,
      _root_.WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_c₆]
    change (((V.c₆ : M) : ℂ) / 216) ∈ M
    exact div_mem (V.c₆ : M).property (ofNat_mem M 216)
  obtain ⟨F, hF, A, D, hMF, hαF, hA, hD, hm, hlc, hc, hdA, hdD, he⟩ :=
    Weierstrass.TorsionAlgebraicity.exists_finite_field_rational_latticeIsogeny
      M hα0 hα (h₂ W L C hC) (h₃ W L C hC)
      (h₂ W₀ (EllipticSeed.periodPair G τ) C₀ hC₀)
      (h₃ W₀ (EllipticSeed.periodPair G τ) C₀ hC₀)
  exact ⟨hα, F, hF, A, D, hMF, hαF, hA, hD, hm, hlc, hc, hdA,
    hdA.trans (Weierstrass.card_ker_latticeIsogeny_phi hα0 hα), hdD, he⟩

section ReverseSchemeIsogeny

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SchemeTheory SchemeTheory.WeierstrassCurve
attribute [local instance] Over.cartesianMonoidalCategory

/-- The actual reverse ideal-class multiplier and the two original integral
models supply a generic morphism by the existing rational-map proof. -/
theorem exists_inverseIdeal_reverse_scheme_isogeny
    (b : (Ideal (𝓞 (quadraticField G)))⁰) (L : PeriodPair)
    (hL : (L.lattice : Set ℂ) = quadraticEmbedding G τ ''
      ((FractionalIdeal.mk0 (quadraticField G) b)⁻¹).1)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W₀ W : _root_.WeierstrassCurve (𝓞 M)) [W₀.IsElliptic] [W.IsElliptic]
    (C₀ C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC₀ : C₀ • W₀.baseChange ℂ = Weierstrass.latticeCurve (EllipticSeed.periodPair G τ))
    (hC : C • W.baseChange ℂ = Weierstrass.latticeCurve L)
    (a : 𝓞 (quadraticField G)) (ha : a ∈ (b : Ideal (𝓞 (quadraticField G)))) (ha0 : a ≠ 0) :
    let Ls := Weierstrass.tangentCoordinatePeriods L C
    let Lt := Weierstrass.tangentCoordinatePeriods (EllipticSeed.periodPair G τ) C₀
    let α := ((C₀.u : ℂ) / (C.u : ℂ))⁻¹ * quadraticEmbedding G τ (a : quadraticField G)
    ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K) (hMK : M ≤ K)
      (Vs Vt : _root_.WeierstrassCurve K) (_ : Vs.IsElliptic) (_ : Vt.IsElliptic)
      (hs : Vs.baseChange ℂ = Weierstrass.latticeCurve Ls)
      (ht : Vt.baseChange ℂ = Weierstrass.latticeCurve Lt)
      (f : schemeOver Vs ⟶ schemeOver Vt),
      Vs = Weierstrass.shortModel ((W.baseChange M).map (IntermediateField.inclusion hMK).toRingHom) ∧
      Vt = Weierstrass.shortModel ((W₀.baseChange M).map (IntermediateField.inclusion hMK).toRingHom) ∧
      IsMonHom f ∧ ∀ z : ℂ,
        ofAffinePoint Vs ℂ ((Weierstrass.pointCongr hs).symm (Weierstrass.latticePoint Ls z)) ≫ f =
          ofAffinePoint Vt ℂ ((Weierstrass.pointCongr ht).symm (Weierstrass.latticePoint Lt (α * z))) := by
  dsimp only
  let Ls := Weierstrass.tangentCoordinatePeriods L C
  let Lt := Weierstrass.tangentCoordinatePeriods (EllipticSeed.periodPair G τ) C₀
  let α := ((C₀.u : ℂ) / (C.u : ℂ))⁻¹ * quadraticEmbedding G τ (a : quadraticField G)
  obtain ⟨hα, F, hF, A, D, hMF, hαF, hAF, hDF, hm, _, _, _, _, _, hformula⟩ :=
    exists_inverseIdeal_reverse_rational_isogeny G τ b L hL M W₀ W C₀ C hC₀ hC a ha ha0
  let _ : NumberField F := hF
  let Ws := Weierstrass.shortModel ((W.baseChange M).map (IntermediateField.inclusion hMF).toRingHom)
  let Wt := Weierstrass.shortModel ((W₀.baseChange M).map (IntermediateField.inclusion hMF).toRingHom)
  haveI : Ws.IsElliptic := by
    dsimp [Ws]
    rw [← Weierstrass.shortChange_spec]
    infer_instance
  haveI : Wt.IsElliptic := by
    dsimp [Wt]
    rw [← Weierstrass.shortChange_spec]
    infer_instance
  have hs : Ws.baseChange ℂ = Weierstrass.latticeCurve Ls := by
    change Ws.map (F.val : F →+* ℂ) = _
    dsimp [Ws]
    rw [Weierstrass.shortModel_map, _root_.WeierstrassCurve.map_map]
    change Weierstrass.shortModel (W.baseChange ℂ) = _
    exact Weierstrass.shortModel_eq_tangentCoordinate_latticeCurve L C (W.baseChange ℂ) hC
  have ht : Wt.baseChange ℂ = Weierstrass.latticeCurve Lt := by
    change Wt.map (F.val : F →+* ℂ) = _
    dsimp [Wt]
    rw [Weierstrass.shortModel_map, _root_.WeierstrassCurve.map_map]
    change Weierstrass.shortModel (W₀.baseChange ℂ) = _
    exact Weierstrass.shortModel_eq_tangentCoordinate_latticeCurve
      (EllipticSeed.periodPair G τ) C₀ (W₀.baseChange ℂ) hC₀
  have haK : (a : quadraticField G) ≠ 0 := by exact_mod_cast ha0
  have hα0 : α ≠ 0 := mul_ne_zero
    (inv_ne_zero (div_ne_zero C₀.u.ne_zero C.u.ne_zero)) ((map_ne_zero _).2 haK)
  obtain ⟨K, hK, hFK, hKs, hKt, f, hf, hpoint⟩ :=
    Weierstrass.exists_scheme_latticeIsogeny F Ws Wt Ls Lt hs ht
      ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ α hα0 hα hαF A D hAF hDF hm.ne_zero hformula
  let _ : NumberField K := hK
  let i := IntermediateField.inclusion hFK
  let Vs := Ws.map i.toRingHom
  let Vt := Wt.map i.toRingHom
  refine ⟨K, hK, hMF.trans hFK, Vs, Vt, inferInstance, inferInstance,
    hKs, hKt, f, ?_, ?_, hf, hpoint⟩
  · change Ws.map i.toRingHom = _
    rw [Ws, Weierstrass.shortModel_map, _root_.WeierstrassCurve.map_map]
    rfl
  · change Wt.map i.toRingHom = _
    rw [Wt, Weierstrass.shortModel_map, _root_.WeierstrassCurve.map_map]
    rfl

end ReverseSchemeIsogeny

end RHLean.Geometry.NativeCM
