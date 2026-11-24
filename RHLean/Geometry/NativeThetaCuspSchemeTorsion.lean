import RHLean.Geometry.NativeCMSerreGenericModel
import RHLean.Geometry.NativeThetaCuspQuotientAdjoint

/-!
# The half-level on actual generic Serre scheme points

The scheme exponential already constructed on the literal projective
coefficient module identifies multiplication torsion with the quotient of
the original integral period lattice. The same separator `cHalf` used in
the finite Fourier transform then identifies the complementary ideal
quotients with actual ideal-annihilated scheme points. The point attached
to a lattice class is the exponential of its original period divided by
the rational level, with precisely this separator.

The elementary quotient proof is native. The geometric target and
normalization follow the level-period identification used in Levent
Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/LevelPointsOfArcEqPeriodDivLevel.lean,
and the separator is the literal one in
src/Formalism/LocalToGlobal/ProjectiveLattices/ThShort.lean.
The source mirror states no license; attribution is retained.

This constructs the level marking on the represented CM fibre. The
scheme representing all marked objects over varying periods, its
connected components and a global character eigensection are later
geometric constructions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical Pointwise

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeTheta.Cusp.SchemeTorsion

section Division

variable {R M V A : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup A] [Module R A]

/-- The literal kernel of an ideal acting on the given point module. -/
def idealTorsion (I : Ideal R) : Submodule R A where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := fun _ _ => smul_zero _
  add_mem' hx hy a ha := by rw [smul_add, hx a ha, hy a ha, add_zero]
  smul_mem' c x hx a ha := by rw [smul_comm a c, hx a ha, smul_zero]

theorem mem_natIdeal_smul (N : ℕ) (x : M) :
    x ∈ (Ideal.span {(N : R)} • ⊤ : Submodule R M) ↔ ∃ y : M, N • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]

private theorem nsmul_inv (N : ℕ) (hN : N ≠ 0) (v : V) :
    N • ((N : ℝ)⁻¹ • v) = v := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN), one_smul]

private theorem inv_nsmul (N : ℕ) (hN : N ≠ 0) (v : V) :
    (N : ℝ)⁻¹ • (N • v) = v := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN), one_smul]

/-- Division occurs in the original analytic ambient space, followed by
the actual exponential into scheme points. -/
def divisionMap (P : M →+ V) (ex : V →+ A) (N : ℕ) : M →+ A where
  toFun x := ex ((N : ℝ)⁻¹ • P x)
  map_zero' := by rw [map_zero, smul_zero, map_zero]
  map_add' x y := by rw [map_add, smul_add, map_add]

theorem divisionMap_zero_iff (P : M →+ V) (hP : Function.Injective P)
    (ex : V →+ A) (hker : ∀ v, ex v = 0 ↔ v ∈ P.range)
    (N : ℕ) (hN : N ≠ 0) (x : M) :
    divisionMap P ex N x = 0 ↔ ∃ y : M, N • y = x := by
  change ex ((N : ℝ)⁻¹ • P x) = 0 ↔ _
  rw [hker]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, hP ?_⟩
    rw [map_nsmul, hy, nsmul_inv N hN]
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [map_nsmul, inv_nsmul N hN]⟩

theorem divisionMap_nsmul (P : M →+ V) (ex : V →+ A)
    (hker : ∀ v, ex v = 0 ↔ v ∈ P.range)
    (N : ℕ) (hN : N ≠ 0) (x : M) :
    N • divisionMap P ex N x = 0 := by
  change N • ex ((N : ℝ)⁻¹ • P x) = 0
  rw [← map_nsmul, nsmul_inv N hN]
  exact (hker (P x)).2 ⟨x, rfl⟩

theorem divisionMap_surjective_torsion (P : M →+ V) (ex : V →+ A)
    (hsurj : Function.Surjective ex) (hker : ∀ v, ex v = 0 ↔ v ∈ P.range)
    (N : ℕ) (hN : N ≠ 0) (y : A) (hy : N • y = 0) :
    ∃ x : M, divisionMap P ex N x = y := by
  obtain ⟨v, rfl⟩ := hsurj y
  obtain ⟨x, hx⟩ := (hker (N • v)).1 (by rw [map_nsmul, hy])
  refine ⟨x, ?_⟩
  change ex ((N : ℝ)⁻¹ • P x) = ex v
  rw [hx, inv_nsmul N hN]

end Division

section Half

variable {R M A : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup A] [Module R A]

/-- Multiplication by the separator gives the exact ideal-torsion
quotient. Neither an integral free basis nor flatness is needed. -/
theorem exists_half_quotient_equiv
    (N : ℕ) (I J : Ideal R) (hIJ : I * J = Ideal.span {(N : R)})
    (c : R) (hc : c ∈ J) (hc1 : c - 1 ∈ I)
    (f : M →ₗ[R] A)
    (hzero : ∀ x, f x = 0 ↔ x ∈ (Ideal.span {(N : R)} • ⊤ : Submodule R M))
    (hfull : ∀ y : A, N • y = 0 → ∃ x, f x = y) :
    ∃ e : (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R] idealTorsion (A := A) I,
      ∀ x, (e (Submodule.Quotient.mk x) : A) = f (c • x) := by
  have hNI : (N : R) ∈ I :=
    (show Ideal.span {(N : R)} ≤ I from hIJ ▸ Ideal.mul_le_left)
      (Ideal.mem_span_singleton_self _)
  have hNI' : (Ideal.span {(N : R)} • (⊤ : Submodule R M)) ≤ I • ⊤ :=
    Submodule.smul_mono (hIJ ▸ Ideal.mul_le_left) le_rfl
  have hcx : ∀ x ∈ (I • ⊤ : Submodule R M), c • x ∈
      (Ideal.span {(N : R)} • ⊤ : Submodule R M) := by
    intro x hx
    rw [← hIJ, mul_comm I J, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hc hx
  let g : M →ₗ[R] idealTorsion (A := A) I :=
    { toFun := fun x => ⟨f (c • x), fun a ha => by
        rw [← map_smul, ← mul_smul]
        apply (hzero _).2
        exact Submodule.smul_mem_smul (hIJ ▸ Ideal.mul_mem_mul ha hc)
          (Submodule.mem_top : x ∈ (⊤ : Submodule R M))⟩
      map_add' := fun x y => Subtype.ext (by
        change f (c • (x + y)) = f (c • x) + f (c • y)
        rw [smul_add, map_add])
      map_smul' := fun a x => Subtype.ext (by
        change f (c • (a • x)) = a • f (c • x)
        rw [smul_comm c a, map_smul]) }
  have hg : ∀ x, (g x : A) = f (c • x) := fun _ => rfl
  have hker : (I • ⊤ : Submodule R M) = g.ker := by
    ext x
    rw [LinearMap.mem_ker, ← Subtype.val_inj]
    change x ∈ (I • ⊤ : Submodule R M) ↔ f (c • x) = 0
    rw [hzero]
    constructor
    · exact hcx x
    · intro hx
      have hdiff : (c - 1) • x ∈ (I • ⊤ : Submodule R M) :=
        Submodule.smul_mem_smul hc1 (Submodule.mem_top : x ∈ (⊤ : Submodule R M))
      have he : x = c • x - (c - 1) • x := by rw [sub_smul, one_smul]; abel
      rw [he]
      exact sub_mem (hNI' hx) hdiff
  have hsurj : Function.Surjective g := by
    intro y
    have hyN : N • (y : A) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul R]
      exact y.2 N hNI
    obtain ⟨x, hx⟩ := hfull y hyN
    refine ⟨x, Subtype.ext ?_⟩
    rw [hg, map_smul, hx]
    have hyc := y.2 (c - 1) hc1
    rw [sub_smul, one_smul, sub_eq_zero] at hyc
    exact hyc
  refine ⟨(Submodule.quotEquivOfEq _ _ hker).trans (g.quotKerEquivOfSurjective hsurj), ?_⟩
  intro x
  rfl

end Half

end RHLean.Geometry.NativeTheta.Cusp.SchemeTorsion

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM EllipticSeed
open SerreScheme SchemeTheory SchemeTheory.WeierstrassCurve Weierstrass
open NativeTheta.Cusp.SchemeTorsion NativeTheta.Cusp.QuotientAdjoint

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E)
    (hbar : ∀ c : 𝓞 H.E, G.bar c = H.conj • c)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (τ₀ : cmTypeFinset H)
    {F : Type} [Field F] [Algebra F ℂ]
    (V : _root_.WeierstrassCurve F) [V.IsElliptic]
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G (τ₀ : H.E →+* ℂ) C))
    (a : OAct (OK G) (schemeOver V))
    (hact : ∀ c : OK G, ∀ z : ℂ,
      ofAffinePoint V ℂ ((pointCongr hVC).symm
        (latticePoint (rescaledPeriods G (τ₀ : H.E →+* ℂ) C) z)) ≫ a.act c =
      ofAffinePoint V ℂ ((pointCongr hVC).symm
        (latticePoint (rescaledPeriods G (τ₀ : H.E →+* ℂ) C)
          (embed G (τ₀ : H.E →+* ℂ) c * z))))
    [Algebra (OK G) ℂ]
    (hcompat : ∀ τ : cmTypeFinset H,
      embed G (τ : H.E →+* ℂ) = algebraMap (OK G) ℂ)

/-- The same exponential, with the actual full coefficient action on its
scheme-point target. The underlying additive points are unchanged. -/
def coefficientFullExponential :
    (cmTypeFinset H → Fin 1 → ℂ) →+
      Pts (coefficientSerreSchemeFullAction H G hbar B hB 1 a) (specOver F ℂ) :=
  (coefficientGenericPeriodExponential H G hbar B hB τ₀ V C hVC a hact hcompat).toAddMonoidHom

/-- The actual level point is exponential(period / N), expressed as an
O(E)-linear map from the original projective lattice. -/
def coefficientLevelPoint (N : ℕ) :
    twistedLattice H B 1 →ₗ[𝓞 H.E]
      Pts (coefficientSerreSchemeFullAction H G hbar B hB 1 a) (specOver F ℂ) where
  toFun x := coefficientFullExponential H G hbar B hB τ₀ V C hVC a hact hcompat
    ((N : ℝ)⁻¹ • purePeriodLinear H G hcompat B 1 x)
  map_add' x y := by rw [map_add, smul_add, map_add]
  map_smul' c x := by
    apply Pts.ext
    change Pts.hom (coefficientGenericPeriodExponential H G hbar B hB τ₀ V C hVC a hact hcompat
      ((N : ℝ)⁻¹ • purePeriodLinear H G hcompat B 1 (c • x))) = _
    rw [← rawCoefficientAction_period H G hcompat B 1 c x]
    have hs : (N : ℝ)⁻¹ • rawCoefficientAction H 1 c (purePeriodLinear H G hcompat B 1 x) =
        rawCoefficientAction H 1 c ((N : ℝ)⁻¹ • purePeriodLinear H G hcompat B 1 x) := by
      exact (((rawCoefficientAction H 1 c).restrictScalars ℝ).map_smul _ _).symm
    rw [hs]
    exact coefficientGenericPeriodExponential_coefficient H G hbar B hB τ₀ V C hVC a hact hcompat c _

/-- The level point in the normalized Weierstrass scheme retains the
nontrivial inverse change-of-variables factor from the exact period
comparison. It is not a point for a rescaled integral lattice. -/
theorem coefficientLevelPoint_scheme_formula (N : ℕ) (x : twistedLattice H B 1) :
    Pts.hom (coefficientLevelPoint H G hbar B hB τ₀ V C hVC a hact hcompat N x) =
      ofAffinePoint V ℂ ((pointCongr hVC).symm
        (latticePoint (rescaledPeriods G (τ₀ : H.E →+* ℂ) C)
          ((C.u : ℂ)⁻¹ * (N : ℂ)⁻¹))) ≫
            (coefficientSerreSchemeTensor H G hbar B hB 1 a).tmul (coefficientTwistedOne H B x) := by
  change Pts.hom (coefficientGenericPeriodExponential H G hbar B hB τ₀ V C hVC a hact hcompat
    ((N : ℝ)⁻¹ • purePeriodLinear H G hcompat B 1 x)) = _
  have hs : (N : ℝ)⁻¹ • purePeriodLinear H G hcompat B 1 x =
      (N : ℂ)⁻¹ • purePeriodLinear H G hcompat B 1 x := by
    ext τ i
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hs]
  exact coefficientGenericPeriodExponential_period_smul
    H G hbar B hB τ₀ V C hVC a hact hcompat (N : ℂ)⁻¹ x

theorem coefficientLevelPoint_zero_iff (N : ℕ) (hN : N ≠ 0) (x : twistedLattice H B 1) :
    coefficientLevelPoint H G hbar B hB τ₀ V C hVC a hact hcompat N x = 0 ↔
      x ∈ (Ideal.span {(N : 𝓞 H.E)} • ⊤ : Submodule (𝓞 H.E) (twistedLattice H B 1)) := by
  rw [mem_natIdeal_smul]
  apply divisionMap_zero_iff (purePeriodLinear H G hcompat B 1).toAddMonoidHom
    (fun x y h => Subtype.ext (funext fun i => (τ₀ : H.E →+* ℂ).injective
      (congrFun (congrFun h τ₀) i)))
    (coefficientFullExponential H G hbar B hB τ₀ V C hVC a hact hcompat)
    (fun v => coefficientGenericPeriodExponential_ker H G hbar B hB τ₀ V C hVC a hact hcompat v)
    N hN x

theorem coefficientLevelPoint_surjective_torsion (N : ℕ) (hN : N ≠ 0)
    (y : Pts (coefficientSerreSchemeFullAction H G hbar B hB 1 a) (specOver F ℂ))
    (hy : N • y = 0) :
    ∃ x : twistedLattice H B 1,
      coefficientLevelPoint H G hbar B hB τ₀ V C hVC a hact hcompat N x = y := by
  exact divisionMap_surjective_torsion (purePeriodLinear H G hcompat B 1).toAddMonoidHom
    (coefficientFullExponential H G hbar B hB τ₀ V C hVC a hact hcompat)
    (coefficientGenericPeriodExponential_surjective H G hbar B hB τ₀ V C hVC a hact hcompat)
    (fun v => coefficientGenericPeriodExponential_ker H G hbar B hB τ₀ V C hVC a hact hcompat v)
    N hN y hy

/-- The finite Fourier separator gives an exact equivalence with the
actual ideal-annihilated scheme points, including its literal formula. -/
theorem coefficient_half_quotient_equiv
    (N : ℕ) (hN : N ≠ 0) (I : Ideal (𝓞 H.E))
    (hI : IsCoprime I (I.map (G.bar : 𝓞 H.E →+* 𝓞 H.E)))
    (hprod : I * I.map (G.bar : 𝓞 H.E →+* 𝓞 H.E) = Ideal.span {(N : 𝓞 H.E)}) :
    ∃ e : (twistedLattice H B 1 ⧸ (I • ⊤ : Submodule (𝓞 H.E) (twistedLattice H B 1)))
      ≃ₗ[𝓞 H.E] idealTorsion
        (A := Pts (coefficientSerreSchemeFullAction H G hbar B hB 1 a) (specOver F ℂ)) I,
      ∀ x, (e (Submodule.Quotient.mk x) :
        Pts (coefficientSerreSchemeFullAction H G hbar B hB 1 a) (specOver F ℂ)) =
        coefficientLevelPoint H G hbar B hB τ₀ V C hVC a hact hcompat N (cHalf G I • x) := by
  obtain ⟨hc, hc1⟩ := cHalf_spec G I hI
  exact exists_half_quotient_equiv N I (I.map (G.bar : 𝓞 H.E →+* 𝓞 H.E)) hprod
    (cHalf G I) hc hc1
    (coefficientLevelPoint H G hbar B hB τ₀ V C hVC a hact hcompat N)
    (coefficientLevelPoint_zero_iff H G hbar B hB τ₀ V C hVC a hact hcompat N hN)
    (coefficientLevelPoint_surjective_torsion H G hbar B hB τ₀ V C hVC a hact hcompat N hN)

include hVC hact hcompat in
/-- The cardinal of actual half-torsion is the norm of the half ideal,
because the unchanged coefficient lattice has projective O(E)-rank one. -/
theorem coefficient_half_torsion_card
    (N : ℕ) (hN : N ≠ 0) (I : Ideal (𝓞 H.E)) (hI0 : I ≠ ⊥)
    (hI : IsCoprime I (I.map (G.bar : 𝓞 H.E →+* 𝓞 H.E)))
    (hprod : I * I.map (G.bar : 𝓞 H.E →+* 𝓞 H.E) = Ideal.span {(N : 𝓞 H.E)}) :
    Finite (idealTorsion
      (A := Pts (coefficientSerreSchemeFullAction H G hbar B hB 1 a) (specOver F ℂ)) I) ∧
      Nat.card (idealTorsion
        (A := Pts (coefficientSerreSchemeFullAction H G hbar B hB 1 a) (specOver F ℂ)) I) =
        Nat.card (𝓞 H.E ⧸ I) := by
  let := twistedLattice_finite H B 1
  let := twistedLattice_projective H B 1
  let : Finite (𝓞 H.E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  obtain ⟨basis⟩ := NativeThetaFullLevelCost.nonempty_equiv_mod (𝓞 H.E)
    (twistedLattice H B 1) I 1 (twistedLattice_rank H B hB 1)
  obtain ⟨lev, -⟩ := coefficient_half_quotient_equiv
    H G hbar B hB τ₀ V C hVC a hact hcompat N hN I hI hprod
  let eqv := lev.symm.trans basis
  refine ⟨Finite.of_equiv _ eqv.symm.toEquiv, ?_⟩
  rw [Nat.card_congr eqv.toEquiv, Nat.card_fun, Nat.card_fin, pow_one]

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization
open RHLean.Geometry RHLean.Geometry.NativeCM EllipticSeed
open SerreScheme SchemeTheory SchemeTheory.WeierstrassCurve Weierstrass
open NativeTheta.Cusp.SchemeTorsion NativeTheta.Cusp.QuotientAdjoint

/-- Construct the actual generic CM fibre and its split five-level at
once. The marking is on scheme points and uses the literal original
projective lattice and the original period divided by five. -/
theorem nativeDyadicHost_exists_genericHalfLevel
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    let hbar := nativeDyadicGeometricHost_bar_eq e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      ∀ τ₀ : cmTypeFinset H.toHostRaw,
        let _ : Algebra (OK G) ℂ := (embed G (τ₀ : H.E →+* ℂ)).toAlgebra
        ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F)
          (V : _root_.WeierstrassCurve F) (_ : V.IsElliptic)
          (C : _root_.WeierstrassCurve.VariableChange ℂ)
          (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G (τ₀ : H.E →+* ℂ) C))
          (a : OAct (OK G) (schemeOver V))
          (hact : ∀ c : OK G, ∀ z : ℂ,
            ofAffinePoint V ℂ ((pointCongr hVC).symm
              (latticePoint (rescaledPeriods G (τ₀ : H.E →+* ℂ) C) z)) ≫ a.act c =
            ofAffinePoint V ℂ ((pointCongr hVC).symm
              (latticePoint (rescaledPeriods G (τ₀ : H.E →+* ℂ) C)
                (embed G (τ₀ : H.E →+* ℂ) c * z))))
          (I : Ideal (𝓞 H.E)),
          I ≠ ⊤ ∧ I ≠ ⊥ ∧
          IsCoprime I (I.map (G.bar : 𝓞 H.E →+* 𝓞 H.E)) ∧
          I * I.map (G.bar : 𝓞 H.E →+* 𝓞 H.E) = Ideal.span {(5 : 𝓞 H.E)} ∧
          ∃ (hc : ∀ τ : cmTypeFinset H.toHostRaw,
            embed G (τ : H.E →+* ℂ) = algebraMap (OK G) ℂ)
            (lev : (twistedLattice H.toHostRaw B 1 ⧸
              (I • ⊤ : Submodule (𝓞 H.E) (twistedLattice H.toHostRaw B 1))) ≃ₗ[𝓞 H.E]
              idealTorsion (A := Pts
                (coefficientSerreSchemeFullAction H.toHostRaw G hbar B hB 1 a) (specOver F ℂ)) I),
            ∀ x, (lev (Submodule.Quotient.mk x) : Pts
              (coefficientSerreSchemeFullAction H.toHostRaw G hbar B hB 1 a) (specOver F ℂ)) =
              coefficientLevelPoint H.toHostRaw G hbar B hB τ₀ V C hVC a hact hc 5 (cHalf G I • x) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  let hbar := nativeDyadicGeometricHost_bar_eq e q d he hH
  obtain ⟨B, hB, _hcop, _hinv, hseed⟩ :=
    nativeDyadicHost_exists_genericSerreSeed e q d he hH
  refine ⟨B, hB, ?_⟩
  intro τ₀
  letI : Algebra (OK G) ℂ := (embed G (τ₀ : H.E →+* ℂ)).toAlgebra
  have hseedτ := hseed τ₀
  obtain ⟨M, hM, W, w, C, hΔ, _hhost, _hw, _hLie, _hLB, _hpol, _hu,
    hC, _hsurj, _hker, _hderiv, hgeneric⟩ := hseedτ
  letI : NumberField M := hM
  letI : W.IsElliptic := ⟨hΔ.symm ▸ isUnit_one⟩
  obtain ⟨F, hF, _hMF, V, hV, hVC, a, _hnorm, hact, _hrest⟩ := hgeneric
  letI : NumberField F := hF
  letI : V.IsElliptic := hV
  obtain ⟨I, hI1, hI0, hIc, _hI2, hI5⟩ :
      ∃ I : Ideal (𝓞 H.E), I ≠ ⊤ ∧ I ≠ ⊥ ∧
        IsCoprime I (H.conj • I) ∧ IsCoprime I (Ideal.span {(2 : 𝓞 H.E)}) ∧
        I * (H.conj • I) = Ideal.span {(5 : 𝓞 H.E)} :=
    NativeTheta.Cusp.SplitLevel.exists_five_split_level e q d he hH
  have hmap : I.map (G.bar : 𝓞 H.E →+* 𝓞 H.E) = H.conj • I := by
    rw [Ideal.pointwise_smul_def]
    congr 1
    ext z
    exact congrArg (fun b : 𝓞 H.E => (b : H.E))
      (nativeDyadicGeometricHost_bar_eq e q d he hH z)
  have hcop : IsCoprime I (I.map (G.bar : 𝓞 H.E →+* 𝓞 H.E)) := by
    rwa [hmap]
  have hprod : I * I.map (G.bar : 𝓞 H.E →+* 𝓞 H.E) = Ideal.span {(5 : 𝓞 H.E)} := by
    rwa [hmap]
  have hc : ∀ τ : cmTypeFinset H.toHostRaw,
      embed G (τ : H.E →+* ℂ) = algebraMap (OK G) ℂ := by
    intro τ
    exact nativeDyadic_quadraticEmbeddings_eq e q d he hH τ τ₀
  refine ⟨F, hF, V, hV, C, hVC, a, hact, I, hI1, hI0, hcop, hprod, hc, ?_⟩
  exact coefficient_half_quotient_equiv
    H.toHostRaw G hbar B hB τ₀ V C hVC a hact hc 5 (by norm_num) I hcop hprod

end RHLean.Analysis.AlpogeThin

end
