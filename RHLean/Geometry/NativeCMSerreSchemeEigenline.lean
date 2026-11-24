import RHLean.Geometry.NativeCMSerreSchemeLie
import RHLean.Geometry.NativeCMAllPlaceEigenlineDegree

/-!
# The actual Serre Lie eigenmodule and its exact coordinate-image degree

The represented trace-frame scheme carries the full CM coefficient action.
Its intrinsic integral Lie eigenspace is identified with the already proved
integral eigenspace of O_F tensor_OK B^-1, hence with the literal extension
of B^-1 D(E/K). The same original Weierstrass equation supplies the analytic
place profile in the resulting original AllWt degree calculation.

This is a join of native proved constructors. The scheme action on the seed
and its action on the specified integral vector remain genuine explicit
inputs. No polarization, arithmetic Lie norm, class-group mean, or desired
degree is a premise or claimed consequence. The source blueprint is
Levent Alpöge (with Claude), CocoSgt/riemann-hypothesis-lean@
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/
TwoMulDegreeEigenLatticeTensorRankOne.lean; its component proofs have already
been rebuilt in the imported native modules. No new source closure is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open scoped Classical BigOperators TensorProduct Pointwise nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.Lie

variable {R : Type} [CommRing R] {G H : Over (Sp R)}
    [GrpObj G] [GrpObj H] [IsCommMonObj G] [IsCommMonObj H]

/-- Differentiation is literal postcomposition of dual-number tangent maps. -/
def map (f : G ⟶ H) [IsMonHom f] : Lie G →ₗ[R] Lie H where
  toFun x := ⟨Additive.ofMul (hom x ≫ f), isTangent_comp x.property f⟩
  map_add' x y := ext (MonObj.mul_comp (hom x) (hom y) f)
  map_smul' c x := ext (Category.assoc (epsScale c) (hom x) f)

@[simp] theorem hom_map (f : G ⟶ H) [IsMonHom f] (x : Lie G) :
    hom (map f x) = hom x ≫ f := rfl

end RHLean.Geometry.NativeCM.SchemeTheory.Lie

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM SerreScheme SchemeTheory
open SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie
open RHLean.Geometry.NativeCM.LineDegree RHLean.Geometry.NativeCM.AllPlaceTangentPeriod

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E) (hbar : ∀ c : 𝓞 H.E, G.bar c = H.conj • c)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (F : Type) [Field F] [Algebra H.E F]
    (W : WeierstrassCurve (𝓞 F)) [W.IsElliptic]
    (a : OAct (OK G) (schemeOver W))
    (ha : ∀ c, IsLieComb ![algebraMap (OK G) (𝓞 F) c] ![integralVector W]
      (integralVector W ≫ a.act c))

def coefficientLieEquiv : IntegralTensor H G F B ≃ₗ[𝓞 F]
    Lie (coefficientSerreScheme H G hbar B hB 1 a) :=
  (coefficientSerreScheme_exists_integralLie H G hbar B hB (𝓞 F) W a ha).choose

theorem coefficientLieEquiv_one (m : (coefficientIdeal H B : Submodule (𝓞 H.E) H.E)) :
    Lie.hom (coefficientLieEquiv H G hbar B hB F W a ha (1 ⊗ₜ[OK G] m)) =
      integralVector W ≫ (coefficientSerreSchemeTensor H G hbar B hB 1 a).tmul m :=
  (coefficientSerreScheme_exists_integralLie H G hbar B hB (𝓞 F) W a ha).choose_spec.1 m

theorem coefficientLieEquiv_action (c : 𝓞 H.E) (y : IntegralTensor H G F B) :
    Lie.hom (coefficientLieEquiv H G hbar B hB F W a ha
      (integralCoefficientAction H G F B c y)) =
    Lie.hom (coefficientLieEquiv H G hbar B hB F W a ha y) ≫
      (coefficientSerreSchemeFullAction H G hbar B hB 1 a).act c :=
  (coefficientSerreScheme_exists_integralLie H G hbar B hB (𝓞 F) W a ha).choose_spec.2 c y

/-- The full-order action on the actual Lie module is differentiated from
the actual coefficient action on the constructed scheme. -/
def coefficientLieAction (c : 𝓞 H.E) :
    Module.End (𝓞 F) (Lie (coefficientSerreScheme H G hbar B hB 1 a)) := by
  have := (coefficientSerreSchemeFullAction H G hbar B hB 1 a).hom c
  exact Lie.map ((coefficientSerreSchemeFullAction H G hbar B hB 1 a).act c)

set_option synthInstance.maxHeartbeats 200000 in
/-- The identity-character eigenmodule in the intrinsic integral Lie module. -/
def coefficientLieEigenmodule :
    Submodule (𝓞 F) (Lie (coefficientSerreScheme H G hbar B hB 1 a)) where
  carrier := {v | ∀ c : 𝓞 H.E, coefficientLieAction H G hbar B hB F W a c v =
    algebraMap (𝓞 H.E) (𝓞 F) c • v}
  zero_mem' := by
    intro c
    rw [map_zero]
    exact (DistribMulAction.smul_zero _).symm
  add_mem' := by
    intro v w hv hw c
    rw [map_add, hv c, hw c, smul_add]
  smul_mem' := by
    intro r v hv c
    rw [map_smul, hv c]
    exact smul_comm r (algebraMap (𝓞 H.E) (𝓞 F) c) v

theorem coefficientLieEquiv_mem_iff (y : IntegralTensor H G F B) :
    coefficientLieEquiv H G hbar B hB F W a ha y ∈
        coefficientLieEigenmodule H G hbar B hB F W a ↔
      y ∈ integralEigenmodule H G F B := by
  constructor
  · intro hy c
    apply (coefficientLieEquiv H G hbar B hB F W a ha).injective
    rw [map_smul]
    apply Lie.ext
    rw [coefficientLieEquiv_action]
    exact congrArg Lie.hom (hy c)
  · intro hy c
    apply Lie.ext
    change Lie.hom (coefficientLieEquiv H G hbar B hB F W a ha y) ≫
        (coefficientSerreSchemeFullAction H G hbar B hB 1 a).act c = _
    rw [← coefficientLieEquiv_action, ← map_smul, hy c]

def coefficientLieEigenEquiv : integralEigenmodule H G F B ≃ₗ[𝓞 F]
    coefficientLieEigenmodule H G hbar B hB F W a where
  toFun y := ⟨coefficientLieEquiv H G hbar B hB F W a ha y,
    (coefficientLieEquiv_mem_iff H G hbar B hB F W a ha y).mpr y.property⟩
  invFun v := ⟨(coefficientLieEquiv H G hbar B hB F W a ha).symm v,
    (coefficientLieEquiv_mem_iff H G hbar B hB F W a ha _).mp (by
      rw [LinearEquiv.apply_symm_apply]
      exact v.property)⟩
  left_inv y := Subtype.ext ((coefficientLieEquiv H G hbar B hB F W a ha).symm_apply_apply y.1)
  right_inv v :=
    Subtype.ext ((coefficientLieEquiv H G hbar B hB F W a ha).apply_symm_apply v.1)
  map_add' y z := Subtype.ext (map_add (coefficientLieEquiv H G hbar B hB F W a ha) y.1 z.1)
  map_smul' c y := Subtype.ext (map_smul (coefficientLieEquiv H G hbar B hB F W a ha) c y.1)

/-- The coordinate map is the original coefficient evaluation applied
through the proved intrinsic Lie equivalence. -/
def coefficientLieEigenCoordinate : coefficientLieEigenmodule H G hbar B hB F W a →ₗ[𝓞 F] F :=
  (eigenCoordinate H G F B).comp
    (coefficientLieEigenEquiv H G hbar B hB F W a ha).symm.toLinearMap

theorem coefficientLieEigenCoordinate_range :
    LinearMap.range (coefficientLieEigenCoordinate H G hbar B hB F W a ha) =
      LinearMap.range (eigenCoordinate H G F B) := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(coefficientLieEigenEquiv H G hbar B hB F W a ha).symm v, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨coefficientLieEigenEquiv H G hbar B hB F W a ha y, by
      simp [coefficientLieEigenCoordinate]⟩

variable [NumberField F]

/-- No rational saturation is taken: this is the actual integral
different-twisted ideal, including its finite index. -/
def coefficientLieEigenCoordinateEquiv (hroot : (G.rt : H.E) = H.sqd) :
    coefficientLieEigenmodule H G hbar B hB F W a ≃ₗ[𝓞 F]
      (FractionalIdeal.extendedHom F (𝓞 F)
        (coefficientIdeal H B *
          (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E))) :=
  (coefficientLieEigenEquiv H G hbar B hB F W a ha).symm ≪≫ₗ
    eigenCoordinateEquiv H G F hroot hbar B hB

variable [IsTotallyComplex F]

/-- The full original all-place degree of the intrinsic Lie eigenmodule's
coordinate image, with the same equation's constructed analytic place profile.
Identification with a polarizing arithmetic Lie norm is not asserted. -/
theorem coefficientLieEigenCoordinate_actualPeriod_degree
    (hroot : (G.rt : H.E) = H.sqd) (hΔ : W.Δ = 1) :
    2 * RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.deg
        (lineNorm (embeddingProfile W hΔ))
        (LinearMap.range (coefficientLieEigenCoordinate H G hbar B hB F W a ha)) =
      (∑ σ : F →+* ℂ, PeriodArithmetic.latticeLogPeriod
        (lattice W hΔ (InfinitePlace.mk σ))) / (Module.finrank ℚ F : ℝ) +
        Real.log (rootDiscr H.K) - Real.log (rootDiscr H.E) := by
  rw [coefficientLieEigenCoordinate_range]
  exact eigenCoordinate_actualPeriod_degree H G hroot hbar B hB F W hΔ

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
