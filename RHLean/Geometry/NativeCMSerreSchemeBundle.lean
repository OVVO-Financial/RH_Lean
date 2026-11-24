import RHLean.Geometry.NativeCMSerreSchemeTensor
import RHLean.Geometry.NativeCMSerreGramForm
import RHLean.Geometry.NativeCMWeierstrassPolarizedOrigin

/-!
# The explicit trace-frame tensor bundle on the represented Serre scheme

The original integral Hermitian frame defines actual projection morphisms
from its represented tensor scheme. The source's tensor bundle is the
signed product of four actual origin-bundle pullbacks for every pair of
frame indices. Its line-bundle atlas and origin rigidification are proved.
The pure-generator identities retain the original kLin coefficients.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsTensorBundle.lean`. We use the four terms of its two-variable cube
explicitly instead of indexing them by subsets. This file does not assert
the cubical pairing isomorphism, ampleness or trivial kernel of the tensor
bundle; those require the genuine seed cubical and Rosati compatibilities.
The source archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open scoped Classical BigOperators TensorProduct Pointwise nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SerreScheme.IsTensor

variable {S : Scheme.{0}} {O : Type} [CommRing O]
    {G : Over S} [GrpObj G] [IsCommMonObj G]

def self (a : OAct O G) : IsTensor G a G a O where
  equiv T := TensorProduct.lid O (Pts a T)
  natural _ z := by
    induction z using TensorProduct.inductionOn with
    | tmul c x => simp only [LinearMap.lTensor_tmul, TensorProduct.lid_tmul, map_smul]
    | add z w hz hw => simp only [map_add, hz, hw]

@[simp] theorem self_tmul (a : OAct O G) (c : O) : (self a).tmul c = a.act c := by
  change Pts.hom (TensorProduct.lid O (Pts a G) (c ⊗ₜ[O] Pts.mk a (𝟙 G))) = _
  rw [TensorProduct.lid_tmul, Pts.hom_smul, Pts.hom_mk, Category.id_comp]

end RHLean.Geometry.NativeCM.SerreScheme.IsTensor

namespace RHLean.Geometry.NativeCM.SchemeTheory

namespace WeierstrassCurve

variable {R : Type} [CommRing R] [_root_.IsReduced R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    {A : Over (Sp R)} [GrpObj A]
    {I : Type} [Fintype I]

/-- Every signed tensor product of origin pullbacks along actual group
morphisms has the literal unit rigidification at the identity. -/
theorem rigidified_originLinComb (f : I → (A ⟶ schemeOver W))
    (hf : ∀ i, IsMonHom (f i)) (e : I → ℤ) :
    Rigidified A (LB.LinComb (originLB W) (fun i => (f i).left) e) := by
  have hz : ∀ i, identitySection A ≫ (f i).left = zero W := fun i => by
    have := hf i
    rw [identitySection, ← Over.comp_left, IsMonHom.one_hom, one_left]
  refine ⟨⟨fun _ => 1⟩, ?_⟩
  intro j j'
  have hg : ((LB.LinComb (originLB W) (fun i => (f i).left) e).pull
      (identitySection A)).g j j' = 1 := by
    apply Units.ext
    apply Cartier.ext_germ
    intro p hp
    have key : ∀ k : PUnit → I → Bool,
        p ∈ ((LB.LinComb (originLB W) (fun i => (f i).left) e).pull
          (identitySection A)).U k → k = fun _ _ => true := by
      intro k hk
      funext u i
      have hk' : (f i).left (identitySection A p) ∈
          (originLB W).U (k u i) :=
        Set.mem_iInter.1 (Set.mem_iInter.1 hk u) i
      have hk'' : zero W p ∈ (originLB W).U (k u i) := by
        change (identitySection A ≫ (f i).left) p ∈ _ at hk'
        rwa [hz i] at hk'
      rcases hki : k u i with _ | _
      · rw [hki] at hk''
        exact absurd ((zero_preimage_coordOpen_two W).le hk'') id
      · rfl
    obtain rfl := key j hp.1
    obtain rfl := key j' hp.2
    have hdiag : ((LB.LinComb (originLB W) (fun i => (f i).left) e).pull
        (identitySection A)).g (fun _ _ => true) (fun _ _ => true) = 1 := by
      simp only [LB.pull, LB.LinComb, originLB, LB.twoChart, map_one,
        one_zpow, Finset.prod_const_one]
    exact congrArg (fun u => ((Sp R).presheaf.germ _ p hp).hom
      (u : Γ(Sp R, _))) hdiag
  change res _ 1 = _ * res _ 1
  rw [map_one, map_one, hg, _root_.one_mul]

end WeierstrassCurve

end RHLean.Geometry.NativeCM.SchemeTheory

namespace RHLean.Geometry.NativeCM.TraceFrame

open SerreScheme SchemeTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : NativeGeometricHost E} {D : TraceLattice H} {ε : ℤˣ}
    (F : TraceFrame D ε) {S : Scheme.{0}} {G : Over S}
    [GrpObj G] [IsCommMonObj G] (a : OAct (OK H) G)

/-- The coordinate functional is the original Hermitian dual-frame pairing. -/
def coefficient (i : Fin F.n) : D.La →ₗ[OK H] OK H :=
  (LinearMap.proj i).comp F.incl

@[simp] theorem coefficient_apply (i : Fin F.n) (m : D.La) :
    F.coefficient i m = kLin D ε m (F.y i) := rfl

/-- Each coordinate is an actual scheme morphism extracted by naturality. -/
def schemeCoordinate (i : Fin F.n) : F.schemeObj a ⟶ G :=
  (F.schemeIsTensor a).mapLeft (IsTensor.self a) (F.coefficient i)

instance isMonHom_schemeCoordinate (i : Fin F.n) : IsMonHom (F.schemeCoordinate a i) :=
  IsTensor.isMonHom_mapLeft _ _ _

theorem isLinearHom_schemeCoordinate (i : Fin F.n) :
    IsLinearHom (F.schemeAct a) a (F.schemeCoordinate a i) :=
  IsTensor.isLinearHom_mapLeft _ _ _

@[reassoc (attr := simp)]
theorem tmul_schemeCoordinate (i : Fin F.n) (m : D.La) :
    (F.schemeIsTensor a).tmul m ≫ F.schemeCoordinate a i =
      a.act (kLin D ε m (F.y i)) := by
  rw [schemeCoordinate, IsTensor.tmul_mapLeft, IsTensor.self_tmul, coefficient_apply]

def schemeBundleFirst (k : Fin F.n × Fin F.n) : F.schemeObj a ⟶ G :=
  F.schemeCoordinate a k.1 ≫ a.act (kLin D ε (F.x k.1) (F.x k.2))

def schemeBundleSecond (k : Fin F.n × Fin F.n) : F.schemeObj a ⟶ G :=
  (F.schemeAct a).act (wK H) ≫ F.schemeCoordinate a k.2

instance isMonHom_schemeBundleFirst (k : Fin F.n × Fin F.n) :
    IsMonHom (F.schemeBundleFirst a k) := by
  have := a.hom (kLin D ε (F.x k.1) (F.x k.2))
  exact inferInstanceAs (IsMonHom
    (F.schemeCoordinate a k.1 ≫ a.act (kLin D ε (F.x k.1) (F.x k.2))))

instance isMonHom_schemeBundleSecond (k : Fin F.n × Fin F.n) :
    IsMonHom (F.schemeBundleSecond a k) := by
  have := (F.schemeAct a).hom (wK H)
  exact inferInstanceAs (IsMonHom ((F.schemeAct a).act (wK H) ≫ F.schemeCoordinate a k.2))

/-- The four terms are addition, the two projections, and the zero map. -/
def schemeBundleMap (k : (Fin F.n × Fin F.n) × Fin 4) : F.schemeObj a ⟶ G :=
  ![F.schemeBundleFirst a k.1 * F.schemeBundleSecond a k.1,
    F.schemeBundleFirst a k.1, F.schemeBundleSecond a k.1, 1] k.2

def schemeBundleExponent (k : (Fin F.n × Fin F.n) × Fin 4) : ℤ :=
  ![1, -1, -1, 1] k.2

instance isMonHom_schemeBundleMap (k : (Fin F.n × Fin F.n) × Fin 4) :
    IsMonHom (F.schemeBundleMap a k) := by
  rcases k with ⟨ij, k⟩
  fin_cases k
  · exact isMonHom_mul _ _
  · exact F.isMonHom_schemeBundleFirst a ij
  · exact F.isMonHom_schemeBundleSecond a ij
  · exact isMonHom_one

/-- The source tensor bundle on the actual equalizer representing the
original projective module. All signed factors are explicit. -/
def schemeBundle (L : LB G.left) : LB (F.schemeObj a).left :=
  LB.LinComb L (fun k => (F.schemeBundleMap a k).left) F.schemeBundleExponent

theorem schemeBundle_isLB {L : LB G.left} (hL : L.IsLB) : (F.schemeBundle a L).IsLB :=
  LB.isLB_linComb hL _ _

theorem tmul_schemeBundleFirst (k : Fin F.n × Fin F.n) (m : D.La) :
    (F.schemeIsTensor a).tmul m ≫ F.schemeBundleFirst a k =
      a.act (F.coefficient k.1 m * kLin D ε (F.x k.1) (F.x k.2)) := by
  rw [schemeBundleFirst, ← Category.assoc, tmul_schemeCoordinate, ← a.mul, coefficient_apply]

theorem tmul_schemeBundleSecond (k : Fin F.n × Fin F.n) (m : D.La) :
    (F.schemeIsTensor a).tmul m ≫ F.schemeBundleSecond a k =
      a.act (wK H * F.coefficient k.2 m) := by
  rw [schemeBundleSecond, ← Category.assoc, ← IsTensor.tmul_smul,
    tmul_schemeCoordinate, ← coefficient_apply, map_smul, smul_eq_mul]

variable {R : Type} [CommRing R] [_root_.IsReduced R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (aW : OAct (OK H) (WeierstrassCurve.schemeOver W))

/-- The actual source tensor bundle is rigidified on the same integral
equation; no tensor-polarization existence is assumed. -/
theorem schemeOriginBundle_isLB_and_rigidified :
    (F.schemeBundle aW (WeierstrassCurve.originLB W)).IsLB ∧
      Rigidified (F.schemeObj aW) (F.schemeBundle aW (WeierstrassCurve.originLB W)) :=
  ⟨F.schemeBundle_isLB aW (WeierstrassCurve.originLB_isLB W),
    WeierstrassCurve.rigidified_originLinComb W (F.schemeBundleMap aW)
      (fun _ => inferInstance) F.schemeBundleExponent⟩

end RHLean.Geometry.NativeCM.TraceFrame

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM SerreScheme SchemeTheory

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E) (hbar : ∀ c : 𝓞 H.E, G.bar c = H.conj • c)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (ε : ℤˣ)
    {R : Type} [CommRing R] [_root_.IsReduced R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (a : OAct (OK G) (WeierstrassCurve.schemeOver W))

/-- Literal B^-1, its proved Hermitian frame, the represented tensor, and
the same original integral origin bundle occur in one construction. -/
def coefficientSerreOriginBundle :
    LB (coefficientSerreScheme H G hbar B hB ε a).left :=
  (coefficientSerreFrame H G hbar B hB ε).schemeBundle a (WeierstrassCurve.originLB W)

theorem coefficientSerreOriginBundle_isLB_and_rigidified :
    (coefficientSerreOriginBundle H G hbar B hB ε W a).IsLB ∧
      Rigidified (coefficientSerreScheme H G hbar B hB ε a)
        (coefficientSerreOriginBundle H G hbar B hB ε W a) :=
  (coefficientSerreFrame H G hbar B hB ε).schemeOriginBundle_isLB_and_rigidified W a

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
