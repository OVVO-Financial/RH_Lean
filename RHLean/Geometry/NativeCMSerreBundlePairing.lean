import RHLean.Geometry.NativeCMLineBundlePairing
import RHLean.Geometry.NativeCMSerreBundleCube

/-!
# Exact polarization pairing of the original projective Serre bundle

The signed bundle is the previously constructed atlas on the actual
trace-frame equalizer. Its four-term polarization pairing on pure Serre
maps is identified by a genuine line-bundle isomorphism with the seed
pairing evaluated at the original integral Hermitian form `kLin`.

The proof reconstructs the geometric part of Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsTensorBundle.lean`. The native proof reuses the original trace
frame rather than choosing a new free module or a new projective frame.

The seed's actual cube generator and conjugate Rosati isomorphisms remain
explicit. They supply bilinearity and adjointness geometrically; no
positivity or metric identity substitutes for either. The source archive
states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open scoped Classical BigOperators Pointwise nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.TraceFrame

open SerreScheme SchemeTheory SchemeTheory.PullClasses SchemeTheory.CubicalPairing

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : NativeGeometricHost E} {D : TraceLattice H} {ε : ℤˣ}
    (F : TraceFrame D ε) {S : Scheme.{0}} {G : Over S}
    [GrpObj G] [IsCommMonObj G] (a : OAct (OK H) G)

def schemeBundleClass (L : LB G.left) {Y : Scheme.{0}}
    (r : Y ⟶ (F.schemeObj a).left) : PullClass L Y :=
  ∏ k, cls L (r ≫ (F.schemeBundleMap a k).left) ^ F.schemeBundleExponent k

theorem schemeBundleMap_pre {T : Over S} (x : T ⟶ F.schemeObj a)
    (ij : Fin F.n × Fin F.n) (k : Fin 4) :
    x ≫ F.schemeBundleMap a (ij, k) =
      pairTerm (x ≫ F.schemeBundleFirst a ij) (x ≫ F.schemeBundleSecond a ij) k := by
  fin_cases k <;> simp [schemeBundleMap, pairTerm, MonObj.comp_mul]

theorem schemeBundleClass_left (L : LB G.left) {T : Over S} (x : T ⟶ F.schemeObj a) :
    F.schemeBundleClass a L x.left =
      ∏ ij, diff₂ (ptCls L T) (x ≫ F.schemeBundleFirst a ij) (x ≫ F.schemeBundleSecond a ij) := by
  rw [schemeBundleClass, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun ij _ => ?_
  refine (Finset.prod_congr rfl fun k _ => ?_).trans
    (prod_pair (x ≫ F.schemeBundleFirst a ij) (x ≫ F.schemeBundleSecond a ij) (cls L))
  change cls L (x.left ≫ (F.schemeBundleMap a (ij, k)).left) ^ pairExponent k = _
  rw [← Over.comp_left, F.schemeBundleMap_pre]

def schemePairingForm {L : LB G.left} (hL : L.IsLB) (hT : HasCubeGenerator G L)
    (T : Over S) (x y : Pts (F.schemeAct a) T) : Additive (PullClass L T.left) :=
  SerreGram.gramForm (lamForm a hL hT T)
    (fun i => Pts.post (F.isLinearHom_schemeCoordinate a i) T)
    (fun i j => kLin D ε (F.x i) (F.x j)) x y

theorem schemeBundleClass_eq_quadratic {L : LB G.left}
    (hL : L.IsLB) (hT : HasCubeGenerator G L)
    (T : Over S) (x : T ⟶ F.schemeObj a) :
    F.schemeBundleClass a L x.left =
      (F.schemePairingForm a hL hT T
        (Pts.mk (F.schemeAct a) x) (wK H • Pts.mk (F.schemeAct a) x)).toMul := by
  rw [F.schemeBundleClass_left]
  refine (Finset.prod_congr rfl fun ij _ => ?_).trans (toMul_sum _ _).symm
  simp only [schemeBundleFirst, schemeBundleSecond, ← Category.assoc]
  rfl

theorem schemeBundleClass_diff₂ {L : LB G.left}
    (hL : L.IsLB) (hT : HasCubeGenerator G L)
    (ha : ∀ c, LamEq L (a.act c) (𝟙 G) L (𝟙 G) (a.act (barOK H c)))
    {T : Over S} (x y : T ⟶ F.schemeObj a) :
    diff₂ (fun q : T ⟶ F.schemeObj a => F.schemeBundleClass a L q.left) x y =
      (F.schemePairingForm a hL hT T
        (Pts.mk (F.schemeAct a) x) (Pts.mk (F.schemeAct a) y)).toMul := by
  simp only [diff₂, F.schemeBundleClass_eq_quadratic a hL hT]
  have hp := SerreGram.gramForm_polar
    (p := fun i => Pts.post (F.isLinearHom_schemeCoordinate a i) T)
    (lamForm_comm a hL hT T) (lamForm_adj a hL hT (barOK H) ha T)
    (fun i j => kLin_barOK D ε (F.x i) (F.x j))
    (wK_add_barOK (H := H))
    (Pts.mk (F.schemeAct a) x) (Pts.mk (F.schemeAct a) y)
  simp only [sub_eq_add_neg] at hp
  exact congrArg Additive.toMul hp

/-- Each pure tensor projects using exactly the original dual-frame
coefficient, as an equality of actual scheme-valued points. -/
theorem schemeCoordinate_pure_point (T : Over S) (u : T ⟶ G)
    (m : D.La) (i : Fin F.n) :
    Pts.post (F.isLinearHom_schemeCoordinate a i) T
        (Pts.mk (F.schemeAct a) (u ≫ (F.schemeIsTensor a).tmul m)) =
      F.incl m i • Pts.mk a u := by
  apply Pts.ext
  simp only [Pts.hom_post, Pts.hom_mk, Pts.hom_smul, Category.assoc,
    F.tmul_schemeCoordinate]
  rfl

/-- The source's actual pure-generator polarization isomorphism, with
the original projective module and the exact trace-Hermitian coefficient. -/
theorem schemeBundle_pure_pairing {L : LB G.left}
    (hL : L.IsLB) (hT : HasCubeGenerator G L)
    (ha : ∀ c, LamEq L (a.act c) (𝟙 G) L (𝟙 G) (a.act (barOK H c)))
    (m m' : D.La) :
    LamEq (F.schemeBundle a L) ((F.schemeIsTensor a).tmul m)
      ((F.schemeIsTensor a).tmul m') L (a.act (kLin D ε m m')) (𝟙 G) := by
  change LBIso (LB.LinComb
      (LB.LinComb L (fun k => (F.schemeBundleMap a k).left) F.schemeBundleExponent)
      (fun k => (pairTerm (fst G G ≫ (F.schemeIsTensor a).tmul m)
        (snd G G ≫ (F.schemeIsTensor a).tmul m') k).left) pairExponent)
    (LB.LinComb L (fun k => (pairTerm (fst G G ≫ a.act (kLin D ε m m'))
      (snd G G ≫ 𝟙 G) k).left) pairExponent)
  refine lbIso_nested hL _ _ _ _ _ _
    ((prod_pair _ _ (F.schemeBundleClass a L)).trans
      (Eq.trans ?_ (prod_pair _ _ (cls L)).symm))
  rw [F.schemeBundleClass_diff₂ a hL hT ha, Category.comp_id]
  exact congrArg Additive.toMul (F.gram_pure
    (lamForm a hL hT (G ⊗ G)) (lamForm_adj a hL hT (barOK H) ha (G ⊗ G))
    (fun i => Pts.post (F.isLinearHom_schemeCoordinate a i) (G ⊗ G)) m m'
    (fun i => F.schemeCoordinate_pure_point a (G ⊗ G) (fst G G) m i)
    (fun i => F.schemeCoordinate_pure_point a (G ⊗ G) (snd G G) m' i))

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

/-- The pure pairing isomorphism for the actual literal coefficient
ideal B^-1. Both genuine seed geometric hypotheses are displayed. -/
theorem coefficientSerreOriginBundle_pure_pairing
    (hT : HasCubeGenerator (WeierstrassCurve.schemeOver W) (WeierstrassCurve.originLB W))
    (ha : ∀ c, LamEq (WeierstrassCurve.originLB W) (a.act c) (𝟙 _)
      (WeierstrassCurve.originLB W) (𝟙 _) (a.act (barOK G c)))
    (m m' : (coefficientTraceLattice H G hbar B hB).La) :
    LamEq (coefficientSerreOriginBundle H G hbar B hB ε W a)
      (((coefficientSerreFrame H G hbar B hB ε).schemeIsTensor a).tmul m)
      (((coefficientSerreFrame H G hbar B hB ε).schemeIsTensor a).tmul m')
      (WeierstrassCurve.originLB W)
      (a.act (kLin (coefficientTraceLattice H G hbar B hB) ε m m')) (𝟙 _) :=
  (coefficientSerreFrame H G hbar B hB ε).schemeBundle_pure_pairing a
    (WeierstrassCurve.originLB_isLB W) hT ha m m'

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
