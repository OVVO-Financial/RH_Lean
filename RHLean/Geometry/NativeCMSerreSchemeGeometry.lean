import RHLean.Geometry.NativeCMSchemeRetract
import RHLean.Geometry.NativeCMSerreSchemeTensor
import RHLean.Geometry.NativeCMWeierstrassReducedGroup

/-!
# Geometric properties of the actual trace-frame tensor scheme

The original trace frame gives a literal retraction from a finite power of
the seed. Its same represented equalizer is smooth, proper, and
geometrically connected. No abelian-scheme existence premise or substitute
projective module is used. The genuine quadratic-order action on the seed
is the input that defines the idempotent.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/`
`PowObjGeometricallyConnected.lean`, `powObj_property`,
`powObj_geometricallyConnected`, and the retract property argument. Here
the already constructed native trace frame replaces the source's generic
choice of summand. The archive states no license; attribution is retained
without assigning one.

The identity-fibre proof is the declaration `geomConn_id` from
`src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/`
`LinCombTrivG.lean` at the same pinned source.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open scoped Classical Pointwise nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SerreScheme

variable {S : Scheme.{0}}

theorem powObj_property (P : MorphismProperty Scheme.{0}) [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] (h₀ : P (𝟙 S)) (G : Over S) (hG : P G.hom) :
    ∀ n : ℕ, P (powObj G n).hom
  | 0 => h₀
  | n + 1 =>
    P.comp_mem _ _ (P.pullback_fst G.hom (powObj G n).hom (powObj_property P h₀ G hG n)) hG

theorem powObj_geometricallyConnected (G : Over S) [UniversallyOpen G.hom]
    [GeometricallyConnected G.hom] : ∀ n : ℕ, GeometricallyConnected (powObj G n).hom
  | 0 => by
    change GeometricallyConnected (𝟙 S)
    rw [geometricallyConnected_iff]
    intro K _ y Z fst snd h
    have h' : IsPullback y (𝟙 _) (𝟙 S) y := IsPullback.of_vert_isIso ⟨by simp⟩
    let e : Z ≅ Spec (CommRingCat.of K) := h.isoIsPullback _ _ h'
    exact (Scheme.homeoOfIso e.symm).surjective.connectedSpace
      (Scheme.homeoOfIso e.symm).continuous
  | n + 1 => by
    have := powObj_geometricallyConnected G n
    have : UniversallyOpen (powObj G n).hom :=
      powObj_property @UniversallyOpen inferInstance G inferInstance n
    exact GeometricallyConnected.comp (pullback.fst G.hom (powObj G n).hom) G.hom

end RHLean.Geometry.NativeCM.SerreScheme

namespace RHLean.Geometry.NativeCM.TraceFrame

open SerreScheme

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : NativeGeometricHost E} {D : TraceLattice H} {ε : ℤˣ}
    (F : TraceFrame D ε) {S : Scheme.{0}} {G : Over S}
    [GrpObj G] [IsCommMonObj G] (a : OAct (OK H) G)

theorem schemeIncl_left_proj :
    (F.schemeIncl a).left ≫ (F.schemeProj a).left = 𝟙 (F.schemeObj a).left := by
  rw [← Over.comp_left, F.schemeIncl_proj, Over.id_left]

/-- The original split inclusion is a closed immersion when the seed is
separated. This concerns the actual fixed subscheme of the original matrix. -/
theorem schemeIncl_isClosedImmersion [IsSeparated G.hom] :
    IsClosedImmersion (F.schemeIncl a).left := by
  have : IsSeparated (powObj G F.n).hom :=
    powObj_property @IsSeparated inferInstance G inferInstance F.n
  exact SchemeTheory.Retract.isClosedImmersion_section
    (F.schemeIncl_left_proj a) (Over.w (F.schemeProj a))

instance schemeSmooth [Smooth G.hom] : Smooth (F.schemeObj a).hom := by
  have : Smooth (powObj G F.n).hom :=
    powObj_property @Smooth inferInstance G inferInstance F.n
  exact SchemeTheory.Retract.smooth (F.schemeIncl_left_proj a) (Over.w (F.schemeProj a))

instance schemeProper [IsProper G.hom] : IsProper (F.schemeObj a).hom := by
  have : IsProper (powObj G F.n).hom :=
    powObj_property @IsProper inferInstance G inferInstance F.n
  exact SchemeTheory.Retract.isProper (F.schemeIncl_left_proj a) (Over.w (F.schemeProj a))

instance schemeGeometricallyConnected [UniversallyOpen G.hom] [GeometricallyConnected G.hom] :
    GeometricallyConnected (F.schemeObj a).hom := by
  have := powObj_geometricallyConnected G F.n
  exact SchemeTheory.Retract.geometricallyConnected
    (F.schemeIncl_left_proj a) (Over.w (F.schemeProj a))

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

/-- The actual Serre scheme on literal B^-1 has the geometric properties
of an abelian scheme over the same base as the original elliptic equation. -/
theorem coefficientSerreScheme_geometricProperties :
    Smooth (coefficientSerreScheme H G hbar B hB ε a).hom ∧
      IsProper (coefficientSerreScheme H G hbar B hB ε a).hom ∧
      GeometricallyConnected (coefficientSerreScheme H G hbar B hB ε a).hom := by
  have : Smooth (WeierstrassCurve.schemeOver W).hom :=
    inferInstanceAs (Smooth (WeierstrassCurve.toSpec W))
  have : IsProper (WeierstrassCurve.schemeOver W).hom :=
    inferInstanceAs (IsProper (WeierstrassCurve.toSpec W))
  have : GeometricallyConnected (WeierstrassCurve.schemeOver W).hom :=
    inferInstanceAs (GeometricallyConnected (WeierstrassCurve.toSpec W))
  exact ⟨(coefficientSerreFrame H G hbar B hB ε).schemeSmooth a,
    (coefficientSerreFrame H G hbar B hB ε).schemeProper a,
    (coefficientSerreFrame H G hbar B hB ε).schemeGeometricallyConnected a⟩

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
