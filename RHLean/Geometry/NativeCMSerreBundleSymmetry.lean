import RHLean.Geometry.NativeCMLineBundleNested
import RHLean.Geometry.NativeCMSerreSchemeBundle

/-!
# Symmetry of the actual trace-frame Serre bundle

The seed's global inversion trivialization is pulled through each of the
four actual monoid maps. The explicit nested generators then trivialize
the inversion difference of their signed product. Thus the same bundle
on the same equalizer is symmetric, retaining the original projective
module and its integral Hermitian frame.

This is native glue to the attributed signed tensor-bundle construction.
The inversion naturality calculation is also used in Levent Alpöge (with
Claude), `CocoSgt/riemann-hypothesis-lean@`
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsProdPolAV.lean`, `inv_comp_left`. Cubicality, the Rosati identity,
relative ampleness, and trivial polarization kernel are not inferred from
this symmetry calculation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open scoped Classical BigOperators nonZeroDivisors Pointwise

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory

variable {S : Scheme.{0}} (A G : Over S) [GrpObj A] [GrpObj G]
    (L : LB G.left) {K : Type} [Fintype K]

/-- A global inversion generator survives every signed product of actual
group homomorphism pullbacks. -/
theorem inversion_isomorphic_linComb
    (hL : ∃ t : LB.Gen (LB.LinComb L (K := Fin 2)
      ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1]), t.IsGen)
    (f : K → (A ⟶ G)) (hf : ∀ k, IsMonHom (f k)) (ε : K → ℤ) :
    ∃ t : LB.Gen (LB.LinComb (LB.LinComb L (fun k => (f k).left) ε) (K := Fin 2)
      ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]), t.IsGen := by
  obtain ⟨t, ht⟩ := hL
  apply LB.exists_isGen_nested
  intro k
  have := hf k
  have e : (fun b : Fin 2 => (f k).left ≫
      ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] b) =
        fun b => ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] b ≫ (f k).left := by
    funext b
    fin_cases b
    · exact (congrArg Over.Hom.left (GrpObj.inv_hom (f k))).symm
    · simp
  have h : ∃ v : LB.Gen (LB.LinComb L
      (fun b : Fin 2 => (f k).left ≫ ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] b)
      ![1, -1]), v.IsGen :=
    ⟨LB.pullGen L _ _ t (f k).left, LB.isGen_pullGen L _ _ t ht (f k).left⟩
  rw [e] at h
  exact h

/-- The original source local symmetry condition follows from a global
inversion generator by literal restriction to the full base open. -/
theorem sym_of_inversion_isomorphic (N : LB A.left)
    (hN : ∃ t : LB.Gen (LB.LinComb N (K := Fin 2)
      ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]), t.IsGen) :
    Sym A N := by
  intro _s
  obtain ⟨t, ht⟩ := hN
  let jTop := (A.hom ⁻¹ᵁ (⊤ : S.Opens)).ι
  have h : ∃ v : LB.Gen (LB.LinComb N
      (fun k : Fin 2 => jTop ≫ ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] k)
      ![1, -1]), v.IsGen :=
    ⟨LB.pullGen N _ _ t jTop, LB.isGen_pullGen N _ _ t ht jTop⟩
  have e : (fun k : Fin 2 => jTop ≫
      ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] k) =
        ![jTop ≫ (GrpObj.inv : A ⟶ A).left, jTop] := by
    funext k
    fin_cases k <;> simp
  rw [e] at h
  exact ⟨⊤, trivial, h⟩

end RHLean.Geometry.NativeCM.SchemeTheory

namespace RHLean.Geometry.NativeCM.TraceFrame

open SerreScheme SchemeTheory SchemeTheory.WeierstrassCurve

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : NativeGeometricHost E} {D : TraceLattice H} {ε : ℤˣ}
    (F : TraceFrame D ε) {R : Type} [CommRing R] [_root_.IsReduced R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (a : OAct (OK H) (schemeOver W))

/-- The generator lives on the inversion difference of the already
constructed bundle on the already constructed trace-frame equalizer. -/
theorem schemeOriginBundle_inversion_isomorphic :
    ∃ t : LB.Gen (LB.LinComb (F.schemeBundle a (originLB W)) (K := Fin 2)
      ![(GrpObj.inv : F.schemeObj a ⟶ F.schemeObj a).left,
        𝟙 (F.schemeObj a).left] ![1, -1]), t.IsGen :=
  inversion_isomorphic_linComb (F.schemeObj a) (schemeOver W) (originLB W)
    (originLB_inversion_isomorphic W) (F.schemeBundleMap a)
    (fun _ => inferInstance) F.schemeBundleExponent

theorem schemeOriginBundle_symmetric :
    Sym (F.schemeObj a) (F.schemeBundle a (originLB W)) :=
  sym_of_inversion_isomorphic (F.schemeObj a) (F.schemeBundle a (originLB W))
    (F.schemeOriginBundle_inversion_isomorphic W a)

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

/-- Symmetry of the actual bundle built from literal B^-1 and its own
trace frame, on the same represented tensor and the same seed equation. -/
theorem coefficientSerreOriginBundle_symmetric :
    Sym (coefficientSerreScheme H G hbar B hB ε a)
      (coefficientSerreOriginBundle H G hbar B hB ε W a) :=
  (coefficientSerreFrame H G hbar B hB ε).schemeOriginBundle_symmetric W a

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
