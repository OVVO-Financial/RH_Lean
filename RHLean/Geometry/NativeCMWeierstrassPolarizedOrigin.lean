import RHLean.Geometry.NativeCMWeierstrassOriginAmple
import RHLean.Geometry.NativeCMWeierstrassOriginBaseChange
import RHLean.Geometry.NativeCMLineBundleKernel

/-!
# The actual integral origin line bundle is a principal polarization

Native reconstruction of Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/OriginLineBundlePolarisation.lean`
- `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/NonzeroLocus.lean`

The constructed integral Weierstrass group scheme carries its literal origin
bundle. Its rigidification, inversion symmetry, relative ampleness and trivial
translation kernel are all proved. The kernel statement ranges over arbitrary
commutative test rings, including nilpotents. No CM scheme action or arithmetic
metric comparison is inferred from these polarization properties alone.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped BigOperators

namespace RHLean.Geometry.NativeCM.SchemeTheory

section Definitions

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def Rigidified (L : LB A.left) : Prop :=
  ∃ t : LB.Gen (L.pull (identitySection A)), t.IsGen

def Sym (L : LB A.left) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]), t.IsGen

end Definitions

namespace WeierstrassCurve

variable {R : Type} [CommRing R] [_root_.IsReduced R]
  (W : WeierstrassCurve R) [W.IsElliptic]

theorem originLB_symmetric : Sym (schemeOver W) (originLB W) := by
  intro _
  obtain ⟨t, ht⟩ := originLB_inversion_isomorphic W
  let ι := (toSpec W ⁻¹ᵁ (⊤ : (Sp R).Opens)).ι
  have h := LB.isGen_pullGen (originLB W)
    ![(GrpObj.inv : schemeOver W ⟶ schemeOver W).left, 𝟙 (scheme W)]
    ![1, -1] t ht ι
  have e : (fun k : Fin 2 => ι ≫
      ![(GrpObj.inv : schemeOver W ⟶ schemeOver W).left, 𝟙 (scheme W)] k) =
      ![ι ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left, ι] := by
    funext k
    fin_cases k <;> simp
  rw [e] at h
  exact ⟨⊤, trivial, _, h⟩

theorem originLB_kTriv : KTriv (schemeOver W) (originLB W) := by
  have hz : ∀ (T : Scheme.{0}) (t : T ⟶ (schemeOver W).left) (i : (originLB W).ι)
      (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i),
      (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔
        t = t ≫ (schemeOver W).hom ≫ identitySection (schemeOver W) := by
    intro T t i h
    simpa only [identitySection, one_left] using appLE_originSec_eq_zero_iff W t i h
  refine kTriv_of_sections_vanish_on_zero _ (schemeOver W) (originLB W)
    (originSec W) (originLB_isLB W) hz ?_
  intro R' _ f Y φ q H s T t j h e
  change t ≫ φ = t ≫ φ ≫ toSpec W ≫ zero W at e
  exact appLE_sec_pull_originLB_eq_zero W H s t j h e

/-- All four original source polarization properties of the same origin
bundle on the group scheme built from the same equation. -/
theorem originLB_polarisation :
    Rigidified (schemeOver W) (originLB W) ∧ Sym (schemeOver W) (originLB W) ∧
      RelAmple (schemeOver W) (originLB W) ∧ KTriv (schemeOver W) (originLB W) :=
  ⟨originLB_rigidified W, originLB_symmetric W, relAmple_originLB W, originLB_kTriv W⟩

end WeierstrassCurve

end RHLean.Geometry.NativeCM.SchemeTheory
