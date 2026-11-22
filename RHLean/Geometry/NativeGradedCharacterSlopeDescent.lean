import RHLean.Geometry.NativeGradedSectionRegularity
import RHLean.Geometry.NativeRegularCharacterSlopeDescent

/-!
# All-place descent on the constructed integer-weight section algebra

The geometric regularity supplier proves regularity on finite sums of
integer-weight sections. It does not prove regularity on arbitrary rules on
test rings. This theorem restricts the action to that constructed algebra,
derives its group-determinant regularity from generic-frame evaluations, and
uses that very determinant in the integral twisted-trace descent.

The input regularity proof follows
`GlobalTheory.SecRingNonZeroDiv.eq_zero_of_mul_eq_zero` in
`IntegerExponentSectionMulEqZeroImpEqZero.lean`; the restricted action and
determinant weight follow `pullSec` and `levDet_mem_secZ` in
`MemLevEigenIffTransl.lean`, at upstream commit
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

The maps, their integral lattices, multiplication norms, short spanning
vectors and rank budget remain the same data throughout. Every quantitative
hypothesis of the original all-place descent is retained. The concrete
theta-cover model and its remaining quantitative suppliers still have to
instantiate those data; no complete character bound is claimed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField
open scoped BigOperators Matrix
open RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt
open RHLean.Geometry.AlpogeAllPlace.Formalism.HN (rkK)

namespace RHLean.Geometry

/-- Transfer the determinant actually constructed at component points to the
corresponding generic-point fields. The geometric input is precisely the
forward direction of `GlobalTheory.CompHt.genVal_eq_zero_iff` on homogeneous
sections; no identification between the point fields and generic fields is
made. The determinant's homogeneous weight is proved here. -/
theorem nativeGradedSection_groupDet_generic_nonzero_of_component_points
    {I K R Z H : Type} [Field K] [CommRing R] [Algebra K R]
    [Group H] [Fintype H] [DecidableEq H]
    (W : (I → ℤ) → Submodule K R)
    (hone : (1 : R) ∈ W 0)
    (hprod : ∀ e e', W e * W e' ≤ W (e + e'))
    (F : Z → Type) [∀ z, CommRing (F z)]
    (generic : ∀ z, R →+* F z)
    (point : Z → R →+* ℂ)
    (hspecialize : ∀ z d f, f ∈ W d → generic z f = 0 → point z f = 0)
    (st : H → R →ₐ[K] R)
    (hst : ∀ h d f, f ∈ W d → st h f ∈ W d)
    (e : I → ℤ) (u : R) (hu : u ∈ W e)
    (hdet : ∀ z, (Matrix.of fun h g : H => point z (st (h * g) u)).det ≠ 0) :
    ∀ z, (Matrix.of fun h g : H => generic z (st (h * g) u)).det ≠ 0 := by
  have hmem : (Matrix.of fun h g : H => st (h * g) u).det ∈
      W (Fintype.card H • e) :=
    nativeGradedSection_det_mem W hone hprod e _ fun h g => hst (h * g) e u hu
  intro z hz
  have hgeneric : generic z (Matrix.of fun h g : H => st (h * g) u).det = 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    exact hz
  have hpoint := hspecialize z (Fintype.card H • e) _ hmem hgeneric
  rw [RingHom.map_det, RingHom.mapMatrix_apply] at hpoint
  exact hdet z hpoint

section GradedSection

variable {I K R Z H : Type}
  [Fintype I] [DecidableEq I] [Group H] [Fintype H] [DecidableEq H]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [CommRing R] [Algebra K R]
  (W : (I → ℤ) → Submodule K R)
  (hone : (1 : R) ∈ W 0)
  (hprod : ∀ e e', W e * W e' ≤ W (e + e'))

local notation "Sec" => nativeGradedSectionAlgebra W hone hprod

/-- Generic-frame nonvanishing supplies the determinant used by the same
integral character maps, with the full all-place norm and rank costs. Neither
ambient reducedness nor ambient minimal-prime evaluations are assumed. -/
theorem nativeAllPlaceDescent_of_graded_character_section
    (F : Z → Type) [∀ z, Field (F z)] [∀ z, CharZero (F z)]
    (generic : ∀ z, R →+* F z)
    (frame : ∀ z, (I → (F z)ˣ) → R →+* F z)
    (hweight : ∀ z e f, f ∈ W e → ∀ t,
      frame z t f = nativeWeightTorusCharacter (F z) e t * generic z f)
    (hfaithful : ∀ e f, f ∈ W e → (∀ z, generic z f = 0) → f = 0)
    (st : H → R →ₐ[K] R)
    (hst : ∀ h e f, f ∈ W e → st h f ∈ W e)
    (h1 : ∀ x, st 1 x = x)
    (hmul : ∀ h h' x, st (h * h') x = st h' (st h x))
    (χ : H →* Kˣ) (e : I → ℤ) (u : Sec)
    (huw : (u : R) ∈ W e)
    (hdet : ∀ z, (Matrix.of fun h g : H => generic z (st (h * g) u)).det ≠ 0)
    (Vm V Vp N : Submodule K Sec)
    [FiniteDimensional K Vm] [FiniteDimensional K V] [FiniteDimensional K Vp]
    (hNV : N ≤ V)
    (hV : ∀ h, ∀ x ∈ V, nativeGradedSectionAction W hone hprod st hst h x ∈ V)
    (hm : ∀ h, ∀ x ∈ Vm,
      x * nativeGradedSectionAction W hone hprod st hst h u ∈ V)
    (hp : ∀ h, ∀ x ∈ V,
      x * nativeGradedSectionAction W hone hprod st hst h u ∈ Vp)
    (hN : ∀ x, x ∈ N ↔ x ∈ V ∧ ∀ h,
      nativeGradedSectionAction W hone hprod st hst h x = ((χ h : Kˣ) : K) • x)
    (A : Submodule (𝓞 K) Vm) (L : Submodule (𝓞 K) V)
    (Lu : Submodule (𝓞 K) Sec) (hu : u ∈ Lu)
    (hLu : ∀ h, ∀ v ∈ Lu, nativeGradedSectionAction W hone hprod st hst h v ∈ Lu)
    (hproduct : ∀ f : Vm, f ∈ A → ∀ v ∈ Lu,
      (f : Sec) * v ∈ L.map (V.subtype.restrictScalars (𝓞 K)))
    (hL : ∀ h, ∀ v ∈ L,
      nativeWeightAction (nativeGradedSectionAction W hone hprod st hst) V hV h v ∈ L)
    (NA : (K →+* ℂ) → Vm → ℝ)
    (NV : (K →+* ℂ) → V → ℝ)
    (hNV0 : ∀ σ v, 0 ≤ NV σ v)
    (hNVsmul : ∀ σ (a : K) v, NV σ (a • v) = ‖σ a‖ * NV σ v)
    (hNVadd : ∀ σ v w, NV σ (v + w) ≤ NV σ v + NV σ w)
    (hNVinv : ∀ h σ v,
      NV σ (nativeWeightAction (nativeGradedSectionAction W hone hprod st hst) V hV h v) =
        NV σ v)
    (hGramA : HasGram NA) (hGramB : HasGram (nativeEigenNorm hNV NV))
    (hAFG : A.FG) (hBFG : (nativeEigenLattice hNV L).FG) (hA0 : A ≠ ⊥)
    {C z b Λ δ t : ℝ} (hC : 0 ≤ C)
    (hqz : Real.log (Fintype.card H : ℝ) ≤ 45 * z ^ 2)
    (hz : 2 * C + 200 ≤ z) (hb : z ^ 12 ≤ b)
    (hM : ∀ h σ f,
      NV σ (nativeWeightMultiply (nativeGradedSectionAction W hone hprod st hst)
        u Vm V hm h f) ≤ Real.exp (C * z ^ 9) * NA σ f)
    (hshort : ∃ s : Set N,
      s ⊆ (nativeEigenLattice hNV L : Set N) ∧
      (∀ y ∈ s, ∀ σ, nativeEigenNorm hNV NV σ y ≤ Real.exp Λ) ∧
      (nativeEigenLattice hNV L : Set N) ⊆ (Submodule.span K s : Set N))
    (hΛ : 0 ≤ Λ) (hδ : 0 ≤ δ)
    (hrank : (Module.finrank K Vp : ℝ) ≤ (1 + δ) * rkK A)
    (ht : t ≤ slope_sq NA A - 2 * b) :
    t - δ * (|t| + 2 * Λ) ≤
      slope_sq (nativeEigenNorm hNV NV) (nativeEigenLattice hNV L) := by
  have hSec1 : ∀ x : Sec, nativeGradedSectionAction W hone hprod st hst 1 x = x := by
    intro x
    apply Subtype.ext
    change st 1 (x : R) = (x : R)
    exact h1 x
  have hSecMul : ∀ h h' (x : Sec),
      nativeGradedSectionAction W hone hprod st hst (h * h') x =
        nativeGradedSectionAction W hone hprod st hst h'
          (nativeGradedSectionAction W hone hprod st hst h x) := by
    intro h h' x
    apply Subtype.ext
    change st (h * h') (x : R) = st h' (st h (x : R))
    exact hmul h h' x
  have hreg := nativeGradedSection_groupDet_regular W hone hprod F generic frame
    hweight hfaithful st hst e u huw hdet
  exact nativeAllPlaceDescent_of_regular_groupDet
    (nativeGradedSectionAction W hone hprod st hst) hSec1 hSecMul χ u hreg
    Vm V Vp N hNV hV hm hp hN A L Lu hu hLu hproduct hL NA NV
    hNV0 hNVsmul hNVadd hNVinv hGramA hGramB hAFG hBFG hA0
    hC hqz hz hb hM hshort hΛ hδ hrank ht


/-- The chosen-point variant attaches the determinant returned by the short
integral section constructor. Homogeneous specialization first transports its
nonvanishing to each actual generic field; the preceding theorem then pays
exactly the same integral character maps, norms and ranks. -/
theorem nativeAllPlaceDescent_of_graded_component_section
    (F : Z → Type) [∀ z, Field (F z)] [∀ z, CharZero (F z)]
    (generic : ∀ z, R →+* F z)
    (frame : ∀ z, (I → (F z)ˣ) → R →+* F z)
    (hweight : ∀ z e f, f ∈ W e → ∀ t,
      frame z t f = nativeWeightTorusCharacter (F z) e t * generic z f)
    (hfaithful : ∀ e f, f ∈ W e → (∀ z, generic z f = 0) → f = 0)
    (st : H → R →ₐ[K] R)
    (hst : ∀ h e f, f ∈ W e → st h f ∈ W e)
    (h1 : ∀ x, st 1 x = x)
    (hmul : ∀ h h' x, st (h * h') x = st h' (st h x))
    (χ : H →* Kˣ) (e : I → ℤ) (u : Sec)
    (huw : (u : R) ∈ W e)
    (point : Z → R →+* ℂ)
    (hspecialize : ∀ z d f, f ∈ W d → generic z f = 0 → point z f = 0)
    (hdet : ∀ z, (Matrix.of fun h g : H => point z (st (h * g) u)).det ≠ 0)
    (Vm V Vp N : Submodule K Sec)
    [FiniteDimensional K Vm] [FiniteDimensional K V] [FiniteDimensional K Vp]
    (hNV : N ≤ V)
    (hV : ∀ h, ∀ x ∈ V, nativeGradedSectionAction W hone hprod st hst h x ∈ V)
    (hm : ∀ h, ∀ x ∈ Vm,
      x * nativeGradedSectionAction W hone hprod st hst h u ∈ V)
    (hp : ∀ h, ∀ x ∈ V,
      x * nativeGradedSectionAction W hone hprod st hst h u ∈ Vp)
    (hN : ∀ x, x ∈ N ↔ x ∈ V ∧ ∀ h,
      nativeGradedSectionAction W hone hprod st hst h x = ((χ h : Kˣ) : K) • x)
    (A : Submodule (𝓞 K) Vm) (L : Submodule (𝓞 K) V)
    (Lu : Submodule (𝓞 K) Sec) (hu : u ∈ Lu)
    (hLu : ∀ h, ∀ v ∈ Lu, nativeGradedSectionAction W hone hprod st hst h v ∈ Lu)
    (hproduct : ∀ f : Vm, f ∈ A → ∀ v ∈ Lu,
      (f : Sec) * v ∈ L.map (V.subtype.restrictScalars (𝓞 K)))
    (hL : ∀ h, ∀ v ∈ L,
      nativeWeightAction (nativeGradedSectionAction W hone hprod st hst) V hV h v ∈ L)
    (NA : (K →+* ℂ) → Vm → ℝ)
    (NV : (K →+* ℂ) → V → ℝ)
    (hNV0 : ∀ σ v, 0 ≤ NV σ v)
    (hNVsmul : ∀ σ (a : K) v, NV σ (a • v) = ‖σ a‖ * NV σ v)
    (hNVadd : ∀ σ v w, NV σ (v + w) ≤ NV σ v + NV σ w)
    (hNVinv : ∀ h σ v,
      NV σ (nativeWeightAction (nativeGradedSectionAction W hone hprod st hst) V hV h v) =
        NV σ v)
    (hGramA : HasGram NA) (hGramB : HasGram (nativeEigenNorm hNV NV))
    (hAFG : A.FG) (hBFG : (nativeEigenLattice hNV L).FG) (hA0 : A ≠ ⊥)
    {C z b Λ δ t : ℝ} (hC : 0 ≤ C)
    (hqz : Real.log (Fintype.card H : ℝ) ≤ 45 * z ^ 2)
    (hz : 2 * C + 200 ≤ z) (hb : z ^ 12 ≤ b)
    (hM : ∀ h σ f,
      NV σ (nativeWeightMultiply (nativeGradedSectionAction W hone hprod st hst)
        u Vm V hm h f) ≤ Real.exp (C * z ^ 9) * NA σ f)
    (hshort : ∃ s : Set N,
      s ⊆ (nativeEigenLattice hNV L : Set N) ∧
      (∀ y ∈ s, ∀ σ, nativeEigenNorm hNV NV σ y ≤ Real.exp Λ) ∧
      (nativeEigenLattice hNV L : Set N) ⊆ (Submodule.span K s : Set N))
    (hΛ : 0 ≤ Λ) (hδ : 0 ≤ δ)
    (hrank : (Module.finrank K Vp : ℝ) ≤ (1 + δ) * rkK A)
    (ht : t ≤ slope_sq NA A - 2 * b) :
    t - δ * (|t| + 2 * Λ) ≤
      slope_sq (nativeEigenNorm hNV NV) (nativeEigenLattice hNV L) := by
  have hgenericDet := nativeGradedSection_groupDet_generic_nonzero_of_component_points
    W hone hprod F generic point hspecialize st hst e u huw hdet
  exact nativeAllPlaceDescent_of_graded_character_section W hone hprod F generic frame
    hweight hfaithful st hst h1 hmul χ e u huw hgenericDet
    Vm V Vp N hNV hV hm hp hN A L Lu hu hLu hproduct hL NA NV
    hNV0 hNVsmul hNVadd hNVinv hGramA hGramB hAFG hBFG hA0
    hC hqz hz hb hM hshort hΛ hδ hrank ht

end GradedSection

end RHLean.Geometry

end
