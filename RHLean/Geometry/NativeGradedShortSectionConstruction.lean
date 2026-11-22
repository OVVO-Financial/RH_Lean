import RHLean.Geometry.NativeComponentRegularSection
import RHLean.Geometry.NativeGradedCharacterSlopeDescent

/-!
# Construct the integral section used by the graded character maps

The orbit evaluation in this file is the actual composite of the homogeneous
section inclusion, the level action and a chosen component point. It is not
an independent linear map. The component short-generator theorem constructs
one integral section with its original all-place pointwise bound. Its chosen
point determinants are transported to the generic fields, proving that the
same section gives jointly injective twisted-trace maps on the graded algebra.

`NativeGradedShortSectionData` bundles exactly the explicit component,
short-span, orbit-separation, support and norm-comparison inputs of
`nativeExists_component_short_integral_group_section`; it contains no regular
seed and no assumed determinant or trace-injection conclusion. The multiplier
metric and full slope costs are not hidden in this construction: their
remaining attachment is handled separately by the graded descent theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField
open scoped BigOperators Matrix

namespace RHLean.Geometry

section GradedSection

variable {I K R Z H P : Type}
  [Field K] [NumberField K] [Algebra K ℂ]
  [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R]
  [Fintype Z] [Group H] [Fintype H] [DecidableEq H]
  (W : (I → ℤ) → Submodule K R)
  (hone : (1 : R) ∈ W 0)
  (hprod : ∀ e e', W e * W e' ≤ W (e + e'))

local notation "Sec" => nativeGradedSectionAlgebra W hone hprod

/-- The exact chosen-point evaluation of each translated section. -/
def nativeGradedPointOrbit (U : Submodule K Sec)
    (point : Z → R →ₐ[K] ℂ) (st : H → R →ₐ[K] R) (z : Z) :
    U →ₗ[K] (H → ℂ) :=
  LinearMap.pi fun h => ((point z).comp (st h)).toLinearMap.comp
    ((nativeGradedSectionAlgebra W hone hprod).val.toLinearMap.comp U.subtype)

/-- The explicit inputs of the finite component section constructor, with
orbit evaluations fixed to the actual action and component points. -/
structure NativeGradedShortSectionData (U : Submodule K Sec)
    (point : Z → R →ₐ[K] ℂ) (st : H → R →ₐ[K] R)
    (J : Z → Type) [∀ z, Fintype (J z)]
    (E : P → Type) [∀ p, SeminormedAddCommGroup (E p)] where
  components : Z → Submodule K U
  components_span : iSup components = ⊤
  lattice : Submodule (𝓞 K) U
  componentLattice : ∀ z, Submodule (𝓞 K) (components z)
  componentFG : ∀ z, (componentLattice z).FG
  component_mem : ∀ z (v : components z), v ∈ componentLattice z → (v : U) ∈ lattice
  norm : (K →+* ℂ) → U → ℝ
  norm_nonneg : ∀ σ v, 0 ≤ norm σ v
  norm_smul : ∀ σ (a : K) v, norm σ (a • v) = ‖σ a‖ * norm σ v
  norm_add : ∀ σ v v', norm σ (v + v') ≤ norm σ v + norm σ v'
  shortSet : ∀ z, Set (components z)
  A : ℝ
  beta : ℝ
  A_nonneg : 0 ≤ A
  beta_nonneg : 0 ≤ beta
  short_mem : ∀ z, shortSet z ⊆ componentLattice z
  short_span : ∀ z, Submodule.span K (shortSet z) = ⊤
  short_bound : ∀ z v, v ∈ shortSet z → ∀ σ, norm σ (v : U) ≤ A
  rankBound : ℕ
  component_rank : ∀ z, Module.finrank K (components z) ≤ rankBound
  orbitIndex : ∀ z, J z → H
  orbitSpace : Z → Submodule K U
  orbit_one : ∀ z, ∃ j, orbitIndex z j = 1
  orbit_zero : ∀ z, ∀ v ∈ orbitSpace z, ∀ h,
    h ∉ Set.range (orbitIndex z) → nativeGradedPointOrbit W hone hprod U point st z v h = 0
  orbit_independent : ∀ z (a : J z → ℂ),
    (∀ v ∈ orbitSpace z, ∑ j,
      a j * nativeGradedPointOrbit W hone hprod U point st z v (orbitIndex z j) = 0) → a = 0
  support : Z → Finset Z
  support_card : ∀ z, (support z).card ≤ Fintype.card H
  determinant_off : ∀ z z', z' ∉ support z → ∀ v : components z, ∀ h,
    nativeGradedPointOrbit W hone hprod U point st z' v h = 0
  realize : ∀ p, U →+ E p
  embedding : P → (K →+* ℂ)
  active : P → Finset Z
  active_card : ∀ p, (active p).card ≤ 1
  realize_off : ∀ p z, z ∉ active p → ∀ v : components z, realize p v = 0
  compare : ∀ p z (v : components z), ‖realize p v‖ ≤ beta * norm (embedding p) v

/-- Construct the actual integral section, preserving its original norm
bound, and derive regularity and joint trace injection on the same graded
section algebra. The chosen component fields and generic fields remain
distinct and are joined only by homogeneous specialization. -/
theorem nativeExists_graded_short_integral_injective_section
    [Fintype I] [DecidableEq I]
    (U : Submodule K Sec) [FiniteDimensional K U]
    (point : Z → R →ₐ[K] ℂ) (st : H → R →ₐ[K] R)
    (J : Z → Type) [∀ z, Fintype (J z)]
    (E : P → Type) [∀ p, SeminormedAddCommGroup (E p)]
    (D : NativeGradedShortSectionData W hone hprod U point st J E)
    (F : Z → Type) [∀ z, Field (F z)] [∀ z, CharZero (F z)]
    (generic : ∀ z, R →+* F z)
    (frame : ∀ z, (I → (F z)ˣ) → R →+* F z)
    (hweight : ∀ z e f, f ∈ W e → ∀ t,
      frame z t f = nativeWeightTorusCharacter (F z) e t * generic z f)
    (hfaithful : ∀ e f, f ∈ W e → (∀ z, generic z f = 0) → f = 0)
    (hspecialize : ∀ z d f, f ∈ W d → generic z f = 0 → point z f = 0)
    (hst : ∀ h d f, f ∈ W d → st h f ∈ W d)
    (h1 : ∀ x, st 1 x = x)
    (hmul : ∀ h h' x, st (h * h') x = st h' (st h x))
    (χ : H →* Kˣ) (e : I → ℤ)
    (hUw : ∀ u : U, ((u : Sec) : R) ∈ W e) :
    let Λ := max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (D.rankBound : ℝ) *
      |(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * D.A)
    ∃ u : U, u ∈ D.lattice ∧
      (∀ p, ‖D.realize p u‖ ≤
        ((2 * Module.finrank ℚ K * D.rankBound : ℕ) : ℝ) *
          ((Fintype.card H : ℝ) ^ 2 * (D.beta * Λ))) ∧
      (Matrix.of fun h g : H =>
        nativeGradedSectionAction W hone hprod st hst (h * g) (u : Sec)).det ∈
        nonZeroDivisors Sec ∧
      ∀ f : Sec,
        (∀ h, ∑ g : H, (((χ g)⁻¹ : Kˣ) : K) •
          nativeGradedSectionAction W hone hprod st hst g
            (f * nativeGradedSectionAction W hone hprod st hst h (u : Sec)) = 0) →
        f = 0 := by
  classical
  dsimp only
  obtain ⟨n, w, c, _hn, _hw, _hc, hu, hdet, hnorm⟩ :=
    nativeExists_component_short_integral_group_section
      D.components D.components_span D.lattice D.componentLattice
      D.componentFG D.component_mem D.norm D.norm_nonneg D.norm_smul D.norm_add
      D.shortSet D.A_nonneg D.beta_nonneg D.short_mem D.short_span D.short_bound
      D.rankBound D.component_rank (nativeGradedPointOrbit W hone hprod U point st)
      J D.orbitIndex D.orbitSpace D.orbit_one D.orbit_zero D.orbit_independent
      D.support D.support_card D.determinant_off E D.realize D.embedding D.active
      D.active_card D.realize_off D.compare
  let u : U := ∑ i, c i • (w i.1 i.2 : U)
  have hpointdet : ∀ z,
      (Matrix.of fun h g : H => point z (st (h * g) ((u : Sec) : R))).det ≠ 0 := by
    intro z
    exact hdet z
  have hgenericdet := nativeGradedSection_groupDet_generic_nonzero_of_component_points
    W hone hprod F generic (fun z => (point z).toRingHom) hspecialize st hst
    e ((u : Sec) : R) (hUw u) hpointdet
  have hreg := nativeGradedSection_groupDet_regular W hone hprod F generic frame
    hweight hfaithful st hst e (u : Sec) (hUw u) hgenericdet
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
  refine ⟨u, hu, hnorm, hreg, ?_⟩
  exact (NativeAlgebraicDescent.twistedTrace_equivariant_and_injective_of_groupDet
    H K Sec (nativeGradedSectionAction W hone hprod st hst) hSec1 hSecMul χ
      (u : Sec) hreg).2.1

end GradedSection

end RHLean.Geometry

end
