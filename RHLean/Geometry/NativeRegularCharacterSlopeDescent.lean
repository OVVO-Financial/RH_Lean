import RHLean.Geometry.NativeAllPlaceDescent
import RHLean.Geometry.NativeCharacterTraceMaps
import RHLean.Geometry.NativeComponentRegularity
import RHLean.Geometry.NativeTwistedTraceRank

/-!
# The same regular section constructs the all-place slope descent

The maps in this theorem are built from the supplied section `u`:
multiply by `st h u`, take the original unnormalized character trace, and
view the result in the actual character eigenspace. Their integrality,
joint injectivity, collective q^3 norm cost, and opposite rank injection
are proved for these same maps. The all-place descent theorem then applies
to the same integral lattices and the restricted target metric.

The inputs are finite geometric data: component evaluations, reduced section
algebra, weight subspaces, integral product closure, multiplication norm,
short target spanning vectors, and the plus/minus near-rank comparison.
No arbitrary map family or unproved joint-map norm estimate is supplied.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField
open scoped BigOperators Matrix
open RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt
open RHLean.Geometry.AlpogeAllPlace.Formalism.HN (rkK)

namespace RHLean.Geometry

def nativeWeightAction {H K R : Type} [Field K] [CommRing R] [Algebra K R]
    (st : H → R →ₐ[K] R) (V : Submodule K R)
    (hV : ∀ h, ∀ x ∈ V, st h x ∈ V) (h : H) : V →ₗ[K] V :=
  (st h).toLinearMap.restrict (hV h)

def nativeWeightMultiply {H K R : Type} [Field K] [CommRing R] [Algebra K R]
    (st : H → R →ₐ[K] R) (u : R) (Vm V : Submodule K R)
    (hm : ∀ h, ∀ x ∈ Vm, x * st h u ∈ V) (h : H) : Vm →ₗ[K] V where
  toFun f := ⟨(f : R) * st h u, hm h f f.2⟩
  map_add' f g := by
    apply Subtype.ext
    simp [add_mul]
  map_smul' a f := by
    apply Subtype.ext
    simp [smul_mul_assoc]

def nativeEigenNorm {K R : Type} [Field K] [CommRing R] [Algebra K R]
    {V N : Submodule K R} (hNV : N ≤ V)
    (NV : (K →+* ℂ) → V → ℝ) : (K →+* ℂ) → N → ℝ :=
  fun σ x => NV σ (Submodule.inclusion hNV x)

def nativeEigenLattice {K R : Type} [Field K] [NumberField K]
    [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] {V N : Submodule K R}
    (hNV : N ≤ V) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) N :=
  L.comap ((Submodule.inclusion hNV).restrictScalars (𝓞 K))

/-- Apply the original all-place slope descent to maps constructed from the
same section, character, weight spaces and integral lattices. -/
theorem nativeAllPlaceDescent_of_regular_character_section
    {H K R : Type} [Group H] [Fintype H] [DecidableEq H]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] [IsReduced R]
    (st : H → R →ₐ[K] R)
    (h1 : ∀ x, st 1 x = x)
    (hmul : ∀ h h' x, st (h * h') x = st h' (st h x))
    (χ : H →* Kˣ) (u : R)
    (F : minimalPrimes R → Type) [∀ p, CommRing (F p)]
    (ev : ∀ p, R →+* F p)
    (hcomponent : ∀ p, p.val ≤ RingHom.ker (ev p))
    (hdet : ∀ p, (Matrix.of fun h g : H => ev p (st (h * g) u)).det ≠ 0)
    (Vm V Vp N : Submodule K R)
    [FiniteDimensional K Vm] [FiniteDimensional K V] [FiniteDimensional K Vp]
    (hNV : N ≤ V)
    (hV : ∀ h, ∀ x ∈ V, st h x ∈ V)
    (hm : ∀ h, ∀ x ∈ Vm, x * st h u ∈ V)
    (hp : ∀ h, ∀ x ∈ V, x * st h u ∈ Vp)
    (hN : ∀ x, x ∈ N ↔ x ∈ V ∧ ∀ h, st h x = ((χ h : Kˣ) : K) • x)
    (A : Submodule (𝓞 K) Vm) (L : Submodule (𝓞 K) V)
    (Lu : Submodule (𝓞 K) R) (hu : u ∈ Lu)
    (hLu : ∀ h, ∀ v ∈ Lu, st h v ∈ Lu)
    (hproduct : ∀ f : Vm, f ∈ A → ∀ v ∈ Lu,
      (f : R) * v ∈ L.map (V.subtype.restrictScalars (𝓞 K)))
    (hL : ∀ h, ∀ v ∈ L, nativeWeightAction st V hV h v ∈ L)
    (NA : (K →+* ℂ) → Vm → ℝ)
    (NV : (K →+* ℂ) → V → ℝ)
    (hNV0 : ∀ σ v, 0 ≤ NV σ v)
    (hNVsmul : ∀ σ (a : K) v, NV σ (a • v) = ‖σ a‖ * NV σ v)
    (hNVadd : ∀ σ v w, NV σ (v + w) ≤ NV σ v + NV σ w)
    (hNVinv : ∀ h σ v, NV σ (nativeWeightAction st V hV h v) = NV σ v)
    (hGramA : HasGram NA) (hGramB : HasGram (nativeEigenNorm hNV NV))
    (hAFG : A.FG) (hBFG : (nativeEigenLattice hNV L).FG) (hA0 : A ≠ ⊥)
    {C z b Λ δ t : ℝ} (hC : 0 ≤ C)
    (hqz : Real.log (Fintype.card H : ℝ) ≤ 45 * z ^ 2)
    (hz : 2 * C + 200 ≤ z) (hb : z ^ 12 ≤ b)
    (hM : ∀ h σ f, NV σ (nativeWeightMultiply st u Vm V hm h f) ≤
      Real.exp (C * z ^ 9) * NA σ f)
    (hshort : ∃ s : Set N,
      s ⊆ (nativeEigenLattice hNV L : Set N) ∧
      (∀ y ∈ s, ∀ σ, nativeEigenNorm hNV NV σ y ≤ Real.exp Λ) ∧
      (nativeEigenLattice hNV L : Set N) ⊆ (Submodule.span K s : Set N))
    (hΛ : 0 ≤ Λ) (hδ : 0 ≤ δ)
    (hrank : (Module.finrank K Vp : ℝ) ≤ (1 + δ) * rkK A)
    (ht : t ≤ slope_sq NA A - 2 * b) :
    t - δ * (|t| + 2 * Λ) ≤
      slope_sq (nativeEigenNorm hNV NV) (nativeEigenLattice hNV L) := by
  classical
  have hreg : (Matrix.of fun h g : H => st (h * g) u).det ∈
      nonZeroDivisors R :=
    nativeMatrixDet_regular_of_component_evaluations F ev hcomponent _ hdet
  obtain ⟨hTr, hPhi, _hPsi⟩ :=
    NativeAlgebraicDescent.twistedTrace_equivariant_and_injective_of_groupDet
      H K R st h1 hmul χ u hreg
  have hmem : ∀ (f : Vm) (h : H),
      ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g ((f : R) * st h u) ∈ N := fun f h =>
    (hN _).2 ⟨V.sum_mem fun g _ => V.smul_mem _
      (hV g _ (hm h _ f.2)), fun g => hTr _ g⟩
  let φH : H → Vm →ₗ[K] N := fun h =>
    { toFun := fun f => ⟨_, hmem f h⟩
      map_add' := fun f f' => by
        apply Subtype.ext
        simp only [Submodule.coe_add, add_mul, map_add, smul_add, Finset.sum_add_distrib]
      map_smul' := fun a f => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, smul_mul_assoc, map_smul,
          RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun g _ => smul_comm _ _ _ }
  have hφ (h : H) (f : Vm) :
      Submodule.inclusion hNV (φH h f) =
        nativeCharacterTrace (nativeWeightAction st V hV) χ
          (nativeWeightMultiply st u Vm V hm h f) := by
    apply Subtype.ext
    simp [φH, nativeCharacterTrace_apply, nativeWeightAction, nativeWeightMultiply]
  have hIntegral (h : H) (f : Vm) (hf : f ∈ A) :
      nativeWeightMultiply st u Vm V hm h f ∈ L := by
    obtain ⟨v, hv, heq⟩ := (Submodule.mem_map).1
      (hproduct f hf (st h u) (hLu h u hu))
    have hv' : v = nativeWeightMultiply st u Vm V hm h f := Subtype.ext heq
    exact hv' ▸ hv
  have hφIntegral (h : H) (f : Vm) (hf : f ∈ A) :
      φH h f ∈ nativeEigenLattice hNV L := by
    change Submodule.inclusion hNV (φH h f) ∈ L
    rw [hφ]
    exact nativeCharacterTrace_mem_lattice (nativeWeightAction st V hV) χ L hL
      (hIntegral h f hf)
  have hφInj : ∀ f : Vm, (∀ h, φH h f = 0) → f = 0 := by
    intro f hf
    apply Subtype.ext
    exact hPhi f fun h => congrArg Subtype.val (hf h)
  have hφNorm : ∀ σ f, ∑ h : H, nativeEigenNorm hNV NV σ (φH h f) ^ 2 ≤
      Real.exp (2 * b) * NA σ f ^ 2 := by
    intro σ f
    simpa only [nativeEigenNorm, hφ, LinearMap.comp_apply] using
      nativeCharacterTrace_jointNorm_paid (nativeWeightAction st V hV) χ
        (nativeWeightMultiply st u Vm V hm) NA NV hNV0 hNVsmul hNVadd hNVinv
        hC hqz hz hb hM σ f
  haveI : FiniteDimensional K N := Submodule.finiteDimensional_of_le hNV
  have hBdim : rkK (nativeEigenLattice hNV L) ≤ Module.finrank K N := by
    exact Submodule.finrank_le _
  have hRank := (NativeAlgebraicDescent.finrank_le_card_mul_finrank_eigenspace_le
    H K R st h1 hmul χ u hreg Vm V Vp N hV hm hp hN).2
  have hRankB : (Fintype.card H : ℝ) * rkK (nativeEigenLattice hNV L) ≤
      (1 + δ) * rkK A := by
    have hnat : Fintype.card H * rkK (nativeEigenLattice hNV L) ≤
        Module.finrank K Vp :=
      (Nat.mul_le_mul_left _ hBdim).trans hRank
    exact (by exact_mod_cast hnat : (Fintype.card H : ℝ) *
      rkK (nativeEigenLattice hNV L) ≤ (Module.finrank K Vp : ℝ)).trans hrank
  let e : Fin (Fintype.card H) ≃ H := (Fintype.equivFin H).symm
  let φ : Fin (Fintype.card H) → Vm →ₗ[K] N := fun i => φH (e i)
  apply nativeAllPlaceDescent K Vm N NA (nativeEigenNorm hNV NV) A
    (nativeEigenLattice hNV L) (Fintype.card H) φ b Λ δ t
    hGramA hGramB hAFG hBFG hA0
    (fun i f hf => hφIntegral (e i) f hf) ?_ ?_
    hshort hΛ hδ hRankB ht
  · intro f hf
    apply hφInj f
    intro h
    simpa only [φ, Equiv.apply_symm_apply] using hf (e.symm h)
  · intro σ f
    change (∑ i, nativeEigenNorm hNV NV σ (φH (e i) f) ^ 2) ≤ _
    rw [e.sum_comp]
    exact hφNorm σ f

end RHLean.Geometry

