import RHLean.Geometry.NativeGradedShortSectionConstruction
import RHLean.Geometry.NativePeterssonMultiplication
import RHLean.Geometry.NativeSectionCostAbsorption

/-!
# The constructed regular section pays Petersson multiplication

The integral section is chosen by the actual short-section constructor.
Its realization is explicitly identified with weighted complex evaluation
at every place and point. The resulting pointwise bound pays every translated
multiplication operator in the weighted Petersson metric. Metric invariance
is itself derived from the measure-preserving level action, its evaluation
identity and the invariance of the original weights.

This is the `homN_mul`, `petAt_mul_le` and `normW_mul_pull_le` mechanism in
`GlobalTheory.ShortDet`, `CardLeOfDetEqZero.lean`, upstream commit
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`. No multiplication-operator bound is
assumed. The actual geometric atlas, short theta spanning family and invariant
measure still have to instantiate the explicit data below.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField MeasureTheory
open scoped BigOperators Matrix

namespace RHLean.Geometry

section GradedSection

variable {I K R Z H : Type}
  [Fintype I] [DecidableEq I]
  [Field K] [NumberField K] [Algebra K ℂ]
  [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R]
  [Fintype Z] [Group H] [Fintype H] [DecidableEq H]
  (W : (I → ℤ) → Submodule K R)
  (hone : (1 : R) ∈ W 0)
  (hprod : ∀ e e', W e * W e' ≤ W (e + e'))

local notation "Sec" => nativeGradedSectionAlgebra W hone hprod

/-- Restrict actual complex evaluation to the constructed section algebra. -/
def nativeGradedEvaluation {Ω : Type} (ev : Ω → R →+* ℂ) : Ω → Sec →+* ℂ :=
  fun x => (ev x).comp (nativeGradedSectionAlgebra W hone hprod).val.toRingHom

/-- The exact pointwise weighted evaluation used by the section constructor. -/
def nativeGradedWeightedRealize (U : Submodule K Sec)
    (ev : R →+* ℂ) (weight : ℝ) : U →+ ℂ where
  toFun f := (weight : ℂ) * ev ((f : Sec) : R)
  map_zero' := by simp
  map_add' f g := by simp [mul_add]

omit [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R] in
/-- The short regular section and every translated Petersson multiplication
bound are constructed on the same witness, with the unchanged section cost. -/
theorem nativeExists_graded_regular_petersson_multiplier
    (U : Submodule K Sec) [FiniteDimensional K U]
    (point : Z → R →ₐ[K] ℂ) (st : H → R →ₐ[K] R)
    (J : Z → Type) [∀ z, Fintype (J z)]
    (Ω : (K →+* ℂ) → Type) [∀ σ, MeasurableSpace (Ω σ)]
    (D : NativeGradedShortSectionData W hone hprod U point st J
      (fun _ : (Σ σ : K →+* ℂ, Ω σ) => ℂ))
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
    (e : I → ℤ) (hUw : ∀ u : U, ((u : Sec) : R) ∈ W e)
    (μ : ∀ σ, Measure (Ω σ)) (ev : ∀ σ, Ω σ → R →+* ℂ)
    (weight weightu : ∀ σ, Ω σ → ℝ)
    (hweight0 : ∀ σ x, 0 ≤ weight σ x)
    (hweightu0 : ∀ σ x, 0 ≤ weightu σ x)
    (hrealize : ∀ σ x u, D.realize ⟨σ, x⟩ u =
      nativeGradedWeightedRealize W hone hprod U (ev σ x) (weightu σ x) u)
    (act : ∀ σ, H → Ω σ → Ω σ)
    (hact : ∀ σ h, MeasurePreserving (act σ h) (μ σ) (μ σ))
    (hweight_act : ∀ σ h x, weight σ (act σ h x) = weight σ x)
    (hweightu_act : ∀ σ h x, weightu σ (act σ h x) = weightu σ x)
    (heval_act : ∀ σ h x f, ev σ x (st h f) = ev σ (act σ h x) f)
    (Vm V : Submodule K Sec)
    (hVm : ∀ h, ∀ f ∈ Vm, nativeGradedSectionAction W hone hprod st hst h f ∈ Vm)
    (hproduct : ∀ u : U, ∀ h, ∀ f ∈ Vm,
      f * nativeGradedSectionAction W hone hprod st hst h (u : Sec) ∈ V)
    (hsource : ∀ σ (f : Vm), MemLp
      (nativeWeightedPointNorm (nativeGradedEvaluation W hone hprod (ev σ))
        (weight σ) (f : Sec)) 2 (μ σ))
    (htarget : ∀ σ (f : V), AEStronglyMeasurable
      (nativeWeightedPointNorm (nativeGradedEvaluation W hone hprod (ev σ))
        (fun x => weight σ x * weightu σ x) (f : Sec)) (μ σ)) :
    let Λ := max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (D.rankBound : ℝ) *
      |(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * D.A)
    let B := ((2 * Module.finrank ℚ K * D.rankBound : ℕ) : ℝ) *
      ((Fintype.card H : ℝ) ^ 2 * (D.beta * Λ))
    ∃ u : U, u ∈ D.lattice ∧
      (Matrix.of fun h g : H =>
        nativeGradedSectionAction W hone hprod st hst (h * g) (u : Sec)).det ∈
        nonZeroDivisors Sec ∧
      (∀ σ x, nativeWeightedPointNorm (nativeGradedEvaluation W hone hprod (ev σ))
        (weightu σ) (u : Sec) x ≤ B) ∧
      ∀ σ h (f : Vm),
        nativePeterssonNorm (μ σ) (nativeGradedEvaluation W hone hprod (ev σ))
            (fun x => weight σ x * weightu σ x)
            ((f : Sec) * nativeGradedSectionAction W hone hprod st hst h (u : Sec)) ≤
          B * nativePeterssonNorm (μ σ) (nativeGradedEvaluation W hone hprod (ev σ))
            (weight σ) (f : Sec) := by
  classical
  dsimp only
  let Λ : ℝ := max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (D.rankBound : ℝ) *
    |(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * D.A)
  let B : ℝ := ((2 * Module.finrank ℚ K * D.rankBound : ℕ) : ℝ) *
    ((Fintype.card H : ℝ) ^ 2 * (D.beta * Λ))
  have hΛ : 0 ≤ Λ := le_trans (by norm_num) (le_max_left _ _)
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (sq_nonneg _) (mul_nonneg D.beta_nonneg hΛ))
  obtain ⟨u, hu, hnorm, hreg, _hinj⟩ :=
    nativeExists_graded_short_integral_injective_section W hone hprod U point st J
      (fun _ : (Σ σ : K →+* ℂ, Ω σ) => ℂ) D F generic frame hweight hfaithful
      hspecialize hst h1 hmul (1 : H →* Kˣ) e hUw
  have hpoint : ∀ σ x,
      nativeWeightedPointNorm (nativeGradedEvaluation W hone hprod (ev σ))
        (weightu σ) (u : Sec) x ≤ B := by
    intro σ x
    have hnormeq : ‖D.realize ⟨σ, x⟩ u‖ =
        nativeWeightedPointNorm (nativeGradedEvaluation W hone hprod (ev σ))
          (weightu σ) (u : Sec) x := by
      rw [hrealize]
      change ‖(weightu σ x : ℂ) * ev σ x ((u : Sec) : R)‖ =
        weightu σ x * ‖ev σ x ((u : Sec) : R)‖
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hweightu0 σ x)]
    rw [← hnormeq]
    exact hnorm ⟨σ, x⟩
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
  have hEval : ∀ σ h x (f : Sec),
      nativeGradedEvaluation W hone hprod (ev σ) x
          (nativeGradedSectionAction W hone hprod st hst h f) =
        nativeGradedEvaluation W hone hprod (ev σ) (act σ h x) f := by
    intro σ h x f
    exact heval_act σ h x f
  refine ⟨u, hu, hreg, hpoint, ?_⟩
  intro σ h f
  apply nativePeterssonNorm_mul_pull_le
    (nativeGradedSectionAction W hone hprod st hst) hSec1 hSecMul Vm V hVm
    (μ σ) (nativeGradedEvaluation W hone hprod (ev σ)) (weight σ) (weightu σ)
    (hweight0 σ) (hweightu0 σ) ?_ ?_ (u : Sec) hB
    (Filter.Eventually.of_forall (hpoint σ)) ?_ ?_ h f (hproduct u h f f.2)
  · intro g f hf
    exact nativePeterssonNorm_pull_eq (μ σ)
      (nativeGradedEvaluation W hone hprod (ev σ)) (weight σ)
      (nativeGradedSectionAction W hone hprod st hst g).toRingHom (act σ g)
      (hact σ g) (hweight_act σ g) (hEval σ g) f
      (hsource σ ⟨f, hf⟩).aestronglyMeasurable
  · intro g f hf
    exact nativePeterssonNorm_pull_eq (μ σ)
      (nativeGradedEvaluation W hone hprod (ev σ))
      (fun x => weight σ x * weightu σ x)
      (nativeGradedSectionAction W hone hprod st hst g).toRingHom (act σ g)
      (hact σ g) (fun x => by rw [hweight_act, hweightu_act]) (hEval σ g) f
      (htarget σ ⟨f, hf⟩)
  · intro f hf
    exact (hsource σ ⟨f, hf⟩).ne
  · intro f hf
    have hp := hproduct u 1 f hf
    rw [hSec1] at hp
    exact htarget σ ⟨f * (u : Sec), hp⟩


omit [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R] in
/-- Feed the SAME constructed section and its proved Petersson multiplier
bound into all-place descent. The free section and free operator-norm premise
are both removed. The complete finite section cost is derived from the
original separate degree, discriminant, rank, theta size and comparison
scales. The actual short theta family, rank and covolume suppliers remain
separate geometric obligations. -/
theorem nativeAllPlaceDescent_of_constructed_petersson_section
    [IsTotallyComplex K]
    (U : Submodule K Sec) [FiniteDimensional K U]
    (point : Z → R →ₐ[K] ℂ) (st : H → R →ₐ[K] R)
    (J : Z → Type) [∀ z, Fintype (J z)]
    (Ω : (K →+* ℂ) → Type) [∀ σ, MeasurableSpace (Ω σ)]
    (D : NativeGradedShortSectionData W hone hprod U point st J
      (fun _ : (Σ σ : K →+* ℂ, Ω σ) => ℂ))
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
    (e : I → ℤ) (hUw : ∀ u : U, ((u : Sec) : R) ∈ W e)
    (μ : ∀ σ, Measure (Ω σ)) (ev : ∀ σ, Ω σ → R →+* ℂ)
    (weight weightu : ∀ σ, Ω σ → ℝ)
    (hweight0 : ∀ σ x, 0 ≤ weight σ x)
    (hweightu0 : ∀ σ x, 0 ≤ weightu σ x)
    (hrealize : ∀ σ x u, D.realize ⟨σ, x⟩ u =
      nativeGradedWeightedRealize W hone hprod U (ev σ x) (weightu σ x) u)
    (act : ∀ σ, H → Ω σ → Ω σ)
    (hact : ∀ σ h, MeasurePreserving (act σ h) (μ σ) (μ σ))
    (hweight_act : ∀ σ h x, weight σ (act σ h x) = weight σ x)
    (hweightu_act : ∀ σ h x, weightu σ (act σ h x) = weightu σ x)
    (heval_act : ∀ σ h x f, ev σ x (st h f) = ev σ (act σ h x) f)
    (Vm V : Submodule K Sec)
    (hVm : ∀ h, ∀ f ∈ Vm, nativeGradedSectionAction W hone hprod st hst h f ∈ Vm)
    (hproduct : ∀ u : U, ∀ h, ∀ f ∈ Vm,
      f * nativeGradedSectionAction W hone hprod st hst h (u : Sec) ∈ V)
    (hsource : ∀ σ (f : Vm), MemLp
      (nativeWeightedPointNorm (nativeGradedEvaluation W hone hprod (ev σ))
        (weight σ) (f : Sec)) 2 (μ σ))
    (htarget : ∀ σ (f : V), AEStronglyMeasurable
      (nativeWeightedPointNorm (nativeGradedEvaluation W hone hprod (ev σ))
        (fun x => weight σ x * weightu σ x) (f : Sec)) (μ σ))
    (χ : H →* Kˣ) (Vp N : Submodule K Sec)
    [FiniteDimensional K Vm] [FiniteDimensional K V] [FiniteDimensional K Vp]
    (hNV : N ≤ V)
    (hV : ∀ h, ∀ f ∈ V, nativeGradedSectionAction W hone hprod st hst h f ∈ V)
    (hplus : ∀ u : U, ∀ h, ∀ f ∈ V,
      f * nativeGradedSectionAction W hone hprod st hst h (u : Sec) ∈ Vp)
    (hN : ∀ f, f ∈ N ↔ f ∈ V ∧ ∀ h,
      nativeGradedSectionAction W hone hprod st hst h f = ((χ h : Kˣ) : K) • f)
    (A : Submodule (𝓞 K) Vm) (L : Submodule (𝓞 K) V)
    (Lu : Submodule (𝓞 K) Sec)
    (hLu_mem : ∀ u : U, u ∈ D.lattice → (u : Sec) ∈ Lu)
    (hLu : ∀ h, ∀ f ∈ Lu, nativeGradedSectionAction W hone hprod st hst h f ∈ Lu)
    (hIntegral : ∀ f : Vm, f ∈ A → ∀ v ∈ Lu,
      (f : Sec) * v ∈ L.map (V.subtype.restrictScalars (𝓞 K)))
    (hL : ∀ h, ∀ f ∈ L,
      nativeWeightAction (nativeGradedSectionAction W hone hprod st hst) V hV h f ∈ L)
    (NA : (K →+* ℂ) → Vm → ℝ) (NV : (K →+* ℂ) → V → ℝ)
    (hNAeq : ∀ σ (f : Vm), NA σ f =
      nativePeterssonNorm (μ σ) (nativeGradedEvaluation W hone hprod (ev σ))
        (weight σ) (f : Sec))
    (hNVeq : ∀ σ (f : V), NV σ f =
      nativePeterssonNorm (μ σ) (nativeGradedEvaluation W hone hprod (ev σ))
        (fun x => weight σ x * weightu σ x) (f : Sec))
    (hNVsmul : ∀ σ (a : K) v, NV σ (a • v) = ‖σ a‖ * NV σ v)
    (hNVadd : ∀ σ v w, NV σ (v + w) ≤ NV σ v + NV σ w)
    (hGramA : AlpogeAllPlace.GlobalTheory.AllWt.HasGram NA)
    (hGramB : AlpogeAllPlace.GlobalTheory.AllWt.HasGram (nativeEigenNorm hNV NV))
    (hAFG : A.FG) (hBFG : (nativeEigenLattice hNV L).FG) (hA0 : A ≠ ⊥)
    {z b Λ δ t o S Crank Ctheta Csup : ℝ}
    (hCrank : 0 ≤ Crank) (hCtheta : 0 ≤ Ctheta) (hCsup : 0 ≤ Csup)
    (hdegree : Real.log (Module.finrank ℚ K : ℝ) ≤ o)
    (hdisc : Real.log |(NumberField.discr K : ℝ)| ≤ (Module.finrank ℚ K : ℝ) * o)
    (ho : o ≤ 391 * z ^ 2)
    (hrankCost : Real.log (D.rankBound : ℝ) ≤ Crank * z ^ 3)
    (hsize : S ≤ z ^ 5)
    (htheta : Real.log D.A ≤ Ctheta * (z ^ 3 * S + z ^ 5))
    (hsup : D.beta ≤ Real.exp (Csup * z ^ 3))
    (hqz : Real.log (Fintype.card H : ℝ) ≤ 45 * z ^ 2)
    (hz : 2 * (3 * (2000 + Crank + Ctheta) + 240 + Csup) + 200 ≤ z)
    (hb : z ^ 12 ≤ b)
    (hshort : ∃ s : Set N,
      s ⊆ (nativeEigenLattice hNV L : Set N) ∧
      (∀ y ∈ s, ∀ σ, nativeEigenNorm hNV NV σ y ≤ Real.exp Λ) ∧
      (nativeEigenLattice hNV L : Set N) ⊆ (Submodule.span K s : Set N))
    (hΛ : 0 ≤ Λ) (hδ : 0 ≤ δ)
    (hrank : (Module.finrank K Vp : ℝ) ≤
      (1 + δ) * AlpogeAllPlace.Formalism.HN.rkK A)
    (ht : t ≤ AlpogeAllPlace.GlobalTheory.AllWt.slope_sq NA A - 2 * b) :
    t - δ * (|t| + 2 * Λ) ≤
      AlpogeAllPlace.GlobalTheory.AllWt.slope_sq
        (nativeEigenNorm hNV NV) (nativeEigenLattice hNV L) := by
  let C0 : ℝ := 3 * (2000 + Crank + Ctheta) + 240 + Csup
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hz' : 2 * C0 + 200 ≤ z := hz
  have hz1 : 1 ≤ z := by linarith only [hC0, hz']
  have hsectionCost := nativeShortSectionCost_le_exp_of_source_scales K H D.rankBound
    D.A_nonneg D.beta_nonneg hz1 hCrank hCtheta hCsup hdegree hdisc ho hrankCost
    hsize htheta hsup (by nlinarith only [hqz, sq_nonneg z])
  obtain ⟨u, hu, hreg, _hpoint, hmult⟩ :=
    nativeExists_graded_regular_petersson_multiplier W hone hprod U point st J Ω D
      F generic frame hweight hfaithful hspecialize hst h1 hmul e hUw
      μ ev weight weightu hweight0 hweightu0 hrealize act hact hweight_act hweightu_act
      heval_act Vm V hVm hproduct hsource htarget
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
  have hNV0 : ∀ σ v, 0 ≤ NV σ v := by
    intro σ v
    rw [hNVeq]
    exact ENNReal.toReal_nonneg
  have hNVinv : ∀ h σ v,
      NV σ (nativeWeightAction (nativeGradedSectionAction W hone hprod st hst) V hV h v) =
        NV σ v := by
    intro h σ v
    rw [hNVeq, hNVeq]
    exact nativePeterssonNorm_pull_eq (μ σ)
      (nativeGradedEvaluation W hone hprod (ev σ))
      (fun x => weight σ x * weightu σ x)
      (nativeGradedSectionAction W hone hprod st hst h).toRingHom (act σ h)
      (hact σ h) (fun x => by rw [hweight_act, hweightu_act])
      (fun x f => heval_act σ h x f) (v : Sec) (htarget σ v)
  have hM : ∀ h σ f,
      NV σ (nativeWeightMultiply (nativeGradedSectionAction W hone hprod st hst)
          (u : Sec) Vm V (hproduct u) h f) ≤ Real.exp (C0 * z ^ 9) * NA σ f := by
    intro h σ f
    rw [hNVeq, hNAeq]
    exact (hmult σ h f).trans
      (mul_le_mul_of_nonneg_right hsectionCost ENNReal.toReal_nonneg)
  exact nativeAllPlaceDescent_of_regular_groupDet
    (nativeGradedSectionAction W hone hprod st hst) hSec1 hSecMul χ (u : Sec) hreg
    Vm V Vp N hNV hV (hproduct u) (hplus u) hN A L Lu (hLu_mem u hu) hLu hIntegral hL
    NA NV hNV0 hNVsmul hNVadd hNVinv hGramA hGramB hAFG hBFG hA0
    hC0 hqz hz' hb hM hshort hΛ hδ hrank ht

end GradedSection

end RHLean.Geometry

end
