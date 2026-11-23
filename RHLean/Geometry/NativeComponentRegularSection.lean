import RHLean.Geometry.NativeAllPlaceShortGenerators
import RHLean.Geometry.NativeGroupDeterminant

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# One dependent construction of a short integral regular section

The component lattices, all-embedding norms, finite orbit evaluations, and
pointwise realizations below refer to the same ambient vector space. We first
construct short generators in each component lattice, then construct the
regular group section from those very generators.

The final pointwise bound is
`(2 * d * r) * q^2 * β * max 1 (d^4 * r * |Disc K|^(1/d) * A)`,
where `d = [K : ℚ]`, `r` bounds each component rank, and `q = |S|`.
There is no total-component factor. Integral membership is over `O_K`, and
the generator norm hypotheses and conclusions quantify over every embedding.

The remaining geometric inputs are explicit: the component decomposition and
lattices, an actual short spanning family in each component, the actual orbit
evaluation independence, support locality, and the pointwise/Petersson norm
comparison. Neither an arithmetic cancellation bound nor a regular seed is
assumed.
-/

noncomputable section

open NumberField
open scoped BigOperators

namespace RHLean.Geometry

/-- Assemble the actual component short generators and the regular-section
algorithm in one dependent witness, retaining the all-place normalization. -/
theorem nativeExists_component_short_integral_group_section
    {K V Z S P : Type} [Field K] [NumberField K] [Algebra K ℂ]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    [Fintype Z] [Group S] [Fintype S] [DecidableEq S]
    (C : Z → Submodule K V) (hcomponents : iSup C = ⊤)
    (L : Submodule (𝓞 K) V)
    (LC : ∀ z, Submodule (𝓞 K) (C z))
    (hLC : ∀ z, (LC z).FG)
    (hmem : ∀ z (v : C z), v ∈ LC z → (v : V) ∈ L)
    (N : (K →+* ℂ) → V → ℝ)
    (hN0 : ∀ σ v, 0 ≤ N σ v)
    (hNsmul : ∀ σ (a : K) v, N σ (a • v) = ‖σ a‖ * N σ v)
    (hNadd : ∀ σ v v', N σ (v + v') ≤ N σ v + N σ v')
    (s : ∀ z, Set (C z)) {A β : ℝ} (hA0 : 0 ≤ A) (hβ : 0 ≤ β)
    (hsL : ∀ z, s z ⊆ LC z)
    (hspan : ∀ z, Submodule.span K (s z) = ⊤)
    (hshort : ∀ z v, v ∈ s z → ∀ σ, N σ (v : V) ≤ A)
    (rmax : ℕ) (hrank : ∀ z, Module.finrank K (C z) ≤ rmax)
    (ev : Z → V →ₗ[K] (S → ℂ))
    (J : Z → Type) [∀ z, Fintype (J z)]
    (r : ∀ z, J z → S) (W : Z → Submodule K V)
    (h1 : ∀ z, ∃ j, r z j = 1)
    (h2 : ∀ z, ∀ v ∈ W z, ∀ h, h ∉ Set.range (r z) → ev z v h = 0)
    (h3 : ∀ z (a : J z → ℂ),
      (∀ v ∈ W z, ∑ j, a j * ev z v (r z j) = 0) → a = 0)
    (support : Z → Finset Z)
    (hsupport : ∀ z, (support z).card ≤ Fintype.card S)
    (hdetOff : ∀ z z', z' ∉ support z → ∀ v : C z, ∀ h, ev z' v h = 0)
    (E : P → Type) [∀ p, SeminormedAddCommGroup (E p)]
    (realize : ∀ p, V →+ E p)
    (σ : P → (K →+* ℂ)) (active : P → Finset Z)
    (hactive : ∀ p, (active p).card ≤ 1)
    (hrealizeOff : ∀ p z, z ∉ active p → ∀ v : C z, realize p v = 0)
    (hcompare : ∀ p z (v : C z), ‖realize p v‖ ≤ β * N (σ p) v) :
    let Λ := max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (rmax : ℝ) *
      |(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A)
    ∃ (n : Z → ℕ) (w : ∀ z, Fin (n z) → C z)
      (c : (Σ z, Fin (n z)) → ℕ),
      (∀ z, n z ≤ 2 * Module.finrank ℚ K * rmax) ∧
      (∀ z i, w z i ∈ LC z) ∧
      (∀ i, c i ≤ Fintype.card S ^ 2) ∧
      let u : V := ∑ i, c i • (w i.1 i.2 : V)
      u ∈ L ∧
      (∀ z, (Matrix.of fun h g : S => ev z u (h * g)).det ≠ 0) ∧
      ∀ p, ‖realize p u‖ ≤
        ((2 * Module.finrank ℚ K * rmax : ℕ) : ℝ) *
          ((Fintype.card S : ℝ) ^ 2 * (β * Λ)) := by
  classical
  dsimp only
  let Λ : ℝ := max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (rmax : ℝ) *
    |(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A)
  have hΛ0 : 0 ≤ Λ := le_trans (by norm_num) (le_max_left _ _)
  choose n w B hw hB hn using fun z =>
    NativeNumberFieldLattice.exists_isShortGen_of_short_span K (C z)
      (fun σ v => N σ (v : V)) (LC z) (s z) A (hLC z)
      (fun σ v => hN0 σ v) (fun σ a v => hNsmul σ a v)
      (fun σ v v' => hNadd σ v v') (hsL z) (hspan z) (hshort z)
  have hBΛ : ∀ z, B z ≤ Λ := fun z => (hB z).trans (max_le_max le_rfl (by
    apply mul_le_mul_of_nonneg_right _ hA0
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hrank z) (by positivity)))
  have hnmax : ∀ z, n z ≤ 2 * Module.finrank ℚ K * rmax := fun z =>
    (hn z).trans (Nat.mul_le_mul_left _ (hrank z))
  have hwmem : ∀ z i, w z i ∈ LC z := fun z i =>
    ((hw z).gen _).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hwspan : ∀ z, Submodule.span K (Set.range (w z)) = ⊤ := by
    intro z
    apply eq_top_iff.2
    rw [← hspan z, Submodule.span_le]
    intro v hv
    have hz : Submodule.span ℤ (Set.range (w z)) ≤
        (Submodule.span K (Set.range (w z))).restrictScalars ℤ :=
      Submodule.span_le.2 fun _ h => Submodule.subset_span h
    exact hz (((hw z).gen v).1 (hsL z hv))
  let θ : (Σ z, Fin (n z)) → V := fun i => w i.1 i.2
  have hθL : ∀ i, θ i ∈ L := fun i => hmem i.1 _ (hwmem i.1 i.2)
  have hθspan : Submodule.span K (Set.range θ) = ⊤ := by
    apply eq_top_iff.2
    rw [← hcomponents]
    apply iSup_le
    intro z v hv
    have hle : Submodule.span K (Set.range (w z)) ≤
        (Submodule.span K (Set.range θ)).comap (C z).subtype :=
      Submodule.span_le.2 (by
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨⟨z, i⟩, rfl⟩)
    have hx : (⟨v, hv⟩ : C z) ∈ Submodule.span K (Set.range (w z)) := by
      rw [hwspan z]
      exact Submodule.mem_top
    exact hle hx
  let act : P → Finset (Σ z, Fin (n z)) := fun p => (active p).sigma fun _ => Finset.univ
  have hact : ∀ p, ((act p).card : ℝ) ≤
      ((2 * Module.finrank ℚ K * rmax : ℕ) : ℝ) := by
    intro p
    have hnat : (act p).card ≤ 2 * Module.finrank ℚ K * rmax := by
      rw [Finset.card_sigma]
      simp only [Finset.card_univ, Fintype.card_fin]
      calc
        ∑ z ∈ active p, n z ≤
            ∑ _z ∈ active p, 2 * Module.finrank ℚ K * rmax :=
          Finset.sum_le_sum fun z _ => hnmax z
        _ = (active p).card * (2 * Module.finrank ℚ K * rmax) := by simp
        _ ≤ 1 * (2 * Module.finrank ℚ K * rmax) :=
          Nat.mul_le_mul_right _ (hactive p)
        _ = 2 * Module.finrank ℚ K * rmax := one_mul _
    exact_mod_cast hnat
  have hactOff : ∀ p i, i ∉ act p → realize p (θ i) = 0 := by
    intro p i hi
    apply hrealizeOff p i.1
    intro hz
    exact hi (Finset.mem_sigma.2 ⟨hz, Finset.mem_univ _⟩)
  have hθshort : ∀ p i, ‖realize p (θ i)‖ ≤ β * Λ := fun p i =>
    (hcompare p i.1 (w i.1 i.2)).trans
      (mul_le_mul_of_nonneg_left (((hw i.1).le i.2 (σ p)).trans (hBΛ i.1)) hβ)
  obtain ⟨c, hc, hL, hreg, hnorm⟩ := nativeExists_short_integral_group_section ev J r W
    h1 h2 h3 L θ hθL hθspan (fun i => support i.1) (fun i => hsupport i.1)
    (fun i z hz h => hdetOff i.1 z hz (w i.1 i.2) h)
    E realize act (mul_nonneg hβ hΛ0) hact hactOff hθshort
  exact ⟨n, w, c, hnmax, hwmem, hc, hL, hreg, hnorm⟩

end RHLean.Geometry

