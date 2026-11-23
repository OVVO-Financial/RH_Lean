import RHLean.Geometry.NativeAllPlaceEigenGenerators
import RHLean.Geometry.NativeDescentCostPayment

/-!
# Integral character-trace maps and their complete collective norm cost

These are the unnormalized maps used in the regular-section descent. Finite
character coefficients are integral and have norm one at every embedding;
the trace costs `q`, and the joint sum of `q` squared norms costs `q^3`.
The exponential payment is then derived in the original size regime.

The algebraic injectivity and opposite rank injection are independently proved
in NativeTwistedTraceDescent and NativeTwistedTraceRank, with the identical
trace formula and the same regular section. No smaller multiplicity cost is
asserted here.
-/

set_option autoImplicit false

noncomputable section
open NumberField
open scoped BigOperators

namespace RHLean.Geometry

def nativeCharacterTrace {H K V : Type} [Group H] [Fintype H]
    [Field K] [AddCommGroup V] [Module K V]
    (st : H → V →ₗ[K] V) (χ : H →* Kˣ) : V →ₗ[K] V :=
  ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g

theorem nativeCharacterTrace_apply {H K V : Type} [Group H] [Fintype H]
    [Field K] [AddCommGroup V] [Module K V]
    (st : H → V →ₗ[K] V) (χ : H →* Kˣ) (v : V) :
    nativeCharacterTrace st χ v = ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g v := by
  simp [nativeCharacterTrace, LinearMap.sum_apply]

/-- The actual trace preserves the integral lattice without dividing by q. -/
theorem nativeCharacterTrace_mem_lattice {H K V : Type} [Group H] [Fintype H]
    [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (st : H → V →ₗ[K] V) (χ : H →* Kˣ) (L : Submodule (𝓞 K) V)
    (hL : ∀ g, ∀ v ∈ L, st g v ∈ L) {v : V} (hv : v ∈ L) :
    nativeCharacterTrace st χ v ∈ L := by
  rw [nativeCharacterTrace_apply]
  apply L.sum_mem
  intro g _
  rw [← map_inv]
  let a : 𝓞 K := ⟨_, (nativeFiniteCharacter_integral_norm_one χ g⁻¹).1⟩
  have hmem := L.smul_mem a (hL g v hv)
  rwa [← algebraMap_smul K a] at hmem

/-- Every embedding has the exact q-fold unnormalized trace cost. -/
theorem nativeCharacterTrace_norm_le {H K V : Type} [Group H] [Fintype H]
    [Field K] [AddCommGroup V] [Module K V]
    (st : H → V →ₗ[K] V) (χ : H →* Kˣ)
    (N : (K →+* ℂ) → V → ℝ)
    (hsm : ∀ σ (a : K) v, N σ (a • v) = ‖σ a‖ * N σ v)
    (hadd : ∀ σ v w, N σ (v + w) ≤ N σ v + N σ w)
    (hinv : ∀ g σ v, N σ (st g v) = N σ v)
    (σ : K →+* ℂ) (v : V) :
    N σ (nativeCharacterTrace st χ v) ≤ (Fintype.card H : ℝ) * N σ v := by
  classical
  have hzero : N σ 0 = 0 := by simpa using hsm σ 0 0
  have hsum : ∀ (T : Finset H) (f : H → V),
      N σ (∑ g ∈ T, f g) ≤ ∑ g ∈ T, N σ (f g) := by
    intro T f
    induction T using Finset.induction_on with
    | empty => simp [hzero]
    | insert g T hg ih =>
        rw [Finset.sum_insert hg, Finset.sum_insert hg]
        exact (hadd σ _ _).trans (add_le_add le_rfl ih)
  rw [nativeCharacterTrace_apply]
  calc
    _ ≤ ∑ g : H, N σ ((((χ g)⁻¹ : Kˣ) : K) • st g v) := hsum _ _
    _ = ∑ _g : H, N σ v := by
      apply Finset.sum_congr rfl
      intro g _
      rw [hsm, hinv, ← map_inv,
        (nativeFiniteCharacter_integral_norm_one χ g⁻¹).2 σ, one_mul]
    _ = (Fintype.card H : ℝ) * N σ v := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Construct the q maps and derive, rather than assume, their collective
square-norm bill from the multiplication bound and the invariant metric. -/
theorem nativeCharacterTrace_jointNorm_le {H K A V : Type}
    [Group H] [Fintype H] [Field K]
    [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
    (st : H → V →ₗ[K] V) (χ : H →* Kˣ)
    (m : H → A →ₗ[K] V) (NA : (K →+* ℂ) → A → ℝ)
    (N : (K →+* ℂ) → V → ℝ)
    (hN : ∀ σ v, 0 ≤ N σ v)
    (hsm : ∀ σ (a : K) v, N σ (a • v) = ‖σ a‖ * N σ v)
    (hadd : ∀ σ v w, N σ (v + w) ≤ N σ v + N σ w)
    (hinv : ∀ g σ v, N σ (st g v) = N σ v)
    {B : ℝ} (hm : ∀ h σ f, N σ (m h f) ≤ B * NA σ f)
    (σ : K →+* ℂ) (f : A) :
    (∑ h : H, N σ ((nativeCharacterTrace st χ).comp (m h) f) ^ 2) ≤
      (Fintype.card H : ℝ) ^ 3 * B ^ 2 * NA σ f ^ 2 := by
  have hc : ∀ h, N σ ((nativeCharacterTrace st χ).comp (m h) f) ≤
      (Fintype.card H : ℝ) * (B * NA σ f) := by
    intro h
    exact (nativeCharacterTrace_norm_le st χ N hsm hadd hinv σ (m h f)).trans
      (mul_le_mul_of_nonneg_left (hm h σ f) (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ _h : H, ((Fintype.card H : ℝ) * (B * NA σ f)) ^ 2 :=
      Finset.sum_le_sum fun h _ => pow_le_pow_left₀ (hN σ _) (hc h) 2
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Apply the actual map-count absorption to these constructed maps on the
same source vector, with the original `exp(C*z^9)` multiplication budget. -/
theorem nativeCharacterTrace_jointNorm_paid {H K A V : Type}
    [Group H] [Fintype H] [Field K]
    [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
    (st : H → V →ₗ[K] V) (χ : H →* Kˣ)
    (m : H → A →ₗ[K] V) (NA : (K →+* ℂ) → A → ℝ)
    (N : (K →+* ℂ) → V → ℝ)
    (hN : ∀ σ v, 0 ≤ N σ v)
    (hsm : ∀ σ (a : K) v, N σ (a • v) = ‖σ a‖ * N σ v)
    (hadd : ∀ σ v w, N σ (v + w) ≤ N σ v + N σ w)
    (hinv : ∀ g σ v, N σ (st g v) = N σ v)
    {C z b : ℝ} (hC : 0 ≤ C)
    (hqz : Real.log (Fintype.card H : ℝ) ≤ 45 * z ^ 2)
    (hz : 2 * C + 200 ≤ z) (hb : z ^ 12 ≤ b)
    (hm : ∀ h σ f, N σ (m h f) ≤ Real.exp (C * z ^ 9) * NA σ f)
    (σ : K →+* ℂ) (f : A) :
    (∑ h : H, N σ ((nativeCharacterTrace st χ).comp (m h) f) ^ 2) ≤
      Real.exp (2 * b) * NA σ f ^ 2 := by
  have hq : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  exact (nativeCharacterTrace_jointNorm_le st χ m NA N hN hsm hadd hinv hm σ f).trans
    (mul_le_mul_of_nonneg_right
      (nativeDescent_collectiveNormBudget hq hC hqz hz hb) (sq_nonneg _))

end RHLean.Geometry
