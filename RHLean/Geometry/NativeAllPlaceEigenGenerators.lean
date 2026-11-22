import Mathlib

/-!
# Integral finite-character short spanning families at every place

This ports the finite-character construction in
`GlobalTheory.CovGminTop.exists_short_eigen` and the Mathlib-only proof
`GlobalTheory.eigenvector_mem_span_twistedTrace_image` from upstream commit
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

The constructed vector is the original UNNORMALIZED twisted trace
`sum h, χ(h)^(-1) • st(h)(v)`. Finite character values are proved integral
and have norm one at every embedding. Thus every output stays in the same
O_K-lattice and the exact norm cost is `|H| * B`.

Division by `|H|` occurs only in the proof of spanning over the field K.
The constructed integral vectors and their norm estimates are never divided.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField
open scoped BigOperators

namespace RHLean.Geometry

/-- A finite-character trace of a field-spanning family spans every vector in
the associated eigenspace. Its integral trace remains unnormalized. -/
theorem nativeEigenvector_mem_span_twistedTrace_image
    (H K V : Type) [Group H] [Fintype H] [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (st : H → V →ₗ[K] V)
    (χ : H →* Kˣ) (s : Set V) (hs : Submodule.span K s = ⊤)
    (x : V) (hx : ∀ h, st h x = ((χ h : Kˣ) : K) • x) :
    x ∈ Submodule.span K
      ((fun y => ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h y) '' s) := by
  let P : V →ₗ[K] V := ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h
  have hP : (fun y => ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h y) = ⇑P := by
    funext y
    simp [P, LinearMap.sum_apply]
  have hPx : P x = (Fintype.card H : K) • x := by
    rw [← hP]
    simp only [hx, smul_smul, Units.inv_mul, one_smul, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hcard : (Fintype.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hxP : x = P ((Fintype.card H : K)⁻¹ • x) := by
    rw [map_smul, hPx, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [hP, Submodule.span_image, hs, hxP]
  exact Submodule.mem_map_of_mem Submodule.mem_top

/-- Finite-character coefficients are integral units and have absolute value
one under every complex embedding. -/
theorem nativeFiniteCharacter_integral_norm_one
    {K H : Type} [Field K] [Group H] [Finite H]
    (χ : H →* Kˣ) (h : H) :
    IsIntegral ℤ ((χ h : Kˣ) : K) ∧
      ∀ σ : K →+* ℂ, ‖σ ((χ h : Kˣ) : K)‖ = 1 := by
  have hn : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h1 : ((χ h : Kˣ) : K) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  refine ⟨IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (h1 ▸ isIntegral_one), fun σ => ?_⟩
  have hpow : ‖σ ((χ h : Kˣ) : K)‖ ^ Nat.card H = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 hpow

/-- The actual finite-character trace constructs short integral eigenvectors
from the same lattice and all-place norms. Its only multiplicative norm cost
is the actual group cardinality. -/
theorem nativeExists_allPlace_short_eigen
    {K V H : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Group H] [Finite H] (st : H → V →ₗ[K] V)
    (hst : ∀ h h' x, st (h * h') x = st h' (st h x))
    (χ : H →* Kˣ) (L : Submodule (𝓞 K) V)
    (hL : ∀ h, ∀ x ∈ L, st h x ∈ L)
    (N : (K →+* ℂ) → V → ℝ)
    (hs : ∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x)
    (hadd : ∀ σ x y, N σ (x + y) ≤ N σ x + N σ y)
    (hi : ∀ h σ x, N σ (st h x) = N σ x)
    (s : Set V) (hsL : s ⊆ L) (hsp : Submodule.span K s = ⊤)
    (B : ℝ) (hB : ∀ y ∈ s, ∀ σ, N σ y ≤ B) :
    ∃ s' : Set V,
      (∀ y ∈ s', (y ∈ L ∧ ∀ h, st h y = ((χ h : Kˣ) : K) • y) ∧
        ∀ σ, N σ y ≤ Nat.card H * B) ∧
      ∀ x, (∀ h, st h x = ((χ h : Kˣ) : K) • x) →
        x ∈ Submodule.span K s' := by
  classical
  let := Fintype.ofFinite H
  have hN0 : ∀ σ, N σ 0 = 0 := fun σ => by simpa using hs σ 0 0
  have hsum : ∀ σ (T : Finset H) (f : H → V),
      N σ (∑ h ∈ T, f h) ≤ ∑ h ∈ T, N σ (f h) := by
    intro σ T f
    induction T using Finset.induction_on with
    | empty => simp [hN0]
    | insert h T hh ih =>
      rw [Finset.sum_insert hh, Finset.sum_insert hh]
      exact (hadd σ _ _).trans (add_le_add le_rfl ih)
  refine ⟨_, ?_, nativeEigenvector_mem_span_twistedTrace_image H K V st χ s hsp⟩
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨⟨L.sum_mem fun h _ => ?_, fun g => ?_⟩, fun σ => ?_⟩
  · rw [← map_inv]
    let a : 𝓞 K := ⟨_, (nativeFiniteCharacter_integral_norm_one χ h⁻¹).1⟩
    have hmem := L.smul_mem a (hL h y (hsL hy))
    rwa [← algebraMap_smul K a] at hmem
  · beta_reduce
    rw [map_sum, Finset.smul_sum,
      ← Equiv.sum_comp (Equiv.mulRight g) fun h => _ • _ • st h y]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_smul, ← hst, smul_smul, Equiv.coe_mulRight, map_mul,
      mul_inv, ← Units.val_mul, mul_left_comm, mul_inv_cancel, mul_one]
  · refine (hsum σ _ _).trans ?_
    rw [Nat.card_eq_fintype_card, ← nsmul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun h _ => ?_
    rw [hs, hi, ← map_inv, (nativeFiniteCharacter_integral_norm_one χ h⁻¹).2, one_mul]
    exact hB y hy σ

end RHLean.Geometry

