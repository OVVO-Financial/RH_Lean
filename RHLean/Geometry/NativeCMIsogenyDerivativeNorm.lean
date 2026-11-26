import Mathlib

/-!
# The exact norm forced by two-sided integral ideal-isogeny derivatives

For an actual ideal b of O_K and a nonzero multiplier beta in M, the two
integrality conditions beta*b^-1 subset O_M and beta^-1*b subset O_M force
the extended ideal b O_M to equal (beta). Consequently the full embedding
sum of log|sigma(beta)| is [M:K] log N(b).

These are precisely the arithmetic derivative hypotheses used by the
row-sum calculation in the source class-group period comparison. They are
retained explicitly: algebraicity or complex lattice inclusion alone does
not prove them. No period average is assumed or assigned here.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/
SumLogNormEmbeddingEqFinrankMulLogAbsNorm.lean; consumed by
MeanLogCovolumeEqMeanClassGroup.lean, `mean_log_covolume_eq_mean_classGroup`.
The source archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped BigOperators nonZeroDivisors

namespace RHLean.Geometry.NativeCM.IsogenyDerivativeNorm

theorem exists_span_singleton_eq_map_of_integral
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (b : Ideal (𝓞 K)) (β : M) (hb : b ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ a ∈ b, IsIntegral ℤ (x * (a : K))) →
      IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ b, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    ∃ β₀ : 𝓞 M, (β₀ : M) = β ∧
      Ideal.span {β₀} = b.map (algebraMap (𝓞 K) (𝓞 M)) := by
  have hint : IsIntegral ℤ β := by
    have := h₁ 1 (fun a _ => by simpa using RingOfIntegers.isIntegral_coe a)
    simpa using this
  let β₀ : 𝓞 M := ⟨β, hint⟩
  have hβ₀ : (β₀ : M) = β := rfl
  have hb0 : (b : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hb
  refine ⟨β₀, hβ₀, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have hone : (1 : K) ∈
        (b : FractionalIdeal (𝓞 K)⁰ K) * (b : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
      rw [mul_inv_cancel₀ hb0]
      exact FractionalIdeal.one_mem_one _
    have key : ∀ r ∈ (b : FractionalIdeal (𝓞 K)⁰ K) *
        (b : FractionalIdeal (𝓞 K)⁰ K)⁻¹,
        ∃ z ∈ b.map (algebraMap (𝓞 K) (𝓞 M)), (z : M) = β * algebraMap K M r := by
      intro r hr
      refine FractionalIdeal.mul_induction_on
        (C := fun r => ∃ z ∈ b.map (algebraMap (𝓞 K) (𝓞 M)),
          (z : M) = β * algebraMap K M r) hr ?_ ?_
      · intro i hi j hj
        obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hi
        have hj' := (FractionalIdeal.mem_inv_iff hb0).mp hj
        have hI : IsIntegral ℤ (β * algebraMap K M j) := by
          refine h₁ j fun c hc => ?_
          obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).mp
            (hj' _ ((FractionalIdeal.mem_coeIdeal _).mpr ⟨c, hc, rfl⟩))
          rw [← hw]
          exact RingOfIntegers.isIntegral_coe w
        refine ⟨algebraMap (𝓞 K) (𝓞 M) a * ⟨_, hI⟩,
          Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha), ?_⟩
        change algebraMap K M (a : K) * (β * algebraMap K M j) =
          β * algebraMap K M ((a : K) * j)
        rw [map_mul]
        ring
      · rintro x y ⟨z, hz, hx⟩ ⟨w, hw, hy⟩
        refine ⟨z + w, Ideal.add_mem _ hz hw, ?_⟩
        change (z : M) + (w : M) = _
        rw [hx, hy, map_add]
        ring
    obtain ⟨z, hz, hz'⟩ := key 1 hone
    have heq : β₀ = z := by
      apply RingOfIntegers.ext
      rw [hz', hβ₀]
      simp
    rw [heq]
    exact hz
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨⟨_, h₂ y hy⟩, ?_⟩
    apply RingOfIntegers.ext
    change β⁻¹ * algebraMap K M (y : K) * (β₀ : M) = algebraMap K M (y : K)
    rw [hβ₀]
    field_simp

theorem abs_norm_eq_absNorm_pow_of_integral
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (b : Ideal (𝓞 K)) (β : M) (hb : b ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ a ∈ b, IsIntegral ℤ (x * (a : K))) →
      IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ b, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    |Algebra.norm ℚ β| = (Ideal.absNorm b : ℚ) ^ Module.finrank K M := by
  obtain ⟨β₀, rfl, hspan⟩ :=
    exists_span_singleton_eq_map_of_integral K M b β hb hβ h₁ h₂
  have h := congrArg Ideal.absNorm hspan
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_algebraMap,
    ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 M) M] at h
  rw [← Algebra.coe_norm_int, ← Nat.cast_pow, ← h, Nat.cast_natAbs, Int.cast_abs]

/-- The product-formula input for the class-family double sum, with all
integral ideal-isogeny derivative hypotheses retained. -/
theorem sum_log_norm_embedding_eq_finrank_mul_log_absNorm
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (b : Ideal (𝓞 K)) (β : M) (hb : b ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ a ∈ b, IsIntegral ℤ (x * (a : K))) →
      IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ b, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    ∑ σ : M →+* ℂ, Real.log ‖σ β‖ =
      (Module.finrank K M : ℝ) * Real.log (Ideal.absNorm b : ℝ) := by
  have h := abs_norm_eq_absNorm_pow_of_integral K M b β hb hβ h₁ h₂
  have hp : ∏ σ : M →+* ℂ, ‖σ β‖ = ((|Algebra.norm ℚ β| : ℚ) : ℝ) := by
    have h3 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ β)
    rw [norm_prod] at h3
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom M ℂ) (fun σ : M →+* ℂ => ‖σ β‖)
      (fun σ : M →ₐ[ℚ] ℂ => ‖σ β‖) (fun _ => rfl), ← h3]
    simp
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hβ)), hp, h]
  push_cast
  rw [Real.log_pow]

end RHLean.Geometry.NativeCM.IsogenyDerivativeNorm

end
