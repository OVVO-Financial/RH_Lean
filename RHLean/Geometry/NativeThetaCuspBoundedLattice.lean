import Mathlib

/-!
# Actual denominators and finiteness of bounded lattice coordinates

Integer multiples are constructed in the full lattice, and a common
coordinate denominator is obtained from its finite generators. Algebraic
integers bounded at every CM embedding form a finite set. No measure or
volume assumption appears.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsIntMulMem.lean,
src/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsIntMulIntegral.lean.
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open NumberField

namespace RHLean.Geometry.NativeTheta.Cusp.FlagBoundedLattice

theorem exists_int_mul_mem {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ y : NumberField.RingOfIntegers E, (d : E) * c = (y : E) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
  exact ⟨y, hy0, ⟨y • c, hy c (Finset.mem_singleton_self c)⟩, (zsmul_eq_mul c y).symm⟩

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ k : ℤ, k ≠ 0 ∧ k • v ∈ Λ := by
  classical
  have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by
    rw [hΛ]
    exact Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp hv
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy0, ?_⟩
  rw [← hfg, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  have hi := hy (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
  let o : NumberField.RingOfIntegers E := ⟨y • f i, hi⟩
  have e : y • f i • (g i : Fin r → E) = o • (g i : Fin r → E) := by
    rw [← smul_assoc, ← algebraMap_smul E o]
    rfl
  rw [e]
  exact Λ.smul_mem o (g i).2

variable {E : Type} [Field E] [NumberField E]

theorem exists_int_mul_integral (x : E) : ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ ((k : E) * x) := by
  have h : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨k, hk, hi⟩ := h.exists_integral_multiple
  exact ⟨k, hk, by simpa [zsmul_eq_mul] using hi⟩

theorem finite_bounded (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (k : ℤ) (hk : k ≠ 0) (R : ℝ) :
    {x : E | IsIntegral ℤ ((k : E) * x) ∧ ∀ τ : Ψ, ‖τ.1 x‖ ≤ R}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ (‖(k : ℂ)‖ * R)
  have hk' : (k : E) ≠ 0 := Int.cast_ne_zero.2 hk
  refine Set.Finite.of_finite_image (f := fun x => (k : E) * x) (hfin.subset ?_)
    (fun x _ y _ h => mul_left_cancel₀ hk' h)
  rintro _ ⟨x, ⟨hi, hb⟩, rfl⟩
  refine ⟨hi, fun φ => ?_⟩
  have : ‖φ x‖ ≤ R := by
    by_cases hφ : φ ∈ Ψ
    · exact hb ⟨φ, hφ⟩
    · have h2 : ComplexEmbedding.conjugate φ ∈ Ψ := by
        by_contra h3
        exact hφ ((hΨ φ).2 h3)
      have := hb ⟨_, h2⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using this
  simp only [map_mul, map_intCast, norm_mul]
  exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

theorem exists_common_den {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ v ∈ Λ, ∀ a, IsIntegral ℤ ((k : E) * v a) := by
  classical
  obtain ⟨S, rfl⟩ := hΛ
  choose d hd hdi using (exists_int_mul_integral (E := E))
  refine ⟨∏ p ∈ S ×ˢ (Finset.univ : Finset (Fin r)), d (p.1 p.2),
    Finset.prod_ne_zero_iff.2 fun p _ => hd _, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    intro a
    have hm : (v, a) ∈ S ×ˢ (Finset.univ : Finset (Fin r)) :=
      Finset.mem_product.2 ⟨hv, Finset.mem_univ _⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : (Fin r → E) × Fin r => d (p.1 p.2)) hm
    rw [hc]
    have := (hdi (v a)).mul (isIntegral_algebraMap (R := ℤ) (A := E) (x := c))
    have e : ((d (v a) * c : ℤ) : E) * v a = (d (v a) : E) * v a * algebraMap ℤ E c := by
      simp only [Int.cast_mul, eq_intCast]
      ring
    exact e ▸ this
  | zero => intro a; simpa using isIntegral_zero
  | add x y _ _ hx hy =>
    intro a
    rw [Pi.add_apply, mul_add]
    exact (hx a).add (hy a)
  | smul c x _ hx =>
    intro a
    have := (hx a).mul (RingOfIntegers.isIntegral_coe c)
    rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm, mul_comm]
    exact this

end RHLean.Geometry.NativeTheta.Cusp.FlagBoundedLattice
