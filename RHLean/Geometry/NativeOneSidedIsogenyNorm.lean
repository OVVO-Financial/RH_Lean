import Mathlib

/-!
# One-sided norm control from reverse ideal-isogeny integrality

If the actual reverse derivative maps an integral ideal `b` into the ring
of integers, then its reciprocal multiplier satisfies an upper norm bound.
The forward derivative integrality hypothesis is not needed. The multiplier
itself need not be integral: the proof clears its denominator and compares
the norms of two literal integral ideals.

In the CM period double sum this is the useful direction: the row correction
`2 * mean(log |beta|) - log Norm(b)` is nonpositive. The theorem below is
only the arithmetic norm estimate. It neither constructs an isogeny nor
assumes or supplies an arithmetic period mean.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical BigOperators nonZeroDivisors

namespace RHLean.Geometry.NativeOneSidedIsogenyNorm

/-- Denominator clearing proves the bound even when the actual multiplier
is not integral. The sole integrality hypothesis is on its reverse action
on the specified ideal. -/
theorem abs_norm_le_absNorm_of_reverse_integral
    (M : Type*) [Field M] [NumberField M]
    (I : Ideal (𝓞 M)) (β : M) (hI : I ≠ ⊥) (hβ : β ≠ 0)
    (hrev : ∀ y ∈ I, IsIntegral ℤ (β⁻¹ * (y : M))) :
    |Algebra.norm ℚ β| ≤ (Ideal.absNorm I : ℚ) := by
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) β
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdM : (d : M) ≠ 0 := by exact_mod_cast hd0
  have haM : (a : M) ≠ 0 := by
    intro ha
    apply hβ
    change (a : M) / (d : M) = 0
    simp [ha]
  have hinc : Ideal.span {d} * I ≤ Ideal.span {a} := by
    rw [Ideal.span_singleton_mul_le_iff]
    intro y hy
    let z : 𝓞 M := ⟨((a : M) / (d : M))⁻¹ * (y : M), hrev y hy⟩
    rw [Ideal.mem_span_singleton']
    refine ⟨z, ?_⟩
    apply RingOfIntegers.ext
    change (((a : M) / (d : M))⁻¹ * (y : M)) * (a : M) =
      (d : M) * (y : M)
    field_simp [haM, hdM]
    <;> ring
  have hId : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
    intro hz
    have hz' : Ideal.span {d} = ⊥ := Ideal.absNorm_eq_zero_iff.mp hz
    exact hd0 (Ideal.span_singleton_eq_bot.mp hz')
  have hII : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hI
  have hprod : 0 < Ideal.absNorm (Ideal.span {d} * I) := by
    rw [map_mul]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hId) (Nat.pos_of_ne_zero hII)
  have hN := Nat.le_of_dvd hprod (Ideal.absNorm_dvd_absNorm_of_le hinc)
  rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at hN
  have hNq :
      ((Algebra.norm ℤ a).natAbs : ℚ) ≤
        ((Algebra.norm ℤ d).natAbs : ℚ) * (Ideal.absNorm I : ℚ) := by
    exact_mod_cast hN
  have hnorm :
      |Algebra.norm ℚ (a : M)| ≤
        |Algebra.norm ℚ (d : M)| * (Ideal.absNorm I : ℚ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int] using hNq
  have hden : 0 < |Algebra.norm ℚ (d : M)| :=
    abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hdM)
  change |Algebra.norm ℚ ((a : M) / (d : M))| ≤ _
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, abs_mul, abs_inv,
    ← div_eq_mul_inv]
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hnorm)

/-- The reverse integrality condition on the original ideal over `K`
extends to its actual ideal in `O_M`; its norm is `Norm(b)^[M:K]`.
No forward derivative condition or integrality of `beta` is assumed. -/
theorem abs_norm_le_absNorm_pow_of_reverse_integral
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (b : Ideal (𝓞 K)) (β : M) (hb : b ≠ ⊥) (hβ : β ≠ 0)
    (hrev : ∀ y ∈ b, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    |Algebra.norm ℚ β| ≤ (Ideal.absNorm b : ℚ) ^ Module.finrank K M := by
  let B : Ideal (𝓞 M) := b.map (algebraMap (𝓞 K) (𝓞 M))
  let J : Ideal (𝓞 M) :=
    { carrier := {y | IsIntegral ℤ (β⁻¹ * (y : M))}
      zero_mem' := by
        change IsIntegral ℤ (β⁻¹ * (0 : M))
        simpa only [mul_zero] using (isIntegral_zero : IsIntegral ℤ (0 : M))
      add_mem' := by
        intro y z hy hz
        change IsIntegral ℤ (β⁻¹ * ((y : M) + (z : M)))
        simpa only [mul_add] using hy.add hz
      smul_mem' := by
        intro r y hy
        change IsIntegral ℤ (β⁻¹ * ((r : M) * (y : M)))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          (RingOfIntegers.isIntegral_coe r).mul hy }
  have hBJ : B ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    change IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))
    exact hrev y hy
  have hBN : Ideal.absNorm B = Ideal.absNorm b ^ Module.finrank K M := by
    dsimp only [B]
    rw [Ideal.absNorm_algebraMap,
      ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 M) M]
  have hB : B ≠ ⊥ := by
    intro h
    have hzero : Ideal.absNorm B = 0 := Ideal.absNorm_eq_zero_iff.mpr h
    rw [hBN] at hzero
    exact pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.mpr hb) hzero
  have h := abs_norm_le_absNorm_of_reverse_integral M B β hB hβ
    (fun y hy => hBJ hy)
  simpa only [hBN, Nat.cast_pow] using h

/-- The complete embedding logarithm has the one-sided bound needed to
make the CM row correction nonpositive. All complex embeddings occur. -/
theorem sum_log_norm_embedding_le_finrank_mul_log_absNorm_of_reverse_integral
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (b : Ideal (𝓞 K)) (β : M) (hb : b ≠ ⊥) (hβ : β ≠ 0)
    (hrev : ∀ y ∈ b, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    ∑ σ : M →+* ℂ, Real.log ‖σ β‖ ≤
      (Module.finrank K M : ℝ) * Real.log (Ideal.absNorm b : ℝ) := by
  have hp : ∏ σ : M →+* ℂ, ‖σ β‖ = ((|Algebra.norm ℚ β| : ℚ) : ℝ) := by
    have h := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ β)
    rw [norm_prod] at h
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom M ℂ)
      (fun σ : M →+* ℂ => ‖σ β‖)
      (fun σ : M →ₐ[ℚ] ℂ => ‖σ β‖) (fun _ => rfl), ← h]
    simp
  have hposQ : (0 : ℚ) < |Algebra.norm ℚ β| :=
    abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hβ)
  have hpos : (0 : ℝ) < ((|Algebra.norm ℚ β| : ℚ) : ℝ) := by
    exact_mod_cast hposQ
  have hnorm : ((|Algebra.norm ℚ β| : ℚ) : ℝ) ≤
      (Ideal.absNorm b : ℝ) ^ Module.finrank K M := by
    exact_mod_cast abs_norm_le_absNorm_pow_of_reverse_integral K M b β hb hβ hrev
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hβ)), hp]
  have hlog := Real.log_le_log hpos hnorm
  rw [Real.log_pow] at hlog
  exact hlog

/-- For a quadratic CM base, the literal correction in each class-period
row is nonpositive. The factor two comes from the degree tower, not from
an assigned normalization of the period. -/
theorem quadratic_period_row_correction_nonpos
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (hK : Module.finrank ℚ K = 2)
    (b : Ideal (𝓞 K)) (β : M) (hb : b ≠ ⊥) (hβ : β ≠ 0)
    (hrev : ∀ y ∈ b, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    (2 / (Module.finrank ℚ M : ℝ)) * (∑ σ : M →+* ℂ, Real.log ‖σ β‖) -
      Real.log (Ideal.absNorm b : ℝ) ≤ 0 := by
  have hlog := sum_log_norm_embedding_le_finrank_mul_log_absNorm_of_reverse_integral
    K M b β hb hβ hrev
  have hM : (0 : ℝ) < Module.finrank ℚ M := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ M)
  have hdegNat : Module.finrank ℚ M = 2 * Module.finrank K M := by
    rw [← Module.finrank_mul_finrank ℚ K M, hK]
  have hdeg : (Module.finrank ℚ M : ℝ) = 2 * (Module.finrank K M : ℝ) := by
    exact_mod_cast hdegNat
  have hfactor : (2 / (Module.finrank ℚ M : ℝ)) * (Module.finrank K M : ℝ) = 1 := by
    field_simp [hM.ne']
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 2 / (Module.finrank ℚ M : ℝ) by positivity)
  rw [← mul_assoc, hfactor, one_mul] at hscaled
  exact sub_nonpos.mpr hscaled

end RHLean.Geometry.NativeOneSidedIsogenyNorm

end
