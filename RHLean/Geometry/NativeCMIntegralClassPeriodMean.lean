import RHLean.Geometry.NativeCMIsogenyPeriodMean
import RHLean.Geometry.NativeCMArithmeticPeriod

/-!
# The exact period mean on the native quadratic field and its actual seed

Integral representatives of every ideal class and their genuine period
lattices are constructed, with the principal class fixed to the original
elliptic seed. The arithmetic double-sum theorem is expressed in the same
`latticeLogPeriod` normalization as the existing native Chowla–Selberg and
all-place degree formulas. The genuine integral ideal-isogeny family is
still an explicit input to the arithmetic comparison.

This joins the native constructor and the declaration cuts attributed in
`NativeCMIsogenyPeriodMean` and `NativeCMArithmeticPeriod`; it adds no new
external source import and no assumed period mean.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField Module
open scoped Classical BigOperators nonZeroDivisors

namespace RHLean.Geometry.NativeCM.PeriodMean

theorem latticeLogPeriod_eq_normDisc (L : PeriodPair) :
    PeriodArithmetic.latticeLogPeriod L = Real.log (latticeNormDisc L) / 6 - Real.log Real.pi := by
  change Real.log (latticeArea L / Real.pi) +
    Real.log ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ / 6 = _
  rw [Real.log_div (latticeArea_pos L).ne' Real.pi_ne_zero, latticeNormDisc,
    Real.log_mul (pow_ne_zero 6 (latticeArea_pos L).ne')
      (norm_ne_zero_iff.mpr (discriminant_ne_zero L)), Real.log_pow]
  ring

theorem classPeriod_mean_eq_normDisc
    (K : Type) [Field K] [NumberField K] (Lc : ClassGroup (𝓞 K) → PeriodPair) :
    (∑ C, PeriodArithmetic.latticeLogPeriod (Lc C)) / (classNumber K : ℝ) =
      (∑ C, Real.log (latticeNormDisc (Lc C))) / (6 * Fintype.card (ClassGroup (𝓞 K))) -
        Real.log Real.pi := by
  have hh : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [latticeLogPeriod_eq_normDisc, Finset.sum_sub_distrib, ← Finset.sum_div,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  set S : ℝ := ∑ C, Real.log (latticeNormDisc (Lc C))
  change (S / 6 - (Fintype.card (ClassGroup (𝓞 K)) : ℝ) * Real.log Real.pi) /
    (Fintype.card (ClassGroup (𝓞 K)) : ℝ) =
      S / (6 * (Fintype.card (ClassGroup (𝓞 K)) : ℝ)) - Real.log Real.pi
  field_simp [hh]
  ring

/-- The arithmetic mean is now in the exact native period normalization.
The hypotheses are the actual two-sided integral derivative and lattice
inclusions, rather than the desired equality of means. -/
theorem mean_log_covolume_sub_log_pi_eq_class_period
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (hK : Module.finrank ℚ K = 2) (σ₀ : K →+* ℂ)
    (h₀ : ¬ NumberField.ComplexEmbedding.IsReal σ₀)
    (b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰) (Lc : ClassGroup (𝓞 K) → PeriodPair)
    (hb : ∀ C, ClassGroup.mk0 (b C) = C)
    (hLc : ∀ C z, z ∈ (Lc C).lattice ↔ ∃ a ∈ (b C : Ideal (𝓞 K)), z = σ₀ (a : K))
    (L₀ : (M →+* ℂ) → PeriodPair)
    (L : ClassGroup (𝓞 K) → (M →+* ℂ) → PeriodPair)
    (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ) (β : ClassGroup (𝓞 K) → M)
    (hst : ∀ s (a : 𝓞 K) z, z ∈ (L₀ s).lattice →
      s (algebraMap K M a) * z ∈ (L₀ s).lattice)
    (hδ : ∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s ((δ C : 𝓞 M) : M))
    (hβ : ∀ C, β C ≠ 0)
    (h₁ : ∀ C (x : K), (∀ y ∈ (b C : Ideal (𝓞 K)), IsIntegral ℤ (x * (y : K))) →
      IsIntegral ℤ (β C * algebraMap K M x) ∧
        ∀ s z, z ∈ (L₀ s).lattice → s (β C * algebraMap K M x) * z ∈ (L C s).lattice)
    (h₂ : ∀ C y, y ∈ (b C : Ideal (𝓞 K)) →
      IsIntegral ℤ ((β C)⁻¹ * algebraMap K M (y : K)) ∧
        ∀ s z, z ∈ (L C s).lattice → s ((β C)⁻¹ * algebraMap K M (y : K)) * z ∈ (L₀ s).lattice) :
    (∑ s : M →+* ℂ, Real.log (ZLattice.covolume (L₀ s).lattice)) /
        (Module.finrank ℚ M : ℝ) - Real.log Real.pi =
      (∑ C, PeriodArithmetic.latticeLogPeriod (Lc C)) / (classNumber K : ℝ) := by
  have h := mean_log_covolume_eq_mean_classGroup K M hK σ₀ h₀ b Lc hb hLc
    L₀ L δ β hst hδ hβ h₁ h₂
  simp only [← latticeArea_eq_abs_im_mul_conj] at h
  rw [classPeriod_mean_eq_normDisc]
  exact congrArg (fun x : ℝ => x - Real.log Real.pi) h

end RHLean.Geometry.NativeCM.PeriodMean

namespace RHLean.Geometry.NativeCM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/-- Actual integral class representatives for the arithmetic isogeny-family
comparison. The same original seed is retained in the principal class. -/
theorem exists_integralIdealClassPeriods_with_seed (G : NativeGeometricHost E) (τ : E →+* ℂ) :
    ∃ (b : ClassGroup (𝓞 (quadraticField G)) → (Ideal (𝓞 (quadraticField G)))⁰)
      (L : ClassGroup (𝓞 (quadraticField G)) → PeriodPair),
      (∀ C, ClassGroup.mk0 (b C) = C) ∧
      (∀ C z, z ∈ (L C).lattice ↔ ∃ a ∈ (b C : Ideal (𝓞 (quadraticField G))),
        z = quadraticEmbedding G τ (a : quadraticField G)) ∧
      b 1 = 1 ∧ L 1 = EllipticSeed.periodPair G τ ∧
      (((∑ C, PeriodArithmetic.latticeLogPeriod (L C)) /
          classNumber (quadraticField G) : ℝ) : ℂ) =
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt G.d) : ℝ) -
          deriv (periodCharacter G).LFunction 1 / (periodCharacter G).LFunction 1 := by
  have hrep : ∀ C : ClassGroup (𝓞 (quadraticField G)),
      ∃ (b : (Ideal (𝓞 (quadraticField G)))⁰) (L : PeriodPair),
        ClassGroup.mk0 b = C ∧
        (∀ z, z ∈ L.lattice ↔ ∃ a ∈ (b : Ideal (𝓞 (quadraticField G))),
          z = quadraticEmbedding G τ (a : quadraticField G)) ∧
        (C = 1 → b = 1 ∧ L = EllipticSeed.periodPair G τ) := by
    intro C
    by_cases hC : C = 1
    · subst C
      refine ⟨1, EllipticSeed.periodPair G τ, by simp, ?_, fun _ => ⟨rfl, rfl⟩⟩
      intro z
      change z ∈ ((EllipticSeed.periodPair G τ).lattice : Set ℂ) ↔ _
      rw [seedPeriod_eq_image_one]
      constructor
      · rintro ⟨x, hx, hz⟩
        obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
        exact ⟨a, by simp, hz.symm⟩
      · rintro ⟨a, _, rfl⟩
        exact ⟨a, (FractionalIdeal.mem_one_iff _).mpr ⟨a, rfl⟩, rfl⟩
    · obtain ⟨b, hb⟩ := ClassGroup.mk0_surjective C
      obtain ⟨L, hL⟩ := PeriodArithmetic.QuadraticZeta.exists_periodPair
        (quadraticField_finrank G) (quadraticField_discr G) (quadraticEmbedding G τ)
        (FractionalIdeal.mk0 (quadraticField G) b)
      refine ⟨b, L, hb, ?_, fun h => (hC h).elim⟩
      intro z
      change z ∈ (L.lattice : Set ℂ) ↔ _
      rw [hL]
      constructor
      · rintro ⟨x, hx, hz⟩
        obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
        exact ⟨a, ha, hz.symm⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, (FractionalIdeal.mem_coeIdeal _).mpr ⟨a, ha, rfl⟩, rfl⟩
  choose b L hb hL hOne using hrep
  refine ⟨b, L, hb, hL, (hOne 1 rfl).1, (hOne 1 rfl).2, ?_⟩
  have : NeZero G.d := ⟨G.d_prime.ne_zero⟩
  have hd : 4 < G.d := by have := G.d_mod; omega
  apply PeriodArithmetic.chowla_selberg_lattice
    (quadraticField_finrank G) (quadraticField_discr G) hd
    (periodCharacter_isKronecker G) (quadraticEmbedding G τ)
    (𝔞 := fun C => FractionalIdeal.mk0 (quadraticField G) (b C))
  · intro C
    exact (ClassGroup.mk_mk0 (quadraticField G) (b C)).trans (hb C)
  · intro C
    ext z
    rw [SetLike.mem_coe, hL]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (FractionalIdeal.mem_coeIdeal _).mpr ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨x, hx, hz⟩
      obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
      exact ⟨a, ha, hz.symm⟩

end RHLean.Geometry.NativeCM

end
