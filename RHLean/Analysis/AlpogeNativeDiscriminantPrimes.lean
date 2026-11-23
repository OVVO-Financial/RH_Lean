import RHLean.Analysis.AlpogeNativeHostPrimes

/-!
# Discriminant support and genuine ramification

A rational prime with a nonidentity inertia automorphism divides the actual
number-field discriminant. Conversely, the native host embeds in the
cyclotomic field of its original conductor, so every discriminant prime
divides that conductor. Both statements use the actual ring of integers.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/DvdDiscrOfInertia.lean`,
`Rd.dvd_discr_of_inertia` and the conductor-support part of `Der.discr_primes`.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

open NumberField IntermediateField Ideal
open scoped Pointwise

namespace RHLean.Analysis.NativeDiscriminantPrimes

theorem dvd_discr_of_inertia {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    {l : ℕ} (hl : l.Prime)
    (h : ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})],
      ∃ σ : E ≃ₐ[ℚ] E, σ ≠ 1 ∧ ∀ x : 𝓞 E, σ • x - x ∈ P) :
    (l : ℤ) ∣ discr E := by
  by_contra hn
  have : Fact l.Prime := ⟨hl⟩
  have hl' := Nat.prime_iff_prime_int.mp hl
  have : (span {(l : ℤ)}).IsPrime := (span_singleton_prime hl'.ne_zero).mpr hl'
  obtain ⟨⟨P, hP, hPl⟩⟩ : Nonempty ((span {(l : ℤ)}).primesOver (𝓞 E)) := inferInstance
  have hpb : span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hl'.ne_zero
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpb P
  have hun := (not_dvd_discr_iff_forall_liesOver E (𝓞 E) hl').mp hn P
    (hP.isMaximal hP0) hPl
  have hcard := card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (span {(l : ℤ)}) P
  rw [ramificationIdxIn_eq_ramificationIdx (span {(l : ℤ)}) P (E ≃ₐ[ℚ] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, Subgroup.card_eq_one] at hcard
  obtain ⟨σ, hσ1, hσ⟩ := h P
  have h3 : σ ∈ P.inertia (E ≃ₐ[ℚ] E) := AddSubgroup.mem_inertia.mpr hσ
  rw [hcard, Subgroup.mem_bot] at h3
  exact hσ1 h3

end RHLean.Analysis.NativeDiscriminantPrimes

namespace RHLean.Analysis

/-- Every discriminant prime of the actual fixed field divides its original
cyclotomic conductor. No ramification-support hypothesis is supplied. -/
theorem alpogeNativeHostField_discr_prime_dvd_conductor
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (p : ℕ) (hp : p.Prime) (h : (p : ℤ) ∣ discr (alpogeNativeHostField e q d)) :
    p ∣ alpogeNativeHostN e q d := by
  have h1 := h.trans
    (discr_dvd_discr (alpogeNativeHostField e q d) (AlpogeNativeCyclotomic e q d))
  rw [Int.natCast_dvd, IsCyclotomicExtension.Rat.natAbs_discr (alpogeNativeHostN e q d)] at h1
  exact hp.dvd_of_dvd_pow (h1.trans
    (Nat.div_dvd_of_dvd (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))))

end RHLean.Analysis

end
