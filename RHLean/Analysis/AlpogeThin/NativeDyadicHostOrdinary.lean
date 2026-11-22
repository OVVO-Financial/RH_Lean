import RHLean.Analysis.AlpogeThin.NativeDyadicHostSplitting
import RHLean.Analysis.AlpogeThin.NativeDyadicHostDifferent
import RHLean.Analysis.AlpogeThin.NativeDyadicHostFrobenius

/-!
# The exact ordinary-prime criterion for the constructed host

The prime splits in the literal quadratic subfield exactly when the actual
prime decomposition group preserves the CM type. All ramified cases are
retained: primes in QS*q use the constructed type-I decomposition theorem,
d uses its actual inertia element, and primes outside N use the actual
Frobenius generator and trivial inertia.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/KcBase.lean`, `Der.ordinary`.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Ideal
open scoped Pointwise

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

private theorem nativeStabOfInertia {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g : G) (P : Ideal S)
    (h : ∀ x : S, g • x - x ∈ P) : g ∈ MulAction.stabilizer G P := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have h1 := h (g⁻¹ • x)
  rw [smul_inv_smul] at h1
  constructor
  · intro hx
    simpa using P.add_mem h1 hx
  · intro hx
    simpa using P.sub_mem hx h1

/-- The original ordinary-prime criterion on the SAME constructed host. -/
theorem nativeDyadicHostRaw_ordinary
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∀ σ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P →
        (H.gal (σ * τ) ∈ (nativeDyadicFrame e).Psi ↔ H.gal σ ∈ (nativeDyadicFrame e).Psi)) ↔
        (primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 := by
  let H := nativeDyadicHostRaw e q d he hH
  intro p hpf P _ _
  have hp : p.Prime := hpf.out
  have hred : (∀ σ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P →
      (H.gal (σ * τ) ∈ (nativeDyadicFrame e).Psi ↔ H.gal σ ∈ (nativeDyadicFrame e).Psi)) ↔
      ∀ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P → H.gal τ ∈ (nativeDyadicFrame e).Psi := by
    constructor
    · intro h τ hτ
      have := h 1 τ hτ
      rw [one_mul, map_one] at this
      exact this.mpr (one_mem _)
    · intro h σ τ hτ
      rw [map_mul]
      exact Subgroup.mul_mem_cancel_right _ (h τ hτ)
  rw [hred, nativeDyadicHostRaw_splitK e q d he hH p hp]
  by_cases h1 : p ∣ H.QS * H.q
  · refine iff_of_true (fun τ hτ => nativeDyadicHostRaw_decomp_typeI e q d he hH p hp h1 P τ hτ) ?_
    by_cases h2 : p = 2
    · exact Or.inl h2
    · refine Or.inr ⟨h2, ?_⟩
      rcases hp.dvd_mul.mp h1 with h3 | h3
      · exact H.QS_split p hp h2 h3
      · rw [(Nat.prime_dvd_prime_iff_eq hp H.hyp.1).mp h3]
        exact H.hyp.2.2.2.2
  have hp2 : p ≠ 2 := by
    rintro rfl
    have htwo : 2 ∣ H.QS := (dvd_pow_self 2 (by omega)).trans H.tower_dvd
    exact h1 (htwo.mul_right _)
  by_cases hpd : p = H.d
  · subst hpd
    refine iff_of_false (fun h => ?_) ?_
    · obtain ⟨σ, hσ⟩ := H.gal.surjective (nativeDyadicFrame e).iod
      have h3 := h σ (nativeStabOfInertia σ P ((nativeDyadicHostRaw_inertia_d e q d he hH P σ).mpr (Or.inr hσ)))
      rw [hσ] at h3
      exact NativeRawHostDifferent.iod_not_mem_Psi h3
    · rintro (h | ⟨-, h⟩)
      · exact hp2 h
      · have : NeZero H.d := ⟨hp.ne_zero⟩
        have h0 : jacobiSym (-(H.d : ℤ)) H.d = 0 :=
          jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa using hp.ne_one)
        omega
  · have hN : ¬ p ∣ H.condN := fun h => by
      rcases hp.dvd_mul.mp h with h3 | h3
      · exact h1 h3
      · exact hpd ((Nat.prime_dvd_prime_iff_eq hp H.hyp.2.1).mp h3)
    obtain ⟨⟨F, hF⟩, -, f3, f4⟩ := nativeDyadicHostRaw_frob e q d he hH p hN P
    have hj := (f3 F hF).2.1
    have hFP : H.gal F ∈ (nativeDyadicFrame e).Psi ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1)) := by
      rw [Frame.mem_Psi_iff, ← hj, or_iff_right hp2, and_iff_right hp2]
      exact (Units.val_eq_one).symm
    rw [← hFP]
    constructor
    · intro h
      exact h F hF.mem_stabilizer
    · intro hFm τ hτ
      obtain ⟨k, ρ, hρ, rfl⟩ := NativePrimeDecomposition.stab_eq_inertia_mul p P F τ hF hτ
      rw [(f4 ρ).mp hρ, one_mul, map_pow]
      exact Subgroup.pow_mem _ hFm k

end RHLean.Analysis.AlpogeThin

end
