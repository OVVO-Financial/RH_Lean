import RHLean.Analysis.AlpogeNativeCMPrimeSplitting
import RHLean.Analysis.AlpogeThin.NativeDyadicHostDifferent
import RHLean.Analysis.AlpogeThin.NativeDyadicHostFrobenius

/-!
# The original eta clause on the actual native host

The native CM extension over its maximal real subfield is already proved
unramified. Its actual prime splitting gives the split-or-inert alternative.
At primes outside the same conductor, the Frobenius subgroup contains
complex conjugation exactly when eta is negative. At conductor primes,
the proved exclusion of conjugation from the decomposition group gives
positive eta. These are all three parts of the literal `HostDer.eta` field.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/KcBase.lean`, `Der.eta`.
Every former `HostCore` field used by that proof is supplied by the actual
native fixed field, its ideal-theoretic Frobenius and its conjugation.
No eta value, splitting premise or decomposition-group equality is assumed.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Ideal
open scoped Pointwise

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

private theorem nativeEta_prime_ne_bot {M : Type} [Field M] [NumberField M]
    (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 M))
    [P.LiesOver (span {(p : ℤ)})] : P ≠ ⊥ := by
  have hne : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by simp [hp.ne_zero]
  exact Ideal.ne_bot_of_liesOver_of_ne_bot hne P

/-- The complete original eta field is proved for the same constructed
native host, with its actual maximal real subfield and actual primes. -/
theorem nativeDyadicHostRaw_eta
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    (∀ 𝔭 : Ideal (𝓞 H.F), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      (primesOver 𝔭 (𝓞 H.E)).ncard = 2 ∨
        ((primesOver 𝔭 (𝓞 H.E)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 H.E) = 2)) ∧
    (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
        (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P →
          (H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔
            (nativeDyadicFrame e).cc ∈ Subgroup.zpowers (H.gal σ))) ∧
    (∀ (p : ℕ) [Fact p.Prime], p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
        H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1) := by
  let H := nativeDyadicHostRaw e q d he hH
  let : IsCMField H.E := nativeDyadicHostRaw_cm e q d he hH
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  let : Algebra.Unramified (𝓞 H.F) (𝓞 H.E) :=
    alpogeNativeHostField_unramified e q d
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have hconj : (IsCMField.complexConj H.E).restrictScalars ℚ = H.conj := by
    apply AlgEquiv.ext
    intro x
    change IsCMField.complexConj H.E x = H.conj x
    rw [nativeDyadicHostRaw_conj e q d he hH]
    exact alpogeNativeHostConj_complexConj e q d x
  have hsm : ∀ P : Ideal (𝓞 H.E), IsCMField.complexConj H.E • P = H.conj • P :=
    fun P => by
      rw [← hconj]
      rfl
  have hetaiff : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], P ≠ ⊥ →
      (H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1 ↔ H.conj • P ≠ P) := by
    intro P hP hP0
    let : P.IsPrime := hP
    have hk := NativeCMPrimeSplitting.ncard_eq_two_iff H.E P hP0
    rw [hsm] at hk
    unfold HostRaw.etaF
    change (if (primesOver (P.under (𝓞 H.F)) (𝓞 H.E)).ncard = 2 then (1 : ℤ)
      else -1) = 1 ↔ _
    rw [← hk]
    split_ifs with h2
    · exact iff_of_true rfl h2
    · exact iff_of_false (by decide) h2
  refine ⟨fun 𝔭 hp h0 => ?_, ?_, ?_⟩
  · let : 𝔭.IsPrime := hp
    exact NativeCMPrimeSplitting.split_or_inert H.E 𝔭 h0
  · intro p hpf hN P hP hPl σ hσ
    let : Fact p.Prime := hpf
    let : P.IsPrime := hP
    let : P.LiesOver (span {(p : ℤ)}) := hPl
    have hP0 := nativeEta_prime_ne_bot p hpf.out P
    have hm1 : H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔ H.conj • P = P := by
      have h1 := hetaiff P hP0
      have hval : H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1 ∨
          H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 := by
        unfold HostRaw.etaF
        split_ifs <;> simp
      constructor
      · intro hm
        by_contra hc
        rw [h1.mpr hc] at hm
        exact absurd hm (by decide)
      · intro hfix
        rcases hval with hv | hv
        · exact absurd hfix (h1.mp hv)
        · exact hv
    rw [hm1]
    constructor
    · intro hfix
      have hst : H.conj ∈ MulAction.stabilizer _ P := hfix
      obtain ⟨k, ρ, hρ, hρeq⟩ :=
        NativePrimeDecomposition.stab_eq_inertia_mul p P σ H.conj hσ hst
      rw [((nativeDyadicHostRaw_frob e q d he hH p hN P).2.2.2 ρ).mp hρ,
        one_mul] at hρeq
      exact Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), by
        rw [zpow_natCast, ← map_pow, ← hρeq, NativeRawHostDifferent.gal_conj]⟩
    · intro hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hσc : σ ^ k = H.conj := H.gal.injective (by
        rw [map_zpow, hk, NativeRawHostDifferent.gal_conj])
      rw [← hσc]
      exact Subgroup.zpow_mem _ hσ.mem_stabilizer k
  · intro p hpf hN P hP hPl
    let : Fact p.Prime := hpf
    let : P.IsPrime := hP
    let : P.LiesOver (span {(p : ℤ)}) := hPl
    exact (hetaiff P (nativeEta_prime_ne_bot p hpf.out P)).mpr
      (nativeDyadicHostRaw_decompConj e q d he hH p hpf.out hN P)

end RHLean.Analysis.AlpogeThin

end
