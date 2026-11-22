import RHLean.Analysis.AlpogeThin.NativeDyadicHostCore

/-!
# The complete original unramified-prime Frobenius field

At every rational prime outside the SAME native conductor, the proved
all-prime inertia and Frobenius criteria give trivial inertia and the unique
Artin image. Both quadratic coordinates and the dyadic class are evaluated
on the actual prime residue. This is the full original `HostDer.frob` field,
including existence, uniqueness, the character values and trivial inertia.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/CycGrp.lean`, `Der.frob` and its `jac_lemma`.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Ideal

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

private theorem nativeFrobeniusJacobi {p d : ℕ}
    (hp : p % 2 = 1) (hd : d % 4 = 3) :
    jacobiSym (-(d : ℤ)) p = jacobiSym (p : ℤ) d := by
  rw [jacobiSym.neg _ (Nat.odd_iff.mpr hp)]
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h (Nat.odd_iff.mpr (by omega))]
  · rw [ZMod.χ₄_nat_three_mod_four h,
      jacobiSym.quadratic_reciprocity_three_mod_four hd h]
    ring

/-- Exactly the original `HostDer.frob` field on the constructed raw host. -/
theorem nativeDyadicHostRaw_frob
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
        (∃ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P) ∧
        (∀ (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ),
          (u : ZMod H.condN) = (p : ZMod H.condN) →
          (IsArithFrobAt ℤ σ P ↔ H.gal σ = H.art u)) ∧
        (∀ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P →
          (((H.gal σ).1.1 : ℤˣ) : ℤ) = H.psAt p ∧
          (((H.gal σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧
          ∃ v : (ZMod (2 ^ ((nativeDyadicFrame e).e + 2)))ˣ,
            (v : ZMod (2 ^ ((nativeDyadicFrame e).e + 2))) = (p : ZMod _) ∧
            (nativeDyadicFrame e).hH (H.gal σ).2 = hcl (nativeDyadicFrame e).e v) ∧
        ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 := by
  dsimp only
  intro p _ hpN P _ _
  let H := nativeDyadicHostRaw e q d he hH
  have hp : p.Prime := Fact.out
  have hdmod := hH.2.2.2.1
  have hd4 : d % 4 = 3 := by omega
  have hcop : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  have hfact : ordCompl[p] H.condN = H.condN := by
    rw [Nat.factorization_eq_zero_of_not_dvd hpN, pow_zero, Nat.div_one]
  have hinert : ∀ σ : H.E ≃ₐ[ℚ] H.E,
      (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1 := by
    intro σ
    constructor
    · intro h
      obtain ⟨u, hu, hgal⟩ := (nativeDyadicHostRaw_inertia e q d he hH p P σ).mp h
      rw [hfact] at hu
      have hu1 : u = 1 := by
        apply Units.ext
        rw [Units.val_one, ← ZMod.natCast_zmod_val (u : ZMod H.condN),
          ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
        exact hu
      apply H.gal.injective
      simpa only [hu1, map_one] using hgal
    · rintro rfl x
      simp
  have hiff : ∀ (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ),
      (u : ZMod H.condN) = (p : ZMod H.condN) →
      (IsArithFrobAt ℤ σ P ↔ H.gal σ = H.art u) := by
    intro σ u hu
    rw [nativeDyadicHostRaw_frob_any e q d he hH p P σ]
    constructor
    · rintro ⟨v, hv, hgal⟩
      rw [hfact] at hv
      have hvu : v = u := by
        apply Units.ext
        rw [hu, ← ZMod.natCast_zmod_val (v : ZMod H.condN),
          ZMod.natCast_eq_natCast_iff]
        exact hv
      simpa only [hvu] using hgal
    · intro hgal
      refine ⟨u, ?_, hgal⟩
      rw [hfact, hu, ZMod.val_natCast]
      exact Nat.mod_modEq p _
  have hu0 : ((ZMod.unitOfCoprime p hcop : (ZMod H.condN)ˣ) : ZMod H.condN) = p :=
    ZMod.coe_unitOfCoprime _ _
  refine ⟨⟨H.gal.symm (H.art (ZMod.unitOfCoprime p hcop)),
    (hiff _ _ hu0).mpr (H.gal.apply_symm_apply _)⟩, hiff, fun σ hσ => ?_, hinert⟩
  have hg := (hiff σ _ hu0).mp hσ
  have htwo : 2 ^ (e + 2) ∣ H.condN := alpogeNativeTwo_dvd_hostN e q d
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpN ((dvd_pow_self 2 (by omega : e + 2 ≠ 0)).trans htwo)
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    unfold HostRaw.psAt
    rw [dite_eq_left hcop]
  · rw [hg, nativeDyadicHostRaw_art_ch e q d he hH, hu0, ZMod.val_natCast,
      nativeFrobeniusJacobi hpodd hd4,
      jacobiSym.mod_left ((p % H.condN : ℕ) : ℤ), jacobiSym.mod_left (p : ℤ)]
    congr 1
    push_cast
    exact Int.emod_emod_of_dvd _ (dvd_mul_left _ _)
  · have hc2 : Nat.Coprime p (2 ^ (e + 2)) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    refine ⟨ZMod.unitOfCoprime p hc2, ZMod.coe_unitOfCoprime _ _, ?_⟩
    rw [hg]
    apply H.art_h
    simp only [ZMod.coe_unitOfCoprime]
    rw [ZMod.val_natCast, ZMod.natCast_eq_natCast_iff]
    exact ((Nat.mod_modEq p H.condN).of_dvd htwo).symm

end RHLean.Analysis.AlpogeThin

end
