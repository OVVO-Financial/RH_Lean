import RHLean.Analysis.AlpogeNativeDiscriminantPrimes
import RHLean.Analysis.AlpogeThin.NativeDyadicHostPrimes
import RHLean.Analysis.AlpogeThin.NativeDyadicHostRamifiedPrimes
import RHLean.Analysis.AlpogeThin.NativeDyadicHostSideConditions

/-!
# The original discriminant-prime conditions on the actual raw host

The original conductor contains every discriminant prime. Two is ramified
using the already constructed unit `1 + N/2`. The prime d is ramified using
an actual CRT unit equal to one modulo `2^(e+2)*q` and minus one modulo d.
Its d-character is minus one because d is three modulo four. The native
inertia theorem turns these units into nonidentity inertia automorphisms
of the SAME field, proving both required discriminant divisibilities.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/DvdDiscrOfInertia.lean`, `Der.discr_primes`, and
`CycGrp.lean`, `Der.{ordCompl_d,exists_art_iod,inertia_d}`.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Ideal
open scoped Pointwise

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits NativeCyclotomicResidue

/-- The proved CRT unit supplies nontrivial d-inertia on the literal conductor. -/
theorem nativeDyadicArt_dInertia_nontrivial
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) :
    ∃ u : (ZMod (alpogeNativeHostN e q d))ˣ,
      (u : ZMod (alpogeNativeHostN e q d)).val ≡
        1 [MOD ordCompl[d] (alpogeNativeHostN e q d)] ∧
      nativeDyadicArt e q d u ≠ 1 := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  have hd4 : d % 4 = 3 := by omega
  obtain ⟨u, hu, hArt⟩ := nativeDyadicArt_exists_iod e q d hd2 hqd hd4
  refine ⟨u, ?_, ?_⟩
  · rw [nativeDyadicOrdCompl_d e q d hd2 hqd]
    exact hu
  · intro h
    have hsign := congrArg (fun g : (nativeDyadicFrame e).GG => g.1.2)
      (hArt.symm.trans h)
    change (-1 : ℤˣ) = 1 at hsign
    exact (by decide : (-1 : ℤˣ) ≠ 1) hsign

theorem nativeDyadicHostRaw_two_dvd_discr
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    (2 : ℤ) ∣ discr (nativeDyadicHostRaw e q d he hH).E := by
  let H := nativeDyadicHostRaw e q d he hH
  have : IsGalois ℚ H.E := H.galois
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine NativeDiscriminantPrimes.dvd_discr_of_inertia Nat.prime_two ?_
  intro P _ _
  obtain ⟨u, hu, hne⟩ := nativeDyadicArt_halfConductor_nontrivial e q d he hH
  have h2N : 2 ∣ alpogeNativeHostN e q d :=
    (dvd_pow_self 2 (by omega : e + 2 ≠ 0)).trans (alpogeNativeTwo_dvd_hostN e q d)
  have hM : ordCompl[2] (alpogeNativeHostN e q d) ∣ alpogeNativeHostN e q d / 2 := by
    rw [← Nat.ordCompl_div_of_dvd Nat.prime_two h2N]
    exact Nat.ordCompl_dvd _ _
  refine ⟨H.gal.symm (H.art u), fun h => hne (H.gal.symm.map_eq_one_iff.mp h), ?_⟩
  exact (nativeDyadicHostRaw_inertia e q d he hH 2 P _).mpr
    ⟨u, hu.of_dvd hM, H.gal.apply_symm_apply _⟩

theorem nativeDyadicHostRaw_d_dvd_discr
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    (d : ℤ) ∣ discr (nativeDyadicHostRaw e q d he hH).E := by
  let H := nativeDyadicHostRaw e q d he hH
  have : IsGalois ℚ H.E := H.galois
  refine NativeDiscriminantPrimes.dvd_discr_of_inertia hH.2.1 ?_
  intro P _ _
  obtain ⟨u, hu, hne⟩ := nativeDyadicArt_dInertia_nontrivial e q d hH
  refine ⟨H.gal.symm (H.art u), fun h => hne (H.gal.symm.map_eq_one_iff.mp h), ?_⟩
  exact (nativeDyadicHostRaw_inertia e q d he hH d P _).mpr
    ⟨u, hu, H.gal.apply_symm_apply _⟩

/-- Exactly the original `HostDer.discr_primes` field for the constructed host. -/
theorem nativeDyadicHostRaw_discr_primes
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr H.E → p ∣ H.condN) ∧
      (2 : ℤ) ∣ discr H.E ∧ (H.d : ℤ) ∣ discr H.E := by
  exact ⟨fun p hp h => alpogeNativeHostField_discr_prime_dvd_conductor e q d p hp h,
    nativeDyadicHostRaw_two_dvd_discr e q d he hH,
    nativeDyadicHostRaw_d_dvd_discr e q d he hH⟩

end RHLean.Analysis.AlpogeThin

end
