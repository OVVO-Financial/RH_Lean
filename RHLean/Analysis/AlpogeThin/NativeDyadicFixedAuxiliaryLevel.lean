import RHLean.Analysis.AlpogeThin.NativeDyadicHostPrimePowerWeights

/-!
# A fixed unramified auxiliary prime on the actual native host

The original HostHyp congruences exclude 5 from both selected primes.
Consequently 5 is coprime to the literal conductor `2^(e+2)*q*d`, and the
actual native inertia group at 5 is trivial, at every dyadic exponent.

This arithmetic fact accompanies the explicit-index finite-order argument:
an action congruent to the identity on the full 5-level has nilpotence index
one, so its freeness threshold does not grow with the lattice rank or field
degree. It does not assert that the original one-ideal level action satisfies
full 5-congruence, or construct a moduli cover with that extra level. Those
geometric and cost comparisons must still be supplied before replacing the
original auxiliary level by this candidate.

The source finite-order insight is reconstructed in
NativeThetaOrbitTorsion from Alpöge's
`FiniteOrderUnipotentAutDivisiblePrimaryEqId.lean` at
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
The conductor and inertia here are the existing native arithmetic objects.
-/

set_option autoImplicit false

namespace RHLean.Analysis.AlpogeThin

open Formalism.FrobeniusOrbits

/-- The same fixed prime 5 avoids the actual conductor at every dyadic size. -/
theorem nativeDyadicFixedLevelFive_not_dvd_conductor
    (e q d : ℕ) (hH : HostHyp q d) :
    ¬ 5 ∣ alpogeNativeHostN e q d := by
  obtain ⟨hq, hd, hq8, hd16, _⟩ := hH
  have h5 : Nat.Prime 5 := by norm_num
  have h5q : ¬ 5 ∣ q := by
    intro h
    have hq5 := (Nat.prime_dvd_prime_iff_eq h5 hq).mp h
    omega
  have h5d : ¬ 5 ∣ d := by
    intro h
    have hd5 := (Nat.prime_dvd_prime_iff_eq h5 hd).mp h
    omega
  have h52 : ¬ 5 ∣ 2 := by norm_num
  intro h
  unfold alpogeNativeHostN at h
  rcases h5.dvd_mul.mp h with h | h
  · rcases h5.dvd_mul.mp h with h | h
    · exact h52 (h5.dvd_of_dvd_pow h)
    · exact h5q h
  · exact h5d h

theorem nativeDyadicFixedLevelFive_coprime_conductor
    (e q d : ℕ) (hH : HostHyp q d) :
    Nat.Coprime 5 (alpogeNativeHostN e q d) :=
  (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr
    (nativeDyadicFixedLevelFive_not_dvd_conductor e q d hH)

/-- Triviality of the actual inertia, rather than a replacement unramified
host record or an assumed degree-one prime. -/
theorem nativeDyadicFixedLevelFive_inertia
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hH : HostHyp q d) :
    (alpogeNativeHostData e q d).inertia 5 = ⊥ :=
  nativeDyadicHostData_inertia_unramified e q d 5 (by norm_num)
    (nativeDyadicFixedLevelFive_not_dvd_conductor e q d hH)

end RHLean.Analysis.AlpogeThin
