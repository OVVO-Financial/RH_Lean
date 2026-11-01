import Mathlib

/-!
# Root-dependent moving-band resonance

The moving product `j * R + k` has branch multiplicity
`gcd (j^2) (j * R + k)`. This module formalizes the referee-accepted
surviving criterion from claims `20261031-wheel-1` and
`20261031-referee-2`: the branch is uniquely invertible exactly when
`j` and `k` are coprime.

It also preserves the smallest exact counterexample to the discarded
root-independent formula. No averaged moment, source bound, or endpoint
estimate is asserted.
-/

namespace RHLean.Proof

/-- Exact moving-band branch multiplicity at root `R`. -/
def rootResonanceMultiplicity (R j k : ℕ) : ℕ :=
  Nat.gcd (j ^ 2) (j * R + k)

/-- The moving branch is unique exactly on the coprime `(j,k)` sector. -/
theorem rootResonanceMultiplicity_eq_one_iff
    (R j k : ℕ) :
    rootResonanceMultiplicity R j k = 1 ↔ Nat.Coprime j k := by
  unfold rootResonanceMultiplicity
  constructor
  · intro hres
    rw [Nat.coprime_iff_gcd_eq_one]
    apply Nat.eq_one_of_dvd_one
    rw [← hres]
    apply Nat.dvd_gcd
    · exact dvd_trans (Nat.gcd_dvd_left j k) (dvd_pow_self j (by norm_num))
    · exact dvd_add
        (dvd_mul_of_dvd_left (Nat.gcd_dvd_left j k) R)
        (Nat.gcd_dvd_right j k)
  · intro hcop
    by_contra hne
    obtain ⟨p, hpPrime, hpDvd⟩ := Nat.exists_prime_and_dvd hne
    have hpDvdJ2 : p ∣ j ^ 2 :=
      dvd_trans hpDvd (Nat.gcd_dvd_left _ _)
    have hpDvdJ : p ∣ j := hpPrime.dvd_of_dvd_pow hpDvdJ2
    have hpDvdJR : p ∣ j * R := dvd_mul_of_dvd_left hpDvdJ R
    have hpDvdSum : p ∣ j * R + k :=
      dvd_trans hpDvd (Nat.gcd_dvd_right _ _)
    have hpDvdK : p ∣ k := by
      apply (Nat.dvd_add_iff_left hpDvdJR).mpr
      simpa [Nat.add_comm] using hpDvdSum
    have hpDvdGcd : p ∣ Nat.gcd j k := Nat.dvd_gcd hpDvdJ hpDvdK
    rw [hcop.gcd_eq_one] at hpDvdGcd
    exact hpPrime.not_dvd_one hpDvdGcd

/-- Minimal regression: the root phase inflates multiplicity from `2` to `4`. -/
theorem rootResonance_root_independent_formula_false :
    rootResonanceMultiplicity 3 2 2 = 4 ∧ Nat.gcd (2 ^ 2) 2 = 2 := by
  norm_num [rootResonanceMultiplicity]

#print axioms rootResonanceMultiplicity_eq_one_iff
#print axioms rootResonance_root_independent_formula_false

end RHLean.Proof
