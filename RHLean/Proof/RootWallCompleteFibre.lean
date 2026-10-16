import Mathlib
import RHLean.Analysis.DyadicTransportCanonicalForm
import RHLean.Proof.OddResidualCofactorSupport

/-!
# Complete greatest-prime fibres above the square-root wall

This module formalizes the exact incidence core of claim `20261016-owner-1`
from the 2026-10-16 unified manual research cycle.

For a strict square endpoint `R^2` and a prime `q ≥ R`, every positive
multiple `a * q < R^2` has `a < q`.  Consequently its canonical greatest prime
factor is exactly `q`, and it is never a perfect square.  Conversely, every
`1 < n < R^2` whose greatest prime factor is `q ≥ R` is such a multiple.  Above
the square-root wall the canonical greatest-prime fibre of `q` is therefore the
complete set of multiples of `q` below the endpoint: no smoothness condition
and no square exclusion is active.  Inside such a fibre, the explicit residual
exclusions `IsOddFactorDepthResidual` hold exactly when the cofactor is
composite, and odd composite cofactors recover the one-ninth wall of
`OddResidualCofactorSupport`.

The greatest-prime and cofactor evaluation of `a * q` for `0 < a < q` reuses the
existing `canonicalLargestPrimeFactor_mul_prime_eq` and
`canonicalCofactor_mul_prime_eq`; only the root-wall inequality, the
non-square property, the fibre characterization and the residual
characterization are new here.

This is a structural incidence theorem only.  It does not define the raw
native-weight ledger, estimate any signed sum or covariance, transfer to the
returned-cell carrier, or bound the canonical endpoint.
-/

noncomputable section

namespace RHLean.Proof

/-- A cofactor of a factor at or above the root of a strict square endpoint is
smaller than that factor. -/
theorem lt_of_mul_lt_sq_of_root_le {R a q : ℕ} (hRq : R ≤ q) (h : a * q < R ^ 2) :
    a < q := by
  rw [sq] at h
  by_contra hcon
  have hqa : q ≤ a := not_lt.mp hcon
  have h1 : R * R ≤ q * q := Nat.mul_le_mul hRq hRq
  have h2 : q * q ≤ a * q := Nat.mul_le_mul_right q hqa
  omega

/-- Such a multiple is never a perfect square. -/
theorem mul_ne_sq_of_lt {a q : ℕ} (hq : q.Prime) (ha : 0 < a) (haq : a < q) (m : ℕ) :
    a * q ≠ m ^ 2 := by
  intro hm
  rw [sq] at hm
  have hqmm : q ∣ m * m := by
    rw [← hm]
    exact dvd_mul_left q a
  have hqm : q ∣ m := by
    rcases (Nat.Prime.dvd_mul hq).mp hqmm with h | h <;> exact h
  obtain ⟨k, hk⟩ := hqm
  have hq0 : 0 < q := hq.pos
  have hmul : a * q = (q * (k * k)) * q := by
    rw [hm, hk]
    ring
  have hak : a = q * (k * k) := Nat.eq_of_mul_eq_mul_right hq0 hmul
  have hkk : k * k ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hak
    omega
  have hk1 : 1 ≤ k * k := Nat.one_le_iff_ne_zero.mpr hkk
  have h1 : q * 1 ≤ q * (k * k) := Nat.mul_le_mul_left q hk1
  omega

/-- Packaged complete-fibre statement: above the root, a positive multiple
below the square endpoint has cofactor below its prime, has that prime as its
canonical greatest prime factor and the multiplier as its canonical cofactor,
and is not a perfect square. -/
theorem completeFibre_of_root_le {R a q : ℕ} (hq : q.Prime) (hRq : R ≤ q) (ha : 0 < a)
    (h : a * q < R ^ 2) :
    a < q ∧ canonicalLargestPrimeFactor (a * q) = q ∧ canonicalCofactor (a * q) = a ∧
      ∀ m : ℕ, a * q ≠ m ^ 2 := by
  have haq := lt_of_mul_lt_sq_of_root_le hRq h
  exact ⟨haq, canonicalLargestPrimeFactor_mul_prime_eq ha haq hq,
    canonicalCofactor_mul_prime_eq ha haq hq, mul_ne_sq_of_lt hq ha haq⟩

/-- Above the square-root wall the canonical greatest-prime fibre of a prime
`q` is the complete set of positive multiples of `q` below the endpoint. -/
theorem largestPrimeFactor_eq_iff_exists_mul_of_root_le {R q n : ℕ} (hq : q.Prime)
    (hRq : R ≤ q) (hnR : n < R ^ 2) :
    (1 < n ∧ canonicalLargestPrimeFactor n = q) ↔ ∃ a, 0 < a ∧ n = a * q := by
  constructor
  · rintro ⟨hn, hPq⟩
    have hprod := canonicalCofactor_mul_largestPrimeFactor hn
    rw [hPq] at hprod
    refine ⟨canonicalCofactor n, ?_, hprod.symm⟩
    rcases Nat.eq_zero_or_pos (canonicalCofactor n) with h0 | h0
    · rw [h0, Nat.zero_mul] at hprod
      omega
    · exact h0
  · rintro ⟨a, ha, rfl⟩
    have haq := lt_of_mul_lt_sq_of_root_le hRq hnR
    refine ⟨?_, canonicalLargestPrimeFactor_mul_prime_eq ha haq hq⟩
    have hq2 : 2 ≤ q := hq.two_le
    have ha1 : 1 ≤ a := by omega
    have hge : 1 * 2 ≤ a * q := Nat.mul_le_mul ha1 hq2
    omega

/-- Conversely, a source below the square endpoint whose greatest prime factor
is at or above the root has canonical cofactor strictly below that prime. -/
theorem canonicalCofactor_lt_largestPrimeFactor_of_root_le {R n : ℕ} (hn : 1 < n)
    (hnR : n < R ^ 2) (hRq : R ≤ canonicalLargestPrimeFactor n) :
    canonicalCofactor n < canonicalLargestPrimeFactor n := by
  have hprod := canonicalCofactor_mul_largestPrimeFactor hn
  have h' : canonicalCofactor n * canonicalLargestPrimeFactor n < R ^ 2 := by
    rw [hprod]
    exact hnR
  exact lt_of_mul_lt_sq_of_root_le hRq h'

/-- Inside a complete fibre, the explicit residual exclusions of the odd-seat
factor-depth partition hold exactly when the cofactor is composite. -/
theorem isOddFactorDepthResidual_mul_iff_of_lt {a q : ℕ} (hq : q.Prime) (ha : 1 < a)
    (haq : a < q) : IsOddFactorDepthResidual (a * q) ↔ ¬ a.Prime := by
  constructor
  · intro hres haPrime
    exact hres.2.1 a q haPrime hq haq rfl
  · intro haNP
    unfold IsOddFactorDepthResidual
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.not_prime_mul (by omega) hq.one_lt.ne'
    · intro p r hp hr _hpr heq
      have hqpr : q ∣ p * r := by
        rw [← heq]
        exact dvd_mul_left q a
      rcases (Nat.Prime.dvd_mul hq).mp hqpr with hqp | hqr
      · have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
        rw [← hqp'] at heq
        have h1 : a * q = r * q := by
          rw [heq, Nat.mul_comm]
        have har : a = r := Nat.eq_of_mul_eq_mul_right hq.pos h1
        exact haNP (by rw [har]; exact hr)
      · have hqr' : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp hqr
        rw [← hqr'] at heq
        have har : a = p := Nat.eq_of_mul_eq_mul_right hq.pos heq
        exact haNP (by rw [har]; exact hp)
    · intro s _hs heq
      exact mul_ne_sq_of_lt hq (by omega) haq s heq

/-- Odd composite cofactors in a complete fibre recover the sharp one-ninth
wall: `9 * q ≤ a * q`. -/
theorem nine_mul_le_of_odd_composite_cofactor {a q : ℕ} (haOdd : Odd a) (ha : 1 < a)
    (haNP : ¬ a.Prime) : 9 * q ≤ a * q :=
  Nat.mul_le_mul_right q (nine_le_of_odd_one_lt_not_prime haOdd ha haNP)

/-! ## Build-enforced axiom audit

Each `#guard_msgs` fails the warning-fatal build unless the theorem depends on
exactly the standard axioms `propext`, `Classical.choice`, `Quot.sound`. -/

/-- info: 'RHLean.Proof.completeFibre_of_root_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RHLean.Proof.completeFibre_of_root_le

/-- info: 'RHLean.Proof.largestPrimeFactor_eq_iff_exists_mul_of_root_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RHLean.Proof.largestPrimeFactor_eq_iff_exists_mul_of_root_le

/-- info: 'RHLean.Proof.canonicalCofactor_lt_largestPrimeFactor_of_root_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RHLean.Proof.canonicalCofactor_lt_largestPrimeFactor_of_root_le

/-- info: 'RHLean.Proof.isOddFactorDepthResidual_mul_iff_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RHLean.Proof.isOddFactorDepthResidual_mul_iff_of_lt

end RHLean.Proof
