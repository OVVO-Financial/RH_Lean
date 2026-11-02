import Mathlib

/-!
# Lifted prime-square Möbius addresses

This module formalizes the accepted structural core of claim
`20261101-owner-4`.  A nonzero Möbius cofactor lifted to the physical address
`q^2 * m` remembers its prime owner and cofactor.  Such a daughter address
cannot lie in the nonzero-Möbius outer square shell.

These are finite carrier and injectivity theorems.  They prove no sign or bound
for the remaining nonzero-shift covariance.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Literal nonzero-Möbius outer addresses in the strict square shell. -/
def liftedMobiusOuterCarrier (R : ℕ) : Finset ℕ :=
  (Finset.Ico (R ^ 2) ((R + 1) ^ 2)).filter fun a => μ a ≠ 0

/-- Literal old-owner daughters in the strict square shell. -/
def liftedMobiusDaughterCarrier (R : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range R).product (Finset.range ((R + 1) ^ 2))).filter fun qm =>
    qm.1.Prime ∧ Odd qm.1 ∧ qm.1 ^ 2 < R ∧
      R ^ 2 ≤ qm.1 ^ 2 * qm.2 ∧
      qm.1 ^ 2 * qm.2 < (R + 1) ^ 2 ∧ μ qm.2 ≠ 0

/-- Physical address of a prime-square daughter occurrence. -/
def liftedMobiusDaughterAddress (qm : ℕ × ℕ) : ℕ :=
  qm.1 ^ 2 * qm.2

@[simp] theorem mem_liftedMobiusOuterCarrier {R a : ℕ} :
    a ∈ liftedMobiusOuterCarrier R ↔
      R ^ 2 ≤ a ∧ a < (R + 1) ^ 2 ∧ μ a ≠ 0 := by
  simp [liftedMobiusOuterCarrier, and_assoc]

@[simp] theorem mem_liftedMobiusDaughterCarrier {R q m : ℕ} :
    (q, m) ∈ liftedMobiusDaughterCarrier R ↔
      q < R ∧ m < (R + 1) ^ 2 ∧ q.Prime ∧ Odd q ∧ q ^ 2 < R ∧
        R ^ 2 ≤ q ^ 2 * m ∧ q ^ 2 * m < (R + 1) ^ 2 ∧ μ m ≠ 0 := by
  simp [liftedMobiusDaughterCarrier, and_assoc]

/-- Two prime-square lifts of squarefree cofactors can agree only when both
prime owner and cofactor agree. -/
theorem primeSquare_mul_eq_primeSquare_mul_of_squarefree
    {p q m n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hn : Squarefree n)
    (h : p ^ 2 * m = q ^ 2 * n) :
    p = q ∧ m = n := by
  have hpq : p = q := by
    by_contra hpq
    have hcop : Nat.Coprime (p ^ 2) (q ^ 2) :=
      Nat.coprime_pow_primes 2 2 hp hq hpq
    have hp2div : p ^ 2 ∣ q ^ 2 * n := by
      rw [← h]
      exact dvd_mul_right (p ^ 2) m
    have hp2n : p ^ 2 ∣ n := hcop.dvd_of_dvd_mul_left hp2div
    exact (Nat.squarefree_iff_prime_squarefree.mp hn p hp) (by
      simpa [pow_two] using hp2n)
  subst q
  refine ⟨rfl, ?_⟩
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h

/-- The physical daughter-address map loses no multiplicity on the literal
accepted carrier. -/
theorem liftedMobiusDaughterAddress_injOn (R : ℕ) :
    Set.InjOn liftedMobiusDaughterAddress
      (liftedMobiusDaughterCarrier R : Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  rcases x with ⟨p, m⟩
  rcases y with ⟨q, n⟩
  have hx' : (p, m) ∈ liftedMobiusDaughterCarrier R := hx
  have hy' : (q, n) ∈ liftedMobiusDaughterCarrier R := hy
  rw [mem_liftedMobiusDaughterCarrier] at hx' hy'
  change p ^ 2 * m = q ^ 2 * n at hxy
  have hn : Squarefree n :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hy'.2.2.2.2.2.2.2
  have hdata :=
    primeSquare_mul_eq_primeSquare_mul_of_squarefree
      hx'.2.2.1 hy'.2.2.1 hn hxy
  exact Prod.ext hdata.1 hdata.2

/-- A nonzero-Möbius outer address cannot equal a prime-square daughter
address. -/
theorem liftedMobiusOuter_ne_daughterAddress
    {R a q m : ℕ} (ha : a ∈ liftedMobiusOuterCarrier R)
    (hqm : (q, m) ∈ liftedMobiusDaughterCarrier R) :
    a ≠ liftedMobiusDaughterAddress (q, m) := by
  rw [mem_liftedMobiusOuterCarrier] at ha
  rw [mem_liftedMobiusDaughterCarrier] at hqm
  intro heq
  have hsq : Squarefree a :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp ha.2.2
  have hnot : ¬ q ^ 2 ∣ a := by
    simpa [pow_two] using
      (Nat.squarefree_iff_prime_squarefree.mp hsq q hqm.2.2.1)
  apply hnot
  rw [heq]
  exact dvd_mul_right (q ^ 2) m

#print axioms primeSquare_mul_eq_primeSquare_mul_of_squarefree
#print axioms liftedMobiusDaughterAddress_injOn
#print axioms liftedMobiusOuter_ne_daughterAddress

end RHLean.Proof
