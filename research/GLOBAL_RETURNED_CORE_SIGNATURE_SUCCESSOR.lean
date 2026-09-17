import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNATURE_FILTRATION»

/-!
# Consecutive-prime refinement of the first-owner signature filtration

If `p < r` are consecutive primes, then among prime coordinates strictly below
`r` the only coordinate not already visible strictly below `p` is `p` itself.
Hence on every positive site

  lowerSig(r,n) = lowerSig(p,n)              if p does not divide n,
                = insert p (lowerSig(p,n))   if p divides n.

This identifies the two halves of every p-cell with the next level of the
prime-coordinate filtration.  It is the local successor theorem needed to turn
the one-owner energy identity into a genuine telescoping filtration.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- There is no prime strictly between consecutive prime coordinates. -/
def ConsecutivePrimeCoordinates (p r : ℕ) : Prop :=
  p.Prime ∧ r.Prime ∧ p < r ∧
    ∀ q : ℕ, q.Prime → p < q → q < r → False

/-- A prime-factor coordinate visible below the successor prime is either
already below `p` or is exactly `p`. -/
theorem primeFactor_lt_successor_eq_lt_or_eq
    {p r n q : ℕ}
    (hpr : ConsecutivePrimeCoordinates p r)
    (hq : q ∈ squarefreePrimeFace n)
    (hqr : q < r) :
    q < p ∨ q = p := by
  have hqPrime : q.Prime := by
    simpa [squarefreePrimeFace] using Nat.prime_of_mem_primeFactors
      (show q ∈ n.primeFactors by simpa [squarefreePrimeFace] using hq)
  by_cases hqp : q < p
  · exact Or.inl hqp
  · have hpq : p ≤ q := Nat.le_of_not_gt hqp
    by_cases hpEq : q = p
    · exact Or.inr hpEq
    · have hpLtq : p < q := lt_of_le_of_ne hpq (Ne.symm hpEq)
      exact False.elim (hpr.2.2.2 q hqPrime hpLtq hqr)

/-- Successor signature when the newly exposed prime coordinate is absent. -/
theorem squarefreeLowerPrimeSignature_successor_of_not_dvd
    {p r n : ℕ}
    (hpr : ConsecutivePrimeCoordinates p r)
    (_hn : 0 < n) (hpn : ¬ p ∣ n) :
    squarefreeLowerPrimeSignature r n =
      squarefreeLowerPrimeSignature p n := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqFace, hqr⟩
    have hcase := primeFactor_lt_successor_eq_lt_or_eq hpr hqFace hqr
    rcases hcase with hqp | hqp
    · exact Finset.mem_filter.mpr ⟨hqFace, hqp⟩
    · subst q
      have hpdvd : p ∣ n := by
        simpa [squarefreePrimeFace] using
          Nat.dvd_of_mem_primeFactors
            (show p ∈ n.primeFactors by simpa [squarefreePrimeFace] using hqFace)
      exact False.elim (hpn hpdvd)
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqFace, hqp⟩
    exact Finset.mem_filter.mpr ⟨hqFace, hqp.trans hpr.2.2.1⟩

/-- Successor signature when the newly exposed prime coordinate is present. -/
theorem squarefreeLowerPrimeSignature_successor_of_dvd
    {p r n : ℕ}
    (hpr : ConsecutivePrimeCoordinates p r)
    (hn : 0 < n) (hpn : p ∣ n) :
    squarefreeLowerPrimeSignature r n =
      insert p (squarefreeLowerPrimeSignature p n) := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqFace, hqr⟩
    have hcase := primeFactor_lt_successor_eq_lt_or_eq hpr hqFace hqr
    rcases hcase with hqp | hqp
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hqFace, hqp⟩))
    · exact Finset.mem_insert.mpr (Or.inl hqp)
  · intro hq
    rcases Finset.mem_insert.mp hq with hqp | hqOld
    · subst q
      have hpFace : p ∈ squarefreePrimeFace n := by
        have hpf : p ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hpr.1, hpn, hn.ne'⟩
        simpa [squarefreePrimeFace] using hpf
      exact Finset.mem_filter.mpr ⟨hpFace, hpr.2.2.1⟩
    · rcases Finset.mem_filter.mp hqOld with ⟨hqFace, hqp⟩
      exact Finset.mem_filter.mpr ⟨hqFace, hqp.trans hpr.2.2.1⟩

/-- Uniform successor formula. -/
theorem squarefreeLowerPrimeSignature_successor
    {p r n : ℕ}
    (hpr : ConsecutivePrimeCoordinates p r)
    (hn : 0 < n) :
    squarefreeLowerPrimeSignature r n =
      if p ∣ n then
        insert p (squarefreeLowerPrimeSignature p n)
      else squarefreeLowerPrimeSignature p n := by
  by_cases hpn : p ∣ n
  · simp [hpn, squarefreeLowerPrimeSignature_successor_of_dvd hpr hn hpn]
  · simp [hpn, squarefreeLowerPrimeSignature_successor_of_not_dvd hpr hn hpn]

/-- An occupied lower-p signature can never already contain p. -/
theorem owner_not_mem_occupied_lowerSignature
    {R p : ℕ} {sig : Finset ℕ}
    (hsig : sig ∈ lowOwnerFirstOwnerSignatureSet R p) :
    p ∉ sig := by
  rcases Finset.mem_image.mp hsig with ⟨n, _hnCar, rfl⟩
  simp [squarefreeLowerPrimeSignature]

/-- Consecutive-prime refinement separates the old p-free and p-divisible
branches into distinct successor signatures. -/
theorem base_child_successor_signatures_distinct
    {R p r : ℕ} {sig : Finset ℕ}
    (hpr : ConsecutivePrimeCoordinates p r)
    (hsig : sig ∈ lowOwnerFirstOwnerSignatureSet R p)
    {a b : ℕ}
    (ha : a ∈ lowOwnerFirstOwnerBaseFiber R p sig)
    (hb : b ∈ lowOwnerFirstOwnerChildFiber R p sig) :
    squarefreeLowerPrimeSignature r a = sig ∧
      squarefreeLowerPrimeSignature r b = insert p sig ∧
      sig ≠ insert p sig := by
  have haCar := (Finset.mem_filter.mp ha).1
  have hbCar := (Finset.mem_filter.mp hb).1
  have haPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar).2
  have hbPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hbCar).2
  have haData := (Finset.mem_filter.mp ha).2
  have hbData := (Finset.mem_filter.mp hb).2
  have haSucc := squarefreeLowerPrimeSignature_successor_of_not_dvd
    hpr haPos haData.2
  have hbSucc := squarefreeLowerPrimeSignature_successor_of_dvd
    hpr hbPos hbData.2
  have hpnot := owner_not_mem_occupied_lowerSignature hsig
  refine ⟨?_, ?_, ?_⟩
  · simpa [haData.1] using haSucc
  · simpa [hbData.1] using hbSucc
  · intro heq
    have : p ∈ sig := by
      rw [heq]
      simp
    exact hpnot this

end RHLean.Proof
