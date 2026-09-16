import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNATURE_SUCCESSOR»

/-!
# Pair-carrier form of consecutive-prime signature refinement

The energy filtration is most transparent on the ordered Gram carrier.  At
level `p`, two nonzero AMP sites interact exactly when their lower-prime
signatures below `p` agree.  Revealing the `p` coordinate keeps precisely the
pairs that also agree on p-divisibility.

For consecutive primes `p < r`, this refined pair condition is exactly equality
of the lower-prime signatures below `r`.  Thus the next filtration level is not
an estimate or relabeling: it is literally the same finite pair carrier.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Ordered nonzero AMP pairs agreeing on every prime coordinate below `p`. -/
def lowOwnerSignaturePairCarrier (R p : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerNonzeroMobiusCarrier R).product
      (lowOwnerNonzeroMobiusCarrier R)).filter fun mn =>
    squarefreeLowerPrimeSignature p mn.1 =
      squarefreeLowerPrimeSignature p mn.2

/-- The same carrier after revealing whether the current prime `p` divides each
endpoint. -/
def lowOwnerSignatureSplitPairCarrier (R p : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerNonzeroMobiusCarrier R).product
      (lowOwnerNonzeroMobiusCarrier R)).filter fun mn =>
    squarefreeLowerPrimeSignature p mn.1 =
        squarefreeLowerPrimeSignature p mn.2 ∧
      (p ∣ mn.1 ↔ p ∣ mn.2)

/-- The old lower signature never contains its own boundary prime. -/
theorem owner_not_mem_lowerPrimeSignature (p n : ℕ) :
    p ∉ squarefreeLowerPrimeSignature p n := by
  simp [squarefreeLowerPrimeSignature]

/-- If both endpoints contain the newly exposed prime, insertion of that prime
is cancellable because it was absent from both old lower signatures. -/
theorem insert_owner_lowerSignature_inj
    {p m n : ℕ}
    (h : insert p (squarefreeLowerPrimeSignature p m) =
      insert p (squarefreeLowerPrimeSignature p n)) :
    squarefreeLowerPrimeSignature p m =
      squarefreeLowerPrimeSignature p n := by
  ext q
  by_cases hqp : q = p
  · subst q
    simp [owner_not_mem_lowerPrimeSignature]
  · have hmem := congrArg (fun s : Finset ℕ => q ∈ s) h
    simpa [hqp] using hmem

/-- **Successor equality criterion.**  Between consecutive primes, equality of
successor signatures is exactly old-signature equality plus agreement on the
new p-coordinate. -/
theorem squarefreeLowerPrimeSignature_successor_eq_iff
    {p r m n : ℕ}
    (hpr : ConsecutivePrimeCoordinates p r)
    (hm : 0 < m) (hn : 0 < n) :
    squarefreeLowerPrimeSignature r m =
        squarefreeLowerPrimeSignature r n ↔
      squarefreeLowerPrimeSignature p m =
          squarefreeLowerPrimeSignature p n ∧
        (p ∣ m ↔ p ∣ n) := by
  by_cases hpm : p ∣ m
  · by_cases hpn : p ∣ n
    · rw [squarefreeLowerPrimeSignature_successor_of_dvd hpr hm hpm,
        squarefreeLowerPrimeSignature_successor_of_dvd hpr hn hpn]
      constructor
      · intro h
        exact ⟨insert_owner_lowerSignature_inj h, by simp [hpm, hpn]⟩
      · rintro ⟨hsig, _⟩
        rw [hsig]
    · rw [squarefreeLowerPrimeSignature_successor_of_dvd hpr hm hpm,
        squarefreeLowerPrimeSignature_successor_of_not_dvd hpr hn hpn]
      constructor
      · intro h
        have hpMem : p ∈ squarefreeLowerPrimeSignature p n := by
          have : p ∈ insert p (squarefreeLowerPrimeSignature p m) := by simp
          rw [h] at this
          exact this
        exact False.elim ((owner_not_mem_lowerPrimeSignature p n) hpMem)
      · rintro ⟨_hsig, hiff⟩
        exact False.elim (hpn (hiff.mp hpm))
  · by_cases hpn : p ∣ n
    · rw [squarefreeLowerPrimeSignature_successor_of_not_dvd hpr hm hpm,
        squarefreeLowerPrimeSignature_successor_of_dvd hpr hn hpn]
      constructor
      · intro h
        have hpMem : p ∈ squarefreeLowerPrimeSignature p m := by
          have : p ∈ insert p (squarefreeLowerPrimeSignature p n) := by simp
          rw [← h] at this
          exact this
        exact False.elim ((owner_not_mem_lowerPrimeSignature p m) hpMem)
      · rintro ⟨_hsig, hiff⟩
        exact False.elim (hpm (hiff.mpr hpn))
    · rw [squarefreeLowerPrimeSignature_successor_of_not_dvd hpr hm hpm,
        squarefreeLowerPrimeSignature_successor_of_not_dvd hpr hn hpn]
      constructor
      · intro h
        exact ⟨h, by simp [hpm, hpn]⟩
      · rintro ⟨h, _⟩
        exact h

/-- **Exact pair-carrier successor.**  Splitting the p-coordinate of the old
signature filtration is literally the next consecutive-prime signature
carrier. -/
theorem lowOwnerSignatureSplitPairCarrier_eq_successor
    {R p r : ℕ} (hpr : ConsecutivePrimeCoordinates p r) :
    lowOwnerSignatureSplitPairCarrier R p =
      lowOwnerSignaturePairCarrier R r := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hprod, hdata⟩
    rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
    have hmPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar).2
    have hnPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmCar, hnCar⟩,
        (squarefreeLowerPrimeSignature_successor_eq_iff
          hpr hmPos hnPos).2 hdata⟩
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hprod, hsig⟩
    rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
    have hmPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar).2
    have hnPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmCar, hnCar⟩,
        (squarefreeLowerPrimeSignature_successor_eq_iff
          hpr hmPos hnPos).1 hsig⟩

end RHLean.Proof
