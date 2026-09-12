import RHLean.Proof.StableFarWallRenewalTerminal

/-!
# Prime-count form of terminal stable-far renewal multiplicity

For a fixed far prime `p`, put `A = floor(X_R / p)`.  Since `p > R`, one has
`A < R`.  The exact unit-terminal condition

  q*p <= X_R < q^2*p

is therefore equivalent to

  sqrt(A) < q <= A.

So the number of incoming renewal branches at the unit terminal `(1,p)` is
literally the number of primes in the reciprocal interval `(sqrt A, A]`.
This identifies the owner multiplicity left visible by `StableFarWallOwnedCensus`
with the prime-count gap already used elsewhere in the square-root architecture.
No estimate is taken.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

/-- A far prime has reciprocal cofactor cutoff strictly below the root. -/
theorem farPrime_reciprocalCutoff_lt_root
    {R p : ℕ} (hR : 2 ≤ R) (hpFar : R + 8 ≤ p) :
    squareRootEndpoint R / p < R := by
  have hpPos : 0 < p := by omega
  apply (Nat.div_lt_iff_lt_mul hpPos).2
  have hXlt : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    simpa [pow_two] using Nat.sub_lt hpos (by norm_num : 0 < 1)
  have hRp : R < p := by omega
  have hRRp : R * R < R * p := Nat.mul_lt_mul_of_pos_left hRp (by omega)
  exact hXlt.trans hRRp

/-- **Terminal-owner interval.**  The incoming owners of the unit renewal state
at a fixed far prime are exactly the primes in `(sqrt(X_R/p), X_R/p]`. -/
theorem lowWheelFarPrimeUnitCrossingOwners_eq_reciprocalPrimeInterval
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpFar : R + 8 ≤ p) :
    lowWheelFarPrimeUnitCrossingOwners R p =
      (Finset.Ioc
        (Nat.sqrt (squareRootEndpoint R / p))
        (squareRootEndpoint R / p)).filter Nat.Prime := by
  ext q
  have hpPos : 0 < p := hp.pos
  have hAlt : squareRootEndpoint R / p < R :=
    farPrime_reciprocalCutoff_lt_root hR hpFar
  constructor
  · intro hq
    rcases mem_lowWheelFarPrimeUnitCrossingOwners.mp hq with
      ⟨hqPrime, _hqR, hqp, hq2p⟩
    have hqLe : q ≤ squareRootEndpoint R / p :=
      (Nat.le_div_iff_mul_le hpPos).2 hqp
    have hAq2 : squareRootEndpoint R / p < q * q :=
      (Nat.div_lt_iff_lt_mul hpPos).2 (by
        simpa [Nat.mul_assoc] using hq2p)
    have hsqrt : Nat.sqrt (squareRootEndpoint R / p) < q := by
      apply (Nat.sqrt_lt').2
      simpa [pow_two] using hAq2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hsqrt, hqLe⟩, hqPrime⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
    rcases Finset.mem_Ioc.mp hqIoc with ⟨hsqrt, hqLe⟩
    have hqR : q ≤ R - 1 := by omega
    have hqp : q * p ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hpPos).1 hqLe
    have hAq2 : squareRootEndpoint R / p < q ^ 2 :=
      (Nat.sqrt_lt').1 hsqrt
    have hq2p : squareRootEndpoint R < q * q * p := by
      have := (Nat.div_lt_iff_lt_mul hpPos).1 hAq2
      simpa [pow_two, Nat.mul_assoc] using this
    exact mem_lowWheelFarPrimeUnitCrossingOwners.mpr
      ⟨hqPrime, hqR, hqp, hq2p⟩

/-- The terminal renewal multiplicity is exactly a prime-count gap.  The
additive form avoids any natural-subtraction truncation. -/
theorem unitCrossingOwner_card_add_primeCounting_sqrt_eq
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpFar : R + 8 ≤ p) :
    (lowWheelFarPrimeUnitCrossingOwners R p).card +
        Nat.primeCounting (Nat.sqrt (squareRootEndpoint R / p)) =
      Nat.primeCounting (squareRootEndpoint R / p) := by
  rw [lowWheelFarPrimeUnitCrossingOwners_eq_reciprocalPrimeInterval hR hp hpFar]
  exact primeCard_Ioc_add_primeCounting_eq (Nat.sqrt_le_self _)

end RHLean.Proof
