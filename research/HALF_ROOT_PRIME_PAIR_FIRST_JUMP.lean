import «research.HALF_ROOT_PRIME_PAIR_WEIGHT»
import RHLean.Proof.FirstJumpPrimeSliceObstruction

/-!
# Half-root prime-pair shell as an existing first-jump carrier

A nonzero half-root pair weight has reciprocal depth one or three, hence its
product is physically present below `X_R`.  Because the earlier prime `q` is
already above `R/2`, physical presence forces `q <= R`.  Thus `q` is exactly an
upper-half post-root first-jump prime and the later prime `p` belongs to its
existing owner set.

So the new prime-pair shell is not a new carrier: every nonzero pair is an
actual `(1,p)` oriented state in the already-compiled first-jump/Othello
geometry.  This is the bridge needed before attacking the signed discrepancy.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Nonzero pair weight means reciprocal depth one or three. -/
theorem halfRootPrimePairWeight_ne_zero_depth
    {R p q : ℕ} (h : halfRootPrimePairWeight R p q ≠ 0) :
    squareRootEndpoint R / (p * q) = 1 ∨
      squareRootEndpoint R / (p * q) = 3 := by
  unfold halfRootPrimePairWeight at h
  by_cases h1 : squareRootEndpoint R / (p * q) = 1
  · exact Or.inl h1
  · simp [h1] at h
    by_cases h3 : squareRootEndpoint R / (p * q) = 3
    · exact Or.inr h3
    · simp [h3] at h

/-- A nonzero half-root pair is physically present below the square endpoint. -/
theorem halfRootPrimePairWeight_ne_zero_product_le_endpoint
    {R p q : ℕ}
    (hpPrime : p.Prime) (hqPrime : q.Prime)
    (h : halfRootPrimePairWeight R p q ≠ 0) :
    p * q ≤ squareRootEndpoint R := by
  have hz := halfRootPrimePairWeight_ne_zero_depth h
  have hdiv : 1 ≤ squareRootEndpoint R / (p * q) := by omega
  have hpos : 0 < p * q := Nat.mul_pos hpPrime.pos hqPrime.pos
  have hmul := (Nat.le_div_iff_mul_le hpos).1 hdiv
  simpa using hmul

/-- Once `R >= 6`, the integer square root lies below the half-root cutoff. -/
theorem sqrt_le_halfRoot
    (R : ℕ) (hR : 6 ≤ R) :
    Nat.sqrt R ≤ R / 2 := by
  have hsSq : (Nat.sqrt R) ^ 2 ≤ R := Nat.sqrt_le' R
  have hdiv : 2 * (R / 2) ≤ R := Nat.mul_div_le R 2
  have hnext : R < 2 * (R / 2 + 1) := by omega
  by_contra hnot
  have hlarge : R / 2 + 1 ≤ Nat.sqrt R := by omega
  have hsLower : (R / 2 + 1) ^ 2 ≤ (Nat.sqrt R) ^ 2 :=
    Nat.pow_le_pow_left hlarge 2
  have hhalf : 3 ≤ R / 2 := by omega
  have hsqGt : R < (R / 2 + 1) ^ 2 := by
    nlinarith
  omega

/-- **Carrier bridge.**  Every nonzero pair in the half-root shell is already
an upper-half first-jump owner incidence: `q` is the first-jump prime and `p`
is one of its later owners. -/
theorem halfRoot_nonzeroPair_mem_firstJump_and_owner
    {R p q : ℕ} (hR : 6 ≤ R)
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R))
    (hq : q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1))
    (hw : halfRootPrimePairWeight R p q ≠ 0) :
    q ∈ signedFirstJumpPostRootPrimeSet R ∧
      p ∈ upperHalfFirstJumpOwnerSet R q := by
  have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
  have hqData := mem_frozenPrimeUniverseHighPrimeSet.mp hq
  have hprod : p * q ≤ squareRootEndpoint R :=
    halfRootPrimePairWeight_ne_zero_product_le_endpoint hpData.1 hqData.1 hw
  have hqR : q ≤ R := by
    by_contra hnot
    have hRq : R < q := Nat.lt_of_not_ge hnot
    have hqp : q < p := by omega
    have hR2lt : R ^ 2 < p * q := by nlinarith
    have hXlt : squareRootEndpoint R < R ^ 2 := by
      unfold squareRootEndpoint
      have hpos : 0 < R ^ 2 := by positivity
      omega
    omega
  have hsqrt : Nat.sqrt R < q :=
    (sqrt_le_halfRoot R hR).trans_lt hqData.2.1
  have hqFirst : q ∈ signedFirstJumpPostRootPrimeSet R := by
    simp [signedFirstJumpPostRootPrimeSet, mem_frozenPrimeUniverseHighPrimeSet,
      hqData.1, hsqrt, hqR]
  have hpOwner : p ∈ upperHalfFirstJumpOwnerSet R q := by
    rw [mem_upperHalfFirstJumpOwnerSet]
    refine ⟨hpData.1, by omega, ?_⟩
    apply (Nat.le_div_iff_mul_le hqData.1.pos).2
    simpa [Nat.mul_comm] using hprod
  exact ⟨hqFirst, hpOwner⟩

/-- Consequently every nonzero pair-shell incidence names an actual oriented
state in the existing low-wheel carrier. -/
theorem halfRoot_nonzeroPair_orientedState_mem
    {R p q : ℕ} (hR : 6 ≤ R)
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R))
    (hq : q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1))
    (hw : halfRootPrimePairWeight R p q ≠ 0) :
    (1, p) ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R := by
  rcases halfRoot_nonzeroPair_mem_firstJump_and_owner hR hp hq hw with
    ⟨hqFirst, hpOwner⟩
  have hhalf : R / 2 < q :=
    (mem_frozenPrimeUniverseHighPrimeSet.mp hq).2.1
  exact upperHalfFirstJumpOwner_state_mem (by omega) hqFirst hhalf hpOwner

end RHLean.Proof
