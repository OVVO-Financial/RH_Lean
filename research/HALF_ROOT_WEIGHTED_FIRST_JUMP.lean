import «research.HALF_ROOT_PRIME_PAIR_FIRST_JUMP»

/-!
# Weighted first-jump realization of the half-root pair shell

The upper-half fixed-first-jump obstruction says that each actual owner state
carries slice mass exactly `-1`.  The half-root shell does not sum those slices
with coefficient one: it keeps the reciprocal-depth weight `w in {-1,0,1}`.
That nonconstant coefficient is precisely what prevents the completed-prime
collapse to the one-sign composite population.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Every nonzero half-root pair is an upper-half first-jump state whose raw
fixed-prime slice mass is exactly `-1`. -/
theorem halfRoot_nonzeroPair_firstJumpStateSlice_eq_neg_one
    {R p q : ℕ} (hR : 9 ≤ R)
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R))
    (hq : q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1))
    (hw : halfRootPrimePairWeight R p q ≠ 0) :
    signedFirstJumpPrimeStateSlice R q (1, p) = -1 := by
  rcases halfRoot_nonzeroPair_mem_firstJump_and_owner (by omega) hp hq hw with
    ⟨hqFirst, hpOwner⟩
  have hhalf : R / 2 < q :=
    (mem_frozenPrimeUniverseHighPrimeSet.mp hq).2.1
  exact upperHalfFirstJumpOwner_stateSlice_eq_neg_one
    (by omega) hqFirst hhalf hpOwner

/-- **Weighted first-jump atom identity.**  The finite prime-pair weight is the
negative of that same weight applied to the existing first-jump slice.  Unlike
the failed completed `(p,k)` coordinate, the coefficient is not summed out. -/
theorem halfRootPrimePairWeight_eq_neg_weighted_firstJumpSlice
    {R p q : ℕ} (hR : 9 ≤ R)
    (hp : p ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (squareRootEndpoint R))
    (hq : q ∈ frozenPrimeUniverseHighPrimeSet (R / 2) (p - 1)) :
    (((halfRootPrimePairWeight R p q : ℤ) : ℂ)) =
      -(((halfRootPrimePairWeight R p q : ℤ) : ℂ) *
        signedFirstJumpPrimeStateSlice R q (1, p)) := by
  by_cases hw : halfRootPrimePairWeight R p q = 0
  · simp [hw]
  · rw [halfRoot_nonzeroPair_firstJumpStateSlice_eq_neg_one hR hp hq hw]
    ring

end RHLean.Proof
