import Mathlib
import RHLean.Arithmetic.PrimeWheelCorrectedLocalFlip

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-!
# No-go theorem for the literal physical collision-site fibre

The nine CRT collision labels record actual prime-square hits.  If a label is
weighted on that same physical square-hit site, the corrected prime-wheel field
is identically zero there.  Thus the current literal collision-site fibre cannot
carry a nonzero corrected-field quotient.

This does not rule out a transported quotient in a different arithmetic fibre.
It proves that such transport is necessary.

The adjacent-cell escape is also unavailable for `p >= 7`: after a current
`p^2` hit, every active site in the next cell is a `p`-miss, so the neighboring
cell cannot realize the required local exponent-state flip.
-/

@[simp] theorem localPrimeExponentState_eq_two_of_square_hit
    (p n : ℕ) (hsq : p ^ 2 ∣ n) :
    localPrimeExponentState p n = 2 := by
  simp [localPrimeExponentState, hsq]

@[simp] theorem localPrimeExponentState_eq_zero_of_not_dvd
    (p n : ℕ) (hnot : ¬ p ∣ n) :
    localPrimeExponentState p n = 0 := by
  have hsq : ¬ p ^ 2 ∣ n := by
    intro h
    apply hnot
    exact dvd_trans (dvd_pow_self p (by norm_num)) h
  simp [localPrimeExponentState, hsq, hnot]

/-- A literal adjacent-cell continuation of a square collision cannot implement
`primeCombExponentFlip` for any selected prime `p >= 7`.  The current site has
state `2`, whose flip is again `2`, while every active site in the next cell has
state `0`. -/
theorem adjacent_threeSlot_exponentFlip_impossible_of_square_hit
    (p k i j : ℕ)
    (hp : 6 < p)
    (hi : i < 3) (hj : j < 3)
    (hsq : p ^ 2 ∣ threeSlotValue k i) :
    localPrimeExponentState p (threeSlotValue (k + 1) j) ≠
      primeCombExponentFlip
        (localPrimeExponentState p (threeSlotValue k i)) := by
  have hnext : ¬ p ∣ threeSlotValue (k + 1) j :=
    prime_not_dvd_next_threeSlotValue_of_square_hit
      p k i j hp hi hj hsq
  rw [localPrimeExponentState_eq_zero_of_not_dvd p _ hnext,
    localPrimeExponentState_eq_two_of_square_hit p _ hsq]
  simp [primeCombExponentFlip]

/-- A collision label weighted on a literal selected-prime square-hit site has
zero corrected prime-wheel weight. -/
theorem correctedCollisionSiteWeight_eq_zero_of_literal_square_hit
    (S : Finset ℕ) (upper p : ℕ)
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (s : TwoPrimeCollisionState)
    (hsquare : p ^ 2 ∣ site s) :
    correctedCollisionSiteWeight S upper site s = 0 := by
  unfold correctedCollisionSiteWeight
  exact correctedPrimeWheelSite_eq_zero_of_square_hit
    S upper p (site s) hpS hsquare

/-- Hence the corrected-field mass of every finite literal collision frontier is
zero, independently of the pairing involution and cutoff. -/
theorem sum_correctedCollisionSiteWeight_eq_zero_of_literal_square_hit
    (S : Finset ℕ) (upper p : ℕ)
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (F : Finset TwoPrimeCollisionState)
    (hsquare : ∀ s ∈ F, p ^ 2 ∣ site s) :
    (∑ s ∈ F, correctedCollisionSiteWeight S upper site s) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro s hs
  exact correctedCollisionSiteWeight_eq_zero_of_literal_square_hit
    S upper p site hpS s (hsquare s hs)

end RHLean.Arithmetic
