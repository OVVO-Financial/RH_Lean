import Mathlib
import RHLean.Arithmetic.PrimeWheelCorrectedLocalFlip
import RHLean.Analysis.SquarePrefixMertensBridge

open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace RHLean.Arithmetic

/-!
# No-go theorem for literal physical collision-site quotients

The nine CRT collision labels record actual prime-square hits.  A literal site
realization therefore assigns each label to a site divisible by the selected
prime square.  But the corrected prime-wheel field is identically zero at every
such site.  Consequently no quotient whose weights live on the same physical
square-hit sites can represent a nonzero square-prefix Mertens value.

This closes the current literal collision-site coordinate system.  It does not
rule out a quotient in a different arithmetic fibre: such a construction would
have to transport each collision label to a non-square-hit site while proving
that the transported weight still represents the square-block mass.

The second theorem below also rules out the most immediate adjacent-cell escape.
For `p >= 7`, a `p^2` hit in the current three-slot cell forces all three active
sites in the next cell to be `p`-misses, so the adjacent cell cannot realize the
required local exponent-state flip.
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

/-- If every collision label is weighted at a literal selected-prime square-hit
site, every corrected collision weight is zero. -/
theorem correctedCollisionSiteWeight_eq_zero_of_literal_square_hit
    (S : Finset ℕ) (upper p : ℕ)
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (hsquare : ∀ s : TwoPrimeCollisionState, p ^ 2 ∣ site s) :
    ∀ s : TwoPrimeCollisionState,
      correctedCollisionSiteWeight S upper site s = 0 := by
  intro s
  unfold correctedCollisionSiteWeight
  exact correctedPrimeWheelSite_eq_zero_of_square_hit
    S upper p (site s) hpS (hsquare s)

/-- Hence the corrected-field mass of every finite literal collision frontier is
zero, independently of the pairing involution and independently of the cutoff. -/
theorem sum_correctedCollisionSiteWeight_eq_zero_of_literal_square_hit
    (S : Finset ℕ) (upper p : ℕ)
    (site : TwoPrimeCollisionState → ℕ)
    (hpS : p ∈ S)
    (hsquare : ∀ s : TwoPrimeCollisionState, p ^ 2 ∣ site s)
    (F : Finset TwoPrimeCollisionState) :
    (∑ s ∈ F, correctedCollisionSiteWeight S upper site s) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro s _hs
  exact correctedCollisionSiteWeight_eq_zero_of_literal_square_hit
    S upper p site hpS hsquare s

/-- The strongest literal use of the current CRT coordinate system: one finite
collision-prefix frontier, weighted directly by corrected prime-wheel values on
sites that realize the selected-prime square collision, is required to represent
one exact square-prefix Mertens value. -/
structure LiteralCollisionPrefixQuotient (n : ℕ) where
  S : Finset ℕ
  upper : ℕ
  p : ℕ
  q : ℕ
  K : ℕ
  hcop : Nat.Coprime (p ^ 2) (q ^ 2)
  site : TwoPrimeCollisionState → ℕ
  selected : p ∈ S
  literal_square_hit : ∀ s : TwoPrimeCollisionState, p ^ 2 ∣ site s
  represents :
    RHLean.Analysis.squarePrefixMertens n =
      ((∑ s ∈ collisionExponentStatePrefixFrontier p q K hcop,
          correctedCollisionSiteWeight S upper site s : ℤ) : ℂ)

namespace LiteralCollisionPrefixQuotient

/-- Every literal collision-prefix quotient forces its represented square-prefix
Mertens value to vanish. -/
theorem target_eq_zero
    {n : ℕ} (Q : LiteralCollisionPrefixQuotient n) :
    RHLean.Analysis.squarePrefixMertens n = 0 := by
  rw [Q.represents]
  rw [sum_correctedCollisionSiteWeight_eq_zero_of_literal_square_hit
    Q.S Q.upper Q.p Q.site Q.selected Q.literal_square_hit
    (collisionExponentStatePrefixFrontier Q.p Q.q Q.K Q.hcop)]
  norm_num

end LiteralCollisionPrefixQuotient

/-- The first nontrivial square prefix is already nonzero. -/
theorem squarePrefixMertens_one_eq_neg_one :
    RHLean.Analysis.squarePrefixMertens 1 = -1 := by
  norm_num [RHLean.Analysis.squarePrefixMertens,
    RHLean.Analysis.squarePrefixEndpoint,
    RHLean.Analysis.mertensSummatory,
    ArithmeticFunction.moebius_apply_prime]

/-- **Literal collision-coordinate no-go.**  No current-coordinate quotient can
represent even the first nontrivial square prefix if every label is weighted on
its own physical selected-prime square-hit site. -/
theorem no_literalCollisionPrefixQuotient_at_one :
    ¬ Nonempty (LiteralCollisionPrefixQuotient 1) := by
  rintro ⟨Q⟩
  have hzero := Q.target_eq_zero
  rw [squarePrefixMertens_one_eq_neg_one] at hzero
  norm_num at hzero

/-- Therefore a global literal collision-prefix quotient statement is false.
Any viable bounded-multiplicity quotient must leave the present collision-site
fibre and construct a separately justified transported arithmetic fibre. -/
def LiteralCollisionPrefixQuotientStatement : Prop :=
  ∀ n : ℕ, Nonempty (LiteralCollisionPrefixQuotient n)

/-- Global no-go for the literal current-coordinate quotient. -/
theorem not_literalCollisionPrefixQuotientStatement :
    ¬ LiteralCollisionPrefixQuotientStatement := by
  intro h
  exact no_literalCollisionPrefixQuotient_at_one (h 1)

end RHLean.Arithmetic
