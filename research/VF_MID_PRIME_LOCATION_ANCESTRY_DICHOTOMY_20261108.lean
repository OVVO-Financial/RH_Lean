import Mathlib
import «research.VF_MID_UNIFORMITY_BIAS_CORRELATION»
import «research.VF_MID_SQUARE_WHEEL_BACKLOG»
import «research.VF_MID_RECURSIVE_SCALE_DESCENT»

/-!
# Square-root prime ancestry versus the location of prime survivors

This is a source-faithful *two-channel descent*, NOT the false principle
"uniform primes in earlier square blocks force uniform primes later".

The repository ALREADY proves:
* genuine primes in (R^2,(R+1)^2) equal the full wheel through prime R;
* each composite there has a prime factor <= R;
* full VF child-owner recursive steps decrease square-root index;
* the U_R half-phase coordinate is exactly the block midpoint bias.

We retain all original candidate sites and use a strict subset decomposition:
prefix-wheel survivors = actual primes + sites killed by later owners.
A spatially biased actual prime block therefore forces bias in one of
those two channels. Only the *removed* channel has a proven smaller-prime
factor witness; that witness is NOT necessarily a bad earlier block.

The complete next theorem would quantitatively bound the signed later-owner
channel after its ancestry reassembly. No such theorem is assumed here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis
open RHLean.Proof

/-- Integer left-minus-right sign of one actual physical square-block site.
The root square itself is not in the open prime carrier. -/
def squareWheelHalfSign (R n : ℕ) : ℤ :=
  if n ≤ R ^ 2 + R then 1 else -1

/-- An exact integer half-location imbalance for ANY original site subset. -/
def squareWheelHalfMass (R : ℕ) (s : Finset ℕ) : ℤ :=
  ∑ n ∈ s, squareWheelHalfSign R n

/-- Actual primes, not random/surrogate prime sites. -/
def squareWheelPrimeHalfMass (R : ℕ) : ℤ :=
  squareWheelHalfMass R (vfMidSquareWheelPrimes R)

/-- Original square block after sieving only primes <= S. -/
def squareWheelPrefixHalfMass (S R : ℕ) : ℤ :=
  squareWheelHalfMass R (vfMidSquarePrefixWheelSurvivors S R)

/-- Survivors at cutoff S which are not genuine primes at the full cutoff R.
These are ACTUAL composite integers, not a modeled unsigned count. -/
def squareWheelLateRemovedSites (S R : ℕ) : Finset ℕ :=
  vfMidSquarePrefixWheelSurvivors S R \ vfMidSquareWheelPrimes R

def squareWheelLateRemovedHalfMass (S R : ℕ) : ℤ :=
  squareWheelHalfMass R (squareWheelLateRemovedSites S R)

/-- Exact ancestry/remainder decomposition at every original square block. -/
theorem squareWheelPrimeHalfMass_eq_prefix_sub_late
    (S R : ℕ) (hR : 2 ≤ R) (hSR : S ≤ R) :
    squareWheelPrimeHalfMass R =
      squareWheelPrefixHalfMass S R -
        squareWheelLateRemovedHalfMass S R := by
  have hsub :=
    vfMidSquareWheelPrimes_subset_prefixWheelSurvivors
      (S := S) (R := R) hR hSR
  have hpart :=
    Finset.sum_sdiff hsub (f := squareWheelHalfSign R)
  unfold squareWheelPrimeHalfMass squareWheelPrefixHalfMass
    squareWheelLateRemovedHalfMass squareWheelLateRemovedSites
    squareWheelHalfMass
  omega

/-- The complete additive/multiplicative location bill, retaining the signs.
A large spatial excursion must occur in the old wheel or the later removals. -/
theorem squareWheelPrimeHalfMass_abs_le_two_channels
    (S R : ℕ) (hR : 2 ≤ R) (hSR : S ≤ R) :
    |squareWheelPrimeHalfMass R| ≤
      |squareWheelPrefixHalfMass S R| +
        |squareWheelLateRemovedHalfMass S R| := by
  rw [squareWheelPrimeHalfMass_eq_prefix_sub_late S R hR hSR]
  simpa [sub_eq_add_neg] using
    (abs_add_le (squareWheelPrefixHalfMass S R)
      (-squareWheelLateRemovedHalfMass S R))

/-- Genuine dichotomy: no spatial-prime first-bad can be descendent-free.
The second branch is *not* the same as a bad earlier square block. -/
theorem squareWheelPrimeLarge_forces_prefix_or_late
    (S R : ℕ) (hR : 2 ≤ R) (hSR : S ≤ R)
    (T : ℤ)
    (hBad : T < |squareWheelPrimeHalfMass R|) :
    T < 2 * |squareWheelPrefixHalfMass S R| ∨
      T < 2 * |squareWheelLateRemovedHalfMass S R| := by
  have hbound :=
    squareWheelPrimeHalfMass_abs_le_two_channels S R hR hSR
  by_cases hw : T < 2 * |squareWheelPrefixHalfMass S R|
  · exact Or.inl hw
  · right
    have hw' : 2 * |squareWheelPrefixHalfMass S R| ≤ T :=
      le_of_not_gt hw
    omega

/-- If the low-prime wheel is known to be positionally uniform to tolerance
C, any bigger actual-prime cluster must be carried by NEW removals. -/
theorem squareWheelPrimeLarge_forces_late_given_prefix
    (S R : ℕ) (hR : 2 ≤ R) (hSR : S ≤ R)
    (T C : ℤ)
    (hPrefix : |squareWheelPrefixHalfMass S R| ≤ C)
    (hBad : T + C < |squareWheelPrimeHalfMass R|) :
    T < |squareWheelLateRemovedHalfMass S R| := by
  have hbound :=
    squareWheelPrimeHalfMass_abs_le_two_channels S R hR hSR
  omega

/-- Every site in the new-removal channel has an ACTUAL new owner prime
S < q <= R, with q dividing the original integer. This is the exact
prime-ancestry assertion sought by the square-root descent intuition. -/
theorem squareWheelLateRemoved_has_new_prime_factor
    {S R n : ℕ} (hR : 2 ≤ R) (_hSR : S ≤ R)
    (hn : n ∈ squareWheelLateRemovedSites S R) :
    ∃ q : ℕ, q.Prime ∧ S < q ∧ q ≤ R ∧ q ∣ n := by
  have hws :
      n ∈ vfMidSquarePrefixWheelSurvivors S R :=
    (Finset.mem_sdiff.mp hn).1
  have hnprime :
      n ∉ vfMidSquareWheelPrimes R :=
    (Finset.mem_sdiff.mp hn).2
  change n ∈ (vfMidSquareWheelSites R).filter
    (lowWheelHighSurvivor S) at hws
  rcases Finset.mem_filter.mp hws with ⟨hsite, hsurv⟩
  have hnot : ¬ n.Prime := by
    intro hp
    exact hnprime (Finset.mem_filter.mpr ⟨hsite, hp⟩)
  obtain ⟨q, hqm, hqdiv⟩ :=
    vfMidSquareBand_composite_has_commonWheel_divisor hR hsite hnot
  have hq : q.Prime ∧ q ≤ R := mem_primesUpTo.mp hqm
  refine ⟨q, hq.1, ?_, hq.2, hqdiv⟩
  by_contra hnotS
  have hqS : q ≤ S := Nat.le_of_not_gt hnotS
  have hqmS : q ∈ primesUpTo S :=
    mem_primesUpTo.mpr ⟨hq.1, hqS⟩
  exact hsurv q hqmS hqdiv

/-- Every such inherited factor occurs at STRICTLY smaller square-root
index. This is pointwise ancestry, NOT a signed-clustering descent. -/
theorem squareWheelLateRemoved_has_smaller_prime_root
    {S R n : ℕ} (hR : 2 ≤ R) (hSR : S ≤ R)
    (hn : n ∈ squareWheelLateRemovedSites S R) :
    ∃ q : ℕ, q.Prime ∧ S < q ∧ q ∣ n ∧ Nat.sqrt q < R := by
  obtain ⟨q, hq, hqS, hqR, hqdiv⟩ :=
    squareWheelLateRemoved_has_new_prime_factor hR hSR hn
  have hqr : q < R ^ 2 := by
    have hR2 : R < R ^ 2 := by nlinarith only [hR]
    omega
  refine ⟨q, hq, hqS, hqdiv, ?_⟩
  exact (Nat.sqrt_lt').2 hqr

/-- At full prime cutoff there is no missing "later owner". -/
theorem squareWheelLateRemoved_full_empty
    (R : ℕ) (hR : 2 ≤ R) :
    squareWheelLateRemovedSites R R = ∅ := by
  unfold squareWheelLateRemovedSites
  rw [vfMidSquarePrefixWheelSurvivors_full]
  rw [vfMidSquareWheelSurvivors_eq_primes R hR]
  simp

/-! ## Exact finite falsifier to naive inheritance -/

/-- The genuinely balanced square block B_2 has primes 5 left and 7 right. -/
theorem squareWheelB2_primeHalfMass_zero :
    squareWheelPrimeHalfMass 2 = 0 := by
  decide

/-- The next genuinely balanced block B_3 has 11 left and 13 right. -/
theorem squareWheelB3_primeHalfMass_zero :
    squareWheelPrimeHalfMass 3 = 0 := by
  decide

/-- B_4 has 17 and 19 left, but only 23 right. -/
theorem squareWheelB4_primeHalfMass_one :
    squareWheelPrimeHalfMass 4 = 1 := by
  decide

/-- No unconditional inheritance of perfect location uniformity:
two consecutive earlier square blocks can be perfectly balanced, while
the next block has a genuine nonzero prime phase bias. -/
theorem squareWheelEarlierBalanced_nextUnbalanced :
    squareWheelPrimeHalfMass 2 = 0 ∧
    squareWheelPrimeHalfMass 3 = 0 ∧
    squareWheelPrimeHalfMass 4 ≠ 0 := by
  exact ⟨squareWheelB2_primeHalfMass_zero,
    squareWheelB3_primeHalfMass_zero,
    by rw [squareWheelB4_primeHalfMass_one]; decide⟩

/-- The genuine prime imbalance at R=4 is nonzero. The finer 2-to-3
wheel comparison is reproduced independently by the exact integer regression,
not falsely reduced through a noncomputable Classical.propDecidable. -/
theorem squareWheelB4_primeHalfMass_ne_zero :
    squareWheelPrimeHalfMass 4 ≠ 0 := by
  rw [squareWheelB4_primeHalfMass_one]
  decide

end RHLean.Analysis
