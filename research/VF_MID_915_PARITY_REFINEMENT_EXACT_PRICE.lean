import Mathlib
import «research.VF_MID_915_TERMINAL_TOP_THIRD_TRANSPORT»
import «research.VF_MID_FIRST_BAD_NORMALIZED_PARTIAL_MOMENT»

/-!
# #915: exact NNS parity-refinement price for 2p composite children

The full integer carrier provides real 2q composite children to large primes
q in (sqrt(X),X/2], but every such even child has ZERO weight in the ORIGINAL
odd-seat VF physical source. A parity-refined even-inclusive VF charge can
preserve the original signed source by halving w across each odd/even seat
pair, but its absolute NNS mass INCREASES by exactly w * P_R.

The exact squared-mass cost is 2*M_original*(w*P_R)+(w*P_R)^2.
No historical mass is added for free. The cost is *not* a payment of
the first-bad hbalance or a proof of RH.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis
open RHLean.Arithmetic RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- Split the original odd charge w-b across odd/even halves,
where b is a genuine 0/1 actual prime event. Signed mass is conserved. -/
theorem vfMid915ParitySplit_signed (w b : ℝ) :
    (w / 2 - b) + (w / 2) = w - b := by ring

/-- The full 2-seat absolute charge contains a *strictly accountable*
positive premium w per actual prime and zero premium per composite. -/
theorem vfMid915ParitySplit_abs_zero
    (w : ℝ) (hw : 0 ≤ w) :
    |w / 2 - 0| + |w / 2| = |w - 0| := by
  have hw2 : 0 ≤ w / 2 := by positivity
  rw [sub_zero, sub_zero, abs_of_nonneg hw2, abs_of_nonneg hw]
  ring

theorem vfMid915ParitySplit_abs_one
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    |w / 2 - 1| + |w / 2| = |w - 1| + w := by
  have hw2 : 0 ≤ w / 2 := by positivity
  have hn1 : w / 2 - 1 ≤ 0 := by linarith
  have hn2 : w - 1 ≤ 0 := by linarith
  rw [abs_of_nonpos hn1, abs_of_nonneg hw2, abs_of_nonpos hn2]
  ring

/-- At a GENUINE PRIME, the favorable local opposite-sign
odd/even pair heat equals the exact squared-absolute-mass inflation.
It is therefore NOT new paid NNS capacity. -/
theorem vfMid915ParitySplit_primePairHeat_eq_exactLocalPrice
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    (|w / 2 - 1| + |w / 2|) ^ 2 - (w - 1) ^ 2 =
      -4 * (w / 2 - 1) * (w / 2) := by
  have hw2 : 0 ≤ w / 2 := by positivity
  have hn1 : w / 2 - 1 ≤ 0 := by linarith
  rw [abs_of_nonpos hn1, abs_of_nonneg hw2]
  ring

/-- Even full-clock pairing gives ZERO local heat on composite odd seats,
and exactly (2w-w^2) per actual prime. -/
theorem vfMid915ParitySplit_quadraticPrice_event
    (w b : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hb : b = 0 ∨ b = 1) :
    (|w / 2 - b| + |w / 2|) ^ 2 -
      (w - b) ^ 2 = (2 * w - w ^ 2) * b := by
  rcases hb with hb | hb
  · subst b
    have hw2 : 0 ≤ w / 2 := by positivity
    rw [sub_zero, sub_zero, abs_of_nonneg hw2]
    ring
  · subst b
    have hw2 : 0 ≤ w / 2 := by positivity
    have hn1 : w / 2 - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos hn1, abs_of_nonneg hw2]
    ring

/-- The prime/composite case-split is on the ACTUAL sieve, not floor Li. -/
theorem vfMid915ParitySplit_physicalSeatAbs
    (R n : ℕ) (hR : 3 ≤ R) :
    |vfMidOddFractionalPrimeSeatWeight R / 2 -
        vfMidActualPrimeSeatMass n| +
      |vfMidOddFractionalPrimeSeatWeight R / 2| =
    |vfMidOddSignedSeatCharge R n| +
      vfMidOddFractionalPrimeSeatWeight R *
        vfMidActualPrimeSeatMass n := by
  have hw0 :=
    vfMidOddFractionalPrimeSeatWeight_nonneg R (by omega : 2 ≤ R)
  have hw1 :=
    vfMidOddFractionalPrimeSeatWeight_le_one_of_three_le R hR
  unfold vfMidOddSignedSeatCharge vfMidActualPrimeSeatMass
  by_cases hp : n.Prime
  · simp only [if_pos hp, mul_one]
    exact vfMid915ParitySplit_abs_one
      (vfMidOddFractionalPrimeSeatWeight R) hw0 hw1
  · simp only [if_neg hp, mul_zero, add_zero]
    exact vfMid915ParitySplit_abs_zero
      (vfMidOddFractionalPrimeSeatWeight R) hw0

/-- Actual physical square-prime indicator: a pointwise 0/1 atom. -/
theorem vfMid915ActualPrimeSeatMass_zero_or_one (n : ℕ) :
    vfMidActualPrimeSeatMass n = 0 ∨
      vfMidActualPrimeSeatMass n = 1 := by
  unfold vfMidActualPrimeSeatMass
  by_cases hp : n.Prime
  · simp [hp]
  · simp [hp]

/-- Exact numerical local opposite-sign heat (and its compensating
absolute-norm premium) on each actual odd VF site. -/
theorem vfMid915ParitySplit_physicalSeatQuadraticPrice
    (R n : ℕ) (hR : 3 ≤ R) :
    (|vfMidOddFractionalPrimeSeatWeight R / 2 -
        vfMidActualPrimeSeatMass n| +
      |vfMidOddFractionalPrimeSeatWeight R / 2|) ^ 2 -
       (vfMidOddSignedSeatCharge R n) ^ 2 =
      (2 * vfMidOddFractionalPrimeSeatWeight R -
        vfMidOddFractionalPrimeSeatWeight R ^ 2) *
        vfMidActualPrimeSeatMass n := by
  have hw0 :=
    vfMidOddFractionalPrimeSeatWeight_nonneg R (by omega : 2 ≤ R)
  have hw1 :=
    vfMidOddFractionalPrimeSeatWeight_le_one_of_three_le R hR
  have hevent := vfMid915ParitySplit_quadraticPrice_event
    (vfMidOddFractionalPrimeSeatWeight R)
    (vfMidActualPrimeSeatMass n)
    hw0 hw1 (vfMid915ActualPrimeSeatMass_zero_or_one n)
  simpa [vfMidOddSignedSeatCharge] using hevent

/-- TOTAL local pair heat that can possibly be credited to splitting
the current odd prime charges into even/odd halves. This is NOT an
actual pair-CODIV history reconstruction and cannot be spent twice. -/
def vfMid915ParityRefinedLocalPairHeat (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidOddCandidateSeats R,
    ((|vfMidOddFractionalPrimeSeatWeight R / 2 -
         vfMidActualPrimeSeatMass n| +
       |vfMidOddFractionalPrimeSeatWeight R / 2|) ^ 2 -
      (vfMidOddSignedSeatCharge R n) ^ 2)

/-- No mysterious large per-site negative heat: its exact total is
(2*w_R-w_R^2)*P_R. At R=1027 this is about 38.55, versus >15669
of GLOBAL NNS-square restoration cost for full parity refinement. -/
theorem vfMid915ParityRefinedLocalPairHeat_eq_coefficient_mul_primeSupply
    (R : ℕ) (hR : 3 ≤ R) :
    vfMid915ParityRefinedLocalPairHeat R =
      (2 * vfMidOddFractionalPrimeSeatWeight R -
        vfMidOddFractionalPrimeSeatWeight R ^ 2) *
        (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  unfold vfMid915ParityRefinedLocalPairHeat
  calc
    (∑ n ∈ vfMidOddCandidateSeats R,
      ((|vfMidOddFractionalPrimeSeatWeight R / 2 -
           vfMidActualPrimeSeatMass n| +
         |vfMidOddFractionalPrimeSeatWeight R / 2|) ^ 2 -
        (vfMidOddSignedSeatCharge R n) ^ 2)) =
      ∑ n ∈ vfMidOddCandidateSeats R,
        (2 * vfMidOddFractionalPrimeSeatWeight R -
          vfMidOddFractionalPrimeSeatWeight R ^ 2) *
          vfMidActualPrimeSeatMass n := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact vfMid915ParitySplit_physicalSeatQuadraticPrice R n hR
    _ = (2 * vfMidOddFractionalPrimeSeatWeight R -
          vfMidOddFractionalPrimeSeatWeight R ^ 2) *
        (∑ n ∈ vfMidOddCandidateSeats R,
           vfMidActualPrimeSeatMass n) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [vfMidActualPrimeSeatMass_sum_oddCandidates R
        (by omega : 2 ≤ R)]

/-- Half of VF expectation is attached to each of the two parity seats;
the actual prime event is attached to its odd seat. Every even mate
contains no actual prime in the original integer square band. -/
def vfMid915ParityRefinedCurrentAbs (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidOddCandidateSeats R,
    (|vfMidOddFractionalPrimeSeatWeight R / 2 -
       vfMidActualPrimeSeatMass n| +
     |vfMidOddFractionalPrimeSeatWeight R / 2|)

/-- Exact *physical*, not estimated, NNS L1 restoration premium:
refined_current_abs - original_odd_current_abs = w_R * P_R. -/
theorem vfMid915ParityRefinedCurrentAbs_eq_original_add_primePremium
    (R : ℕ) (hR : 3 ≤ R) :
    vfMid915ParityRefinedCurrentAbs R =
      (∑ n ∈ vfMidOddCandidateSeats R,
        |vfMidOddSignedSeatCharge R n|) +
      vfMidOddFractionalPrimeSeatWeight R *
        (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  unfold vfMid915ParityRefinedCurrentAbs
  calc
    (∑ n ∈ vfMidOddCandidateSeats R,
      (|vfMidOddFractionalPrimeSeatWeight R / 2 -
         vfMidActualPrimeSeatMass n| +
       |vfMidOddFractionalPrimeSeatWeight R / 2|)) =
      ∑ n ∈ vfMidOddCandidateSeats R,
        (|vfMidOddSignedSeatCharge R n| +
         vfMidOddFractionalPrimeSeatWeight R *
           vfMidActualPrimeSeatMass n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact vfMid915ParitySplit_physicalSeatAbs R n hR
    _ = (∑ n ∈ vfMidOddCandidateSeats R,
          |vfMidOddSignedSeatCharge R n|) +
        vfMidOddFractionalPrimeSeatWeight R *
          (∑ n ∈ vfMidOddCandidateSeats R,
             vfMidActualPrimeSeatMass n) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by
      rw [vfMidActualPrimeSeatMass_sum_oddCandidates R
        (by omega : 2 ≤ R)]

/-- Same original signed historical anchor, with the price of a
FULL-INTEGER parity refinement paid explicitly in the denominator. -/
def vfMid915ParityRefinedCurrentNNSMass (R : ℕ) : ℝ :=
  (|vfMidActualPrimeEndpointDefect R| +
    vfMid915ParityRefinedCurrentAbs R) ^ 2

/-- The full clock costs EXACTLY 2*M*delta+delta^2 in squared mass,
where delta=w_R*P_R and M is the ORIGINAL compressed-anchor NNS norm.
This must be restored before any 2q return heat is used. -/
theorem vfMid915ParityRefinedCurrentNNSMass_eq_original_add_exactPrice
    (R : ℕ) (hR : 3 ≤ R) :
    vfMid915ParityRefinedCurrentNNSMass R =
      vfMidFirstBadZeroTargetTotalMass R +
      2 * (|vfMidActualPrimeEndpointDefect R| +
        ∑ n ∈ vfMidOddCandidateSeats R,
          |vfMidOddSignedSeatCharge R n|) *
        (vfMidOddFractionalPrimeSeatWeight R *
          (vfMidIntegerBlockPrimeSupply R : ℝ)) +
      (vfMidOddFractionalPrimeSeatWeight R *
        (vfMidIntegerBlockPrimeSupply R : ℝ)) ^ 2 := by
  rw [vfMidFirstBadZeroTargetTotalMass_eq]
  unfold vfMid915ParityRefinedCurrentNNSMass
  rw [vfMid915ParityRefinedCurrentAbs_eq_original_add_primePremium R hR]
  ring


/-! ## Genuine signed quantitative inequality: no free 2q NNS payment -/

/-- A pure scalar ORIGINAL-denominator inequality. Splitting a w-weighted
prime into one negative odd and one positive even contribution incurs
more quadratic NNS inflation than the sum of its local opposite-sign
pair heats: price >= (#actual primes) * local_heat. -/
theorem vfMid915ParitySplit_globalPrice_ge_count_mul_localHeat
    (M w p : ℝ) (hw : 0 ≤ w) (hp : 0 ≤ p)
    (hM : (1 - w) * p ≤ M) :
    p * ((2 * w - w ^ 2) * p) ≤
      2 * M * (w * p) + (w * p) ^ 2 := by
  have hwp : 0 ≤ w * p := mul_nonneg hw hp
  have hmul := mul_le_mul_of_nonneg_right hM hwp
  calc
    p * ((2 * w - w ^ 2) * p) =
        2 * ((1 - w) * p) * (w * p) + (w * p) ^ 2 := by ring
    _ ≤ 2 * M * (w * p) + (w * p) ^ 2 := by
      linarith [hmul]

/-- Original physical odd-seat absolute mass contains at least
(1-w_R) times EVERY actual prime seat. No reference Li-only event
is allowed to count as a physical negative prime. -/
theorem vfMid915OriginalOddAbs_ge_actualPrimePart
    (R : ℕ) (hR : 3 ≤ R) :
    (1 - vfMidOddFractionalPrimeSeatWeight R) *
      (vfMidIntegerBlockPrimeSupply R : ℝ) ≤
      ∑ n ∈ vfMidOddCandidateSeats R,
        |vfMidOddSignedSeatCharge R n| := by
  have hw0 :=
    vfMidOddFractionalPrimeSeatWeight_nonneg R (by omega : 2 ≤ R)
  have hw1 :=
    vfMidOddFractionalPrimeSeatWeight_le_one_of_three_le R hR
  have hpoint (n : ℕ) :
      (1 - vfMidOddFractionalPrimeSeatWeight R) *
        vfMidActualPrimeSeatMass n ≤
        |vfMidOddSignedSeatCharge R n| := by
    by_cases hp : n.Prime
    · have hcomp : 0 ≤ 1 - vfMidOddFractionalPrimeSeatWeight R := by
        linarith
      rw [vfMidOddSignedSeatCharge_of_prime R n hp, abs_neg,
        abs_of_nonneg hcomp]
      simp [vfMidActualPrimeSeatMass, hp]
    · rw [vfMidOddSignedSeatCharge_of_not_prime R n hp,
        abs_of_nonneg hw0]
      simpa [vfMidActualPrimeSeatMass, hp] using hw0
  calc
    (1 - vfMidOddFractionalPrimeSeatWeight R) *
        (vfMidIntegerBlockPrimeSupply R : ℝ) =
      (1 - vfMidOddFractionalPrimeSeatWeight R) *
        (∑ n ∈ vfMidOddCandidateSeats R,
          vfMidActualPrimeSeatMass n) := by
        rw [vfMidActualPrimeSeatMass_sum_oddCandidates R
          (by omega : 2 ≤ R)]
    _ = ∑ n ∈ vfMidOddCandidateSeats R,
          (1 - vfMidOddFractionalPrimeSeatWeight R) *
            vfMidActualPrimeSeatMass n := by
        rw [Finset.mul_sum]
    _ ≤ ∑ n ∈ vfMidOddCandidateSeats R,
          |vfMidOddSignedSeatCharge R n| := by
        apply Finset.sum_le_sum
        intro n _hn
        exact hpoint n

/-- The unconditional quantitative NEGATIVE VERDICT for owner-2
full-integer compensation: per-site paired negative heat has a global
absolute-NNS restoration cost at least P_R times as large.
At R=317 the measured factor is ~145.84; at R=1027 ~406.46.
This is NOT a proof of the terminal first-bad hbalance. -/
theorem vfMid915ParityRefinedGlobalPrice_ge_primeCount_mul_localHeat
    (R : ℕ) (hR : 3 ≤ R) :
    (vfMidIntegerBlockPrimeSupply R : ℝ) *
        vfMid915ParityRefinedLocalPairHeat R ≤
      vfMid915ParityRefinedCurrentNNSMass R -
        vfMidFirstBadZeroTargetTotalMass R := by
  have hw0 :=
    vfMidOddFractionalPrimeSeatWeight_nonneg R (by omega : 2 ≤ R)
  have hp0 : 0 ≤ (vfMidIntegerBlockPrimeSupply R : ℝ) := by positivity
  have habs := vfMid915OriginalOddAbs_ge_actualPrimePart R hR
  have hM :
      (1 - vfMidOddFractionalPrimeSeatWeight R) *
          (vfMidIntegerBlockPrimeSupply R : ℝ) ≤
        |vfMidActualPrimeEndpointDefect R| +
          ∑ n ∈ vfMidOddCandidateSeats R,
            |vfMidOddSignedSeatCharge R n| := by
    have habs0 : 0 ≤ |vfMidActualPrimeEndpointDefect R| :=
      abs_nonneg _
    linarith
  have hscalar := vfMid915ParitySplit_globalPrice_ge_count_mul_localHeat
    (|vfMidActualPrimeEndpointDefect R| +
       ∑ n ∈ vfMidOddCandidateSeats R,
         |vfMidOddSignedSeatCharge R n|)
    (vfMidOddFractionalPrimeSeatWeight R)
    (vfMidIntegerBlockPrimeSupply R : ℝ) hw0 hp0 hM
  rw [vfMid915ParityRefinedLocalPairHeat_eq_coefficient_mul_primeSupply R hR,
    vfMid915ParityRefinedCurrentNNSMass_eq_original_add_exactPrice R hR]
  linarith [hscalar]

end RHLean.Analysis
