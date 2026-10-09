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

end RHLean.Analysis
