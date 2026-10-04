import Mathlib
import «research.VF_MID_OPTIMAL_BASE_FIRST_CROSSING_TRIGGER»
import «research.VF_MID_SIGNED_SEAT_CHARGE»
import «research.VF_MID_FRACTIONAL_PRIME_CLUSTER»

/-!
# VF-native Lyapunov seat Gram

This file performs the exact reassembly between the macroscopic VF endpoint
energy and the literal integer-lattice VF-minus-actual seat charges.

For block R let

  q_R(n) = w_R - 1_Prime(n)

on the parity-surviving odd candidate seats.  The already-compiled signed-seat
identity gives

  sum_n q_R(n) = V_R - P_R = -e_R,

where

  D_R = pi(R^2) - VF_mid(R^2),
  e_R = D_(R+1) - D_R = P_R - V_R.

For a historical run [A,R), define its signed seat mass and the rectangular
historical-current Gram.  Exact finite Fubini then gives

  HistoryCurrentGram(A,R)
    = (D_R - D_A) * e_R.

Likewise the current self-Gram is exactly e_R^2.  Therefore

  D_(R+1)^2 - D_R^2
    = SelfGram(R)
      + 2 * HistoryCurrentGram(A,R)
      + 2 * D_A * e_R.

This is the exact macroscopic-to-lattice Lyapunov weld.  No Li approximation,
Mertens substitution, norm estimate, or probabilistic assumption appears.

The final theorem feeds the already-compiled optimal-base first-crossing bill
directly into this VF-native signed Gram decomposition.

What is intentionally not done here is to identify the full uncentered VF Gram
with the centered Mobius/zero-target Gram.  On a frozen cubic-depth carrier the
centered pair identity is exact, but affine target cross-terms must remain
explicit until a signed owner reassembly accounts for them.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Signed VF-minus-actual mass of one square block on the literal odd-seat
carrier. -/
def vfMidOddBlockSeatMass (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidOddCandidateSeats R, vfMidOddSignedSeatCharge R n

/-- Historical signed VF-minus-actual seat mass over the complete square blocks
A <= r < B. -/
def vfMidOddRunSeatMass (A B : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico A B, vfMidOddBlockSeatMass r

/-- Literal rectangular Gram between all historical seats in [A,R) and the
current R-th block seats. -/
def vfMidOddHistoricalCurrentSeatGram (A R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico A R,
    ∑ n ∈ vfMidOddCandidateSeats r,
      ∑ m ∈ vfMidOddCandidateSeats R,
        vfMidOddSignedSeatCharge r n *
          vfMidOddSignedSeatCharge R m

/-- Literal current-block self Gram. -/
def vfMidOddCurrentSeatSelfGram (R : ℕ) : ℝ :=
  ∑ n ∈ vfMidOddCandidateSeats R,
    ∑ m ∈ vfMidOddCandidateSeats R,
      vfMidOddSignedSeatCharge R n *
        vfMidOddSignedSeatCharge R m

/-- One block's literal signed seat mass is exactly the native VF tracking
defect V_R-P_R. -/
theorem vfMidOddBlockSeatMass_eq_trackingDefect
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddBlockSeatMass R =
      vfMidOddCompositeTrackingDefect R := by
  exact vfMidOddSignedSeatCharge_sum R hR

/-- The same block mass is exactly minus the direct prime-minus-VF increment. -/
theorem vfMidOddBlockSeatMass_eq_neg_bandError
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddBlockSeatMass R = -vfMidSquareBandError R := by
  rw [vfMidOddBlockSeatMass_eq_trackingDefect R hR,
    vfMidOddCompositeTrackingDefect_eq_neg_bandError R hR]

/-- Historical seat mass is the sum of the already-named block tracking
defects. -/
theorem vfMidOddRunSeatMass_eq_dyadicTracking
    (A B : ℕ) (hA : 2 ≤ A) :
    vfMidOddRunSeatMass A B =
      vfMidOddDyadicCompositeTrackingDefect A B := by
  unfold vfMidOddRunSeatMass vfMidOddDyadicCompositeTrackingDefect
  apply Finset.sum_congr rfl
  intro r hr
  have hr2 : 2 ≤ r := hA.trans (Finset.mem_Ico.mp hr).1
  exact vfMidOddBlockSeatMass_eq_trackingDefect r hr2

/-- **Exact accumulated-state dictionary.**

The historical VF-minus-actual seat mass over [A,B) is minus the change of the
square-endpoint VF error. -/
theorem vfMidOddRunSeatMass_eq_neg_endpointError_increment
    (A B : ℕ) (hA : 2 ≤ A) (hAB : A ≤ B) :
    vfMidOddRunSeatMass A B =
      -(vfMidSquareEndpointError B - vfMidSquareEndpointError A) := by
  unfold vfMidOddRunSeatMass
  calc
    (∑ r ∈ Finset.Ico A B, vfMidOddBlockSeatMass r) =
        ∑ r ∈ Finset.Ico A B, -vfMidSquareBandError r := by
          apply Finset.sum_congr rfl
          intro r hr
          have hr2 : 2 ≤ r := hA.trans (Finset.mem_Ico.mp hr).1
          exact vfMidOddBlockSeatMass_eq_neg_bandError r hr2
    _ = -(∑ r ∈ Finset.Ico A B, vfMidSquareBandError r) := by
          rw [Finset.sum_neg_distrib]
    _ = -(vfMidSquareEndpointError B - vfMidSquareEndpointError A) := by
          congr 1
          calc
            (∑ r ∈ Finset.Ico A B, vfMidSquareBandError r) =
                vfMidFractionalPrimeClusterDiscrepancy A B := by
                  symm
                  exact
                    vfMidFractionalPrimeClusterDiscrepancy_eq_sum_bandError
                      A B hA
            _ = vfMidSquareEndpointError B -
                vfMidSquareEndpointError A :=
                  vfMidFractionalPrimeClusterDiscrepancy_eq_endpointError_sub
                    A B hA hAB

/-- Finite Fubini: the historical-current rectangle factors into historical
mass times current mass before any estimate is taken. -/
theorem vfMidOddHistoricalCurrentSeatGram_eq_run_mul_block
    (A R : ℕ) :
    vfMidOddHistoricalCurrentSeatGram A R =
      vfMidOddRunSeatMass A R * vfMidOddBlockSeatMass R := by
  unfold vfMidOddHistoricalCurrentSeatGram
    vfMidOddRunSeatMass vfMidOddBlockSeatMass
  calc
    (∑ r ∈ Finset.Ico A R,
      ∑ n ∈ vfMidOddCandidateSeats r,
        ∑ m ∈ vfMidOddCandidateSeats R,
          vfMidOddSignedSeatCharge r n *
            vfMidOddSignedSeatCharge R m) =
      ∑ r ∈ Finset.Ico A R,
        ∑ n ∈ vfMidOddCandidateSeats r,
          vfMidOddSignedSeatCharge r n *
            (∑ m ∈ vfMidOddCandidateSeats R,
              vfMidOddSignedSeatCharge R m) := by
                apply Finset.sum_congr rfl
                intro r _hr
                apply Finset.sum_congr rfl
                intro n _hn
                rw [Finset.mul_sum]
    _ =
      ∑ r ∈ Finset.Ico A R,
        (∑ n ∈ vfMidOddCandidateSeats r,
          vfMidOddSignedSeatCharge r n) *
            (∑ m ∈ vfMidOddCandidateSeats R,
              vfMidOddSignedSeatCharge R m) := by
                apply Finset.sum_congr rfl
                intro r _hr
                rw [Finset.sum_mul]
    _ =
      (∑ r ∈ Finset.Ico A R,
        ∑ n ∈ vfMidOddCandidateSeats r,
          vfMidOddSignedSeatCharge r n) *
            (∑ m ∈ vfMidOddCandidateSeats R,
              vfMidOddSignedSeatCharge R m) := by
                rw [Finset.sum_mul]

/-- **Exact historical-current polarization.**

The physical rectangular VF-seat Gram is exactly (D_R-D_A)e_R. -/
theorem vfMidOddHistoricalCurrentSeatGram_eq_endpointPolarization
    {A R : ℕ} (hA : 2 ≤ A) (hAR : A ≤ R) :
    vfMidOddHistoricalCurrentSeatGram A R =
      (vfMidSquareEndpointError R - vfMidSquareEndpointError A) *
        vfMidSquareBandError R := by
  rw [vfMidOddHistoricalCurrentSeatGram_eq_run_mul_block,
    vfMidOddRunSeatMass_eq_neg_endpointError_increment A R hA hAR,
    vfMidOddBlockSeatMass_eq_neg_bandError R (hA.trans hAR)]
  ring

/-- Current self Gram factors as the square of current signed seat mass. -/
theorem vfMidOddCurrentSeatSelfGram_eq_blockMass_sq
    (R : ℕ) :
    vfMidOddCurrentSeatSelfGram R =
      (vfMidOddBlockSeatMass R) ^ 2 := by
  unfold vfMidOddCurrentSeatSelfGram vfMidOddBlockSeatMass
  calc
    (∑ n ∈ vfMidOddCandidateSeats R,
      ∑ m ∈ vfMidOddCandidateSeats R,
        vfMidOddSignedSeatCharge R n *
          vfMidOddSignedSeatCharge R m) =
      ∑ n ∈ vfMidOddCandidateSeats R,
        vfMidOddSignedSeatCharge R n *
          (∑ m ∈ vfMidOddCandidateSeats R,
            vfMidOddSignedSeatCharge R m) := by
              apply Finset.sum_congr rfl
              intro n _hn
              rw [Finset.mul_sum]
    _ =
      (∑ n ∈ vfMidOddCandidateSeats R,
        vfMidOddSignedSeatCharge R n) *
        (∑ m ∈ vfMidOddCandidateSeats R,
          vfMidOddSignedSeatCharge R m) := by
            rw [Finset.sum_mul]
    _ = (∑ n ∈ vfMidOddCandidateSeats R,
        vfMidOddSignedSeatCharge R n) ^ 2 := by ring

/-- **Exact current self energy.** -/
theorem vfMidOddCurrentSeatSelfGram_eq_bandError_sq
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddCurrentSeatSelfGram R =
      vfMidSquareBandError R ^ 2 := by
  rw [vfMidOddCurrentSeatSelfGram_eq_blockMass_sq,
    vfMidOddBlockSeatMass_eq_neg_bandError R hR]
  ring

/-- The exact VF-native Lyapunov bill written on physical signed seat Grams. -/
def vfMidOddLyapunovSeatGramBill (A R : ℕ) : ℝ :=
  vfMidOddCurrentSeatSelfGram R +
    2 * vfMidOddHistoricalCurrentSeatGram A R +
    2 * vfMidSquareEndpointError A * vfMidSquareBandError R

/-- **Macroscopic-to-lattice Lyapunov weld.**

For every anchor A <= R, the exact endpoint energy increment is the current
seat self-Gram plus twice the historical-current seat Gram plus the explicit
anchor polarization.  All three terms remain signed. -/
theorem vfMidSquareEndpointError_energy_step_eq_oddLyapunovSeatGramBill
    {A R : ℕ} (hA : 2 ≤ A) (hAR : A ≤ R) :
    vfMidSquareEndpointError (R + 1) ^ 2 -
        vfMidSquareEndpointError R ^ 2 =
      vfMidOddLyapunovSeatGramBill A R := by
  have hR : 2 ≤ R := hA.trans hAR
  rw [vfMidSquareEndpointError_succ R hR]
  unfold vfMidOddLyapunovSeatGramBill
  rw [vfMidOddCurrentSeatSelfGram_eq_bandError_sq R hR,
    vfMidOddHistoricalCurrentSeatGram_eq_endpointPolarization hA hAR]
  ring

/-- **Optimal-base first escape issues the same literal VF-seat Gram bill.**

This is the direct bridge from the already-solved moving optimal-base boundary
to the integer lattice. -/
theorem vfMidOptimalBase_upperFirstEscape_forces_oddLyapunovSeatGramBill
    {K : ℝ} (hK : 0 ≤ K)
    {A R : ℕ} (hA : 2 ≤ A) (hAR : A ≤ R)
    (hinside :
      vfMidSolvedFantasyRadialLowerOptimalBase K R ≤
          optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ∧
        optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ≤
          vfMidSolvedFantasyRadialUpperOptimalBase K R)
    (habove :
      vfMidSolvedFantasyRadialUpperOptimalBase K (R + 1) <
        optimalLogBase vfMidPrimeCount (((R + 1 : ℕ) : ℝ) ^ 2)) :
    vfMidRadialWallWidth K (R + 1) ^ 2 -
        vfMidRadialWallWidth K R ^ 2 <
      vfMidOddLyapunovSeatGramBill A R := by
  have hR : 2 ≤ R := hA.trans hAR
  have hfirst :=
    vfMidOptimalBase_upperFirstEscape_forces_energy
      hK R hR hinside habove
  have henergy :=
    vfMidSquareEndpointError_sq_succ_eq_correlation R hR
  have hseat :=
    vfMidSquareEndpointError_energy_step_eq_oddLyapunovSeatGramBill
      hA hAR
  rw [← henergy, hseat] at hfirst
  exact hfirst

end RHLean.Analysis
