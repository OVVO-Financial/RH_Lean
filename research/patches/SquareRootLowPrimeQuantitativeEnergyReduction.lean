import Mathlib
import RHLean.Proof.SquareRootLowPrimeSignedResponseChildren
import RHLean.Proof.SquareRootLowPrimeCanonicalFrontierBridge

/-!
# Real quantitative reductions for the low-prime sequential state

All response coefficients are real although the repository stores the finite
sums in `ℂ`. This module moves the exact chronological step, the signed-child
identity, and the terminal canonical bridges into ordered real coordinates.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

def squareRootLowPrimeRunningImbalanceReal
    (R K j p : ℕ) : ℝ :=
  (squareRootLowPrimeRunningImbalance R K j p).re

def squareRootLowPrimeFreshIncrementReal
    (R K j p : ℕ) : ℝ :=
  (squareRootLowPrimeFreshIncrement R K j p).re

def squareRootLowPrimeCanonicalTerminalCoreReal
    (R K j : ℕ) : ℝ :=
  (squareRootLowPrimeCanonicalTerminalCore R K j).re

def squareRootLowPrimeFarSurvivorTerminalCoreReal
    (R : ℕ) : ℝ :=
  (squareRootLowPrimeFarSurvivorTerminalCore R).re

theorem squareRootLowPrimeRunningImbalanceReal_step_eq_freshIncrementReal
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootLowPrimeRunningImbalanceReal R K j (p - 1) -
        squareRootLowPrimeRunningImbalanceReal R K j p =
      squareRootLowPrimeFreshIncrementReal R K j p := by
  have h := congrArg Complex.re
    (squareRootLowPrimeRunningImbalance_step_eq_freshIncrement
      R K j p hp)
  simpa [squareRootLowPrimeRunningImbalanceReal,
    squareRootLowPrimeFreshIncrementReal] using h

theorem squareRootLowPrimeRunningEnergyReal_step
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootLowPrimeRunningImbalanceReal R K j (p - 1) ^ 2 -
        squareRootLowPrimeRunningImbalanceReal R K j p ^ 2 =
      2 * squareRootLowPrimeRunningImbalanceReal R K j (p - 1) *
          squareRootLowPrimeFreshIncrementReal R K j p -
        squareRootLowPrimeFreshIncrementReal R K j p ^ 2 := by
  have hstep :=
    squareRootLowPrimeRunningImbalanceReal_step_eq_freshIncrementReal
      R K j p hp
  calc
    squareRootLowPrimeRunningImbalanceReal R K j (p - 1) ^ 2 -
        squareRootLowPrimeRunningImbalanceReal R K j p ^ 2 =
      2 * squareRootLowPrimeRunningImbalanceReal R K j (p - 1) *
          (squareRootLowPrimeRunningImbalanceReal R K j (p - 1) -
            squareRootLowPrimeRunningImbalanceReal R K j p) -
        (squareRootLowPrimeRunningImbalanceReal R K j (p - 1) -
          squareRootLowPrimeRunningImbalanceReal R K j p) ^ 2 := by ring
    _ = 2 * squareRootLowPrimeRunningImbalanceReal R K j (p - 1) *
          squareRootLowPrimeFreshIncrementReal R K j p -
        squareRootLowPrimeFreshIncrementReal R K j p ^ 2 := by rw [hstep]

theorem squareRootLowPrimeFreshIncrementReal_sum_eq_neg_ownedResponseChildrenMass
    {R K j U : ℕ} (hR : 2 ≤ R) (hUR : U < R) :
    (∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      squareRootLowPrimeFreshIncrementReal R K j p) =
      -∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
        (canonicalMoebiusWeight n).re := by
  have h := congrArg Complex.re
    (squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseChildrenMass
      (R := R) (K := K) (j := j) (U := U) hR hUR)
  simpa [squareRootLowPrimeFreshIncrementReal] using h

private theorem abs_re_sub_le_norm_sub (z w : ℂ) :
    |z.re - w.re| ≤ ‖z - w‖ := by
  have h := Complex.abs_re_le_norm (z - w)
  simpa using h

theorem squareRootLowPrimeRunningImbalanceReal_sub_canonicalCore_abs_le_root
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
      squareRootLowPrimeCanonicalTerminalCoreReal R K j| ≤ (R : ℝ) := by
  exact (abs_re_sub_le_norm_sub
    (squareRootLowPrimeRunningImbalance R K j
      (squareRootBornPostTailLowPrimeCutoff R))
    (squareRootLowPrimeCanonicalTerminalCore R K j)).trans
      (squareRootLowPrimeRunningImbalance_sub_canonicalCore_norm_le_root
        R K j hR hK hKR hj)

theorem squareRootLowPrimeRunningImbalanceReal_abs_le_canonicalCore_add_root
    (R K j : ℕ) (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
      |squareRootLowPrimeCanonicalTerminalCoreReal R K j| + (R : ℝ) := by
  have hdiff :=
    squareRootLowPrimeRunningImbalanceReal_sub_canonicalCore_abs_le_root
      R K j hR hK hKR hj
  rw [show squareRootLowPrimeRunningImbalanceReal R K j
      (squareRootBornPostTailLowPrimeCutoff R) =
      (squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootLowPrimeCanonicalTerminalCoreReal R K j) +
        squareRootLowPrimeCanonicalTerminalCoreReal R K j by ring]
  calc
    |(squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootLowPrimeCanonicalTerminalCoreReal R K j) +
        squareRootLowPrimeCanonicalTerminalCoreReal R K j| ≤
      |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootLowPrimeCanonicalTerminalCoreReal R K j| +
        |squareRootLowPrimeCanonicalTerminalCoreReal R K j| := abs_add _ _
    _ ≤ (R : ℝ) + |squareRootLowPrimeCanonicalTerminalCoreReal R K j| :=
      add_le_add_right hdiff _
    _ = |squareRootLowPrimeCanonicalTerminalCoreReal R K j| + (R : ℝ) := by ring

theorem squareRootLowPrimeRunningImbalanceReal_abs_le_of_canonicalCore
    (R K j : ℕ) (B : ℝ)
    (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hcore : |squareRootLowPrimeCanonicalTerminalCoreReal R K j| ≤ B) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤ B + (R : ℝ) := by
  exact
    (squareRootLowPrimeRunningImbalanceReal_abs_le_canonicalCore_add_root
      R K j hR hK hKR hj).trans (add_le_add_right hcore _)

theorem squareRootLowPrimeRunningImbalanceReal_sq_le_of_canonicalCore
    (R K j : ℕ) (B : ℝ)
    (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hB : 0 ≤ B)
    (hcore : |squareRootLowPrimeCanonicalTerminalCoreReal R K j| ≤ B) :
    squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) ^ 2 ≤
      (B + (R : ℝ)) ^ 2 := by
  have habs := squareRootLowPrimeRunningImbalanceReal_abs_le_of_canonicalCore
    R K j B hR hK hKR hj hcore
  have hnonneg : 0 ≤ B + (R : ℝ) := by positivity
  rcases (abs_le.mp habs) with ⟨hlow, hupp⟩
  nlinarith

theorem squareRootLowPrimeEndpointEnergyReal_ge_of_canonicalCore
    (R K j : ℕ) (B : ℝ)
    (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hB : 0 ≤ B)
    (hcore : |squareRootLowPrimeCanonicalTerminalCoreReal R K j| ≤ B) :
    squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        squareRootLowPrimeRunningImbalanceReal R K j
          (squareRootBornPostTailLowPrimeCutoff R) ^ 2 ≥
      squareRootLowPrimeRunningImbalanceReal R K j K ^ 2 -
        (B + (R : ℝ)) ^ 2 := by
  have hterminal :=
    squareRootLowPrimeRunningImbalanceReal_sq_le_of_canonicalCore
      R K j B hR hK hKR hj hB hcore
  linarith

theorem squareRootLowPrimeRunningImbalanceReal_sub_farSurvivorCore_abs_le
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
      squareRootLowPrimeFarSurvivorTerminalCoreReal R| ≤
        8 * (R : ℝ) + (K : ℝ) := by
  exact (abs_re_sub_le_norm_sub
    (squareRootLowPrimeRunningImbalance R K j
      (squareRootBornPostTailLowPrimeCutoff R))
    (squareRootLowPrimeFarSurvivorTerminalCore R)).trans
      (squareRootLowPrimeRunningImbalance_sub_farSurvivorCore_norm_le
        R K j hR hK hKR hj hV0 hVK)

theorem squareRootLowPrimeRunningImbalanceReal_abs_le_farSurvivorCore_add_boundary
    (R K j : ℕ) (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ)) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
      |squareRootLowPrimeFarSurvivorTerminalCoreReal R| +
        (8 * (R : ℝ) + (K : ℝ)) := by
  have hdiff := squareRootLowPrimeRunningImbalanceReal_sub_farSurvivorCore_abs_le
    R K j hR hK hKR hj hV0 hVK
  rw [show squareRootLowPrimeRunningImbalanceReal R K j
      (squareRootBornPostTailLowPrimeCutoff R) =
      (squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootLowPrimeFarSurvivorTerminalCoreReal R) +
        squareRootLowPrimeFarSurvivorTerminalCoreReal R by ring]
  calc
    |(squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootLowPrimeFarSurvivorTerminalCoreReal R) +
        squareRootLowPrimeFarSurvivorTerminalCoreReal R| ≤
      |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R) -
        squareRootLowPrimeFarSurvivorTerminalCoreReal R| +
        |squareRootLowPrimeFarSurvivorTerminalCoreReal R| := abs_add _ _
    _ ≤ (8 * (R : ℝ) + (K : ℝ)) +
        |squareRootLowPrimeFarSurvivorTerminalCoreReal R| :=
      add_le_add_right hdiff _
    _ = |squareRootLowPrimeFarSurvivorTerminalCoreReal R| +
        (8 * (R : ℝ) + (K : ℝ)) := by ring

end RHLean.Proof
