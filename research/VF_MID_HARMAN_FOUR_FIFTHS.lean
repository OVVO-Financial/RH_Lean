import Mathlib
import «research.VF_MID_GLOBAL_PHASE_UNIFORMITY_BRIDGE»

/-!
# Quantitative square-root prime-phase discrepancy at the VF-mid square scale

Balog's 1983 work on fractional parts of prime powers, and Harman's 1983
sieve treatment of sqrt(p) modulo one, give a classical star-discrepancy
estimate at exponent 4/5 + epsilon for the sequence {sqrt p}, p <= X.

The analytic proof of that published theorem is not presently formalized in
Mathlib.  Accordingly this file does NOT add it as an axiom.  Instead it gives
the precise proposition interface and proves all consequences for the direct
VF-mid square-block midpoint-bias coordinate.

If the global half-phase discrepancy satisfies

  |G(X)| <= C X^(4/5 + epsilon),

then at the square endpoint X = R^2,

  |G_R| <= C R^(8/5 + 2 epsilon),

and the exact telescope from VF_MID_GLOBAL_PHASE_UNIFORMITY_BRIDGE gives

  |sum_{k<n} U_(R+k)|
    <= C R^(8/5+2 epsilon) + C (R+n)^(8/5+2 epsilon).

Thus the classical theorem gives a genuine quantitative no-global-bunching
statement on the actual VF-mid midpoint-bias sequence, while also recording
its exact inherited scale.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Quantitative star-discrepancy interface corresponding to the classical
Balog/Harman 4/5+epsilon estimate for {sqrt p} over primes.

The count is anchored at phase zero because this is the star-discrepancy form
needed by the VF-mid half-phase window. -/
def SquareRootPrimePhaseFourFifthsDiscrepancyStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          |(squareRootPrimePhaseWindowCount X 0 t : ℝ) -
              t * (primeCountUpTo X : ℝ)| ≤
            C * Real.rpow (X : ℝ) ((4 : ℝ) / 5 + ε)

/-- General square-endpoint exponent transport:
((R^2)^alpha) = R^(2 alpha). -/
theorem vfMid_rpow_square (R : ℕ) (α : ℝ) :
    Real.rpow (((R ^ 2 : ℕ) : ℝ)) α =
      Real.rpow (R : ℝ) (2 * α) := by
  have hR : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have hcast : (((R ^ 2 : ℕ) : ℝ)) = (R : ℝ) ^ (2 : ℕ) := by
    push_cast
    ring
  have hexp : ((2 : ℕ) : ℝ) * α = 2 * α := by norm_num
  rw [hcast, ← Real.rpow_natCast (R : ℝ) 2, ← Real.rpow_mul hR, hexp]

/-- Exact exponent conversion for the classical 4/5+epsilon scale at a square
endpoint. -/
theorem vfMid_rpow_square_fourFifths (R : ℕ) (ε : ℝ) :
    Real.rpow (((R ^ 2 : ℕ) : ℝ)) ((4 : ℝ) / 5 + ε) =
      Real.rpow (R : ℝ) ((8 : ℝ) / 5 + 2 * ε) := by
  rw [vfMid_rpow_square]
  congr 1
  ring

/-- The quantitative global discrepancy theorem specialized to the exact
VF-mid half-phase primitive G_R at square endpoints. -/
theorem vfMidGlobalHalfPhaseDiscrepancy_fourFifths
    (h45 : SquareRootPrimePhaseFourFifthsDiscrepancyStatement)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ R0 : ℕ, ∀ R : ℕ, R0 ≤ R →
        |vfMidGlobalHalfPhaseDiscrepancy R| ≤
          C * Real.rpow (R : ℝ) ((8 : ℝ) / 5 + 2 * ε) := by
  rcases h45 ε hε with ⟨C, hC, X0, hX0⟩
  refine ⟨C, hC, max X0 2, ?_⟩
  intro R hR
  have hRX0 : X0 ≤ R := (le_max_left X0 2).trans hR
  have hRR : R ≤ R ^ 2 := by nlinarith
  have hXsq : X0 ≤ R ^ 2 := hRX0.trans hRR
  have hhalf :=
    hX0 (R ^ 2) hXsq (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hG :
      |vfMidGlobalHalfPhaseDiscrepancy R| ≤
        C * Real.rpow (((R ^ 2 : ℕ) : ℝ)) ((4 : ℝ) / 5 + ε) := by
    simpa [vfMidGlobalHalfPhaseDiscrepancy] using hhalf
  rw [vfMid_rpow_square_fourFifths] at hG
  exact hG

/-- Quantitative consequence for the accumulated actual square-block midpoint
bias U_R.  This uses only the exact kernel-checked telescope
sum U = G_endpoint - G_start plus the Balog/Harman discrepancy input. -/
theorem vfMidSquareBlockMidpointBias_sum_fourFifths
    (h45 : SquareRootPrimePhaseFourFifthsDiscrepancyStatement)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ R0 : ℕ, ∀ R n : ℕ, R0 ≤ R →
        |∑ k ∈ Finset.range n,
            vfMidSquareBlockMidpointBias (R + k)| ≤
          C * Real.rpow (R + n : ℝ) ((8 : ℝ) / 5 + 2 * ε) +
            C * Real.rpow (R : ℝ) ((8 : ℝ) / 5 + 2 * ε) := by
  rcases vfMidGlobalHalfPhaseDiscrepancy_fourFifths h45 hε with
    ⟨C, hC, R0, hG⟩
  refine ⟨C, hC, max R0 2, ?_⟩
  intro R n hR
  have hRR0 : R0 ≤ R := (le_max_left R0 2).trans hR
  have hR2 : 2 ≤ R := (le_max_right R0 2).trans hR
  have hRn0 : R0 ≤ R + n := by omega
  have hstart := hG R hRR0
  have hend := hG (R + n) hRn0
  rw [vfMidSquareBlockMidpointBias_sum_eq_globalPhaseDifference R n hR2]
  calc
    |vfMidGlobalHalfPhaseDiscrepancy (R + n) -
        vfMidGlobalHalfPhaseDiscrepancy R|
        ≤ |vfMidGlobalHalfPhaseDiscrepancy (R + n)| +
            |vfMidGlobalHalfPhaseDiscrepancy R| := abs_sub _ _
    _ ≤ C * Real.rpow (R + n : ℝ) ((8 : ℝ) / 5 + 2 * ε) +
          C * Real.rpow (R : ℝ) ((8 : ℝ) / 5 + 2 * ε) :=
      add_le_add hend hstart

/-- The inherited square-endpoint exponent is strictly above the linear scale.
This records the exact strength of the classical global-discrepancy input; it
does not claim that a sharper theorem is impossible. -/
theorem vfMid_fourFifths_square_exponent_gt_one
    {ε : ℝ} (hε : 0 < ε) :
    (1 : ℝ) < (8 : ℝ) / 5 + 2 * ε := by
  linarith

end RHLean.Analysis
