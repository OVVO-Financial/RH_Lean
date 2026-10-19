import RHLean.Analysis.DeterministicTGreenKuboComparison

/-!
# Exact signed square-shell covariance at the 7/8 scale

For S_R = sum_{R^2 <= n < (R+1)^2} mu(n), this module proves:

* the shell has exactly 2R+1 physical integer positions;
* its ACTUAL squarefree diagonal K_R is at most 2R+1;
* its complete internal signed-pair covariance C_R obeys the exact
  Green--Kubo identity S_R^2 = K_R + 2*C_R;
* a bound on positive signed covariance reduces the shell energy bound
  to an ordinary O(R) diagonal budget.

The internal pair covariance is obtained by subtracting the two original
Mertens pair prefixes and removing precisely the cross-boundary
parent/shell pairs. It is not a random-pair approximation or a model.

NO uniform all-R signed covariance, 7/8 shell bound, ideal lift or
zero-free theorem is claimed here. These are arithmetic acceptance targets.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- Mertens sign sum over every integer in [R^2, (R+1)^2). -/
def vf919SquareShellSum (R : ℕ) : ℝ :=
  realMertensLength ((R + 1) ^ 2) - realMertensLength (R ^ 2)

/-- Exact squarefree diagonal of the physical square shell. -/
def vf919SquareShellDiagonal (R : ℕ) : ℝ :=
  realMertensDiagonal ((R + 1) ^ 2) - realMertensDiagonal (R ^ 2)

/-- Genuine within-shell signed pair sum: all pairs in the upper
Mertens prefix, minus lower-prefix pairs and lower/shell cross pairs. -/
def vf919SquareShellCovariance (R : ℕ) : ℝ :=
  realMertensPositiveLagPairSum ((R + 1) ^ 2) -
    realMertensPositiveLagPairSum (R ^ 2) -
      realMertensLength (R ^ 2) * vf919SquareShellSum R

/-- Exact square telescoping, not a statistical assumption:
the sum of all shells below R equals the COMPLETE physical Mobius
prefix immediately preceding R^2. -/
theorem vf919SquareShell_telescope (R : ℕ) :
    (∑ r ∈ Finset.range R, vf919SquareShellSum r) =
      realMertensLength (R ^ 2) := by
  induction R with
  | zero =>
      simp [realMertensLength]
  | succ R ih =>
      rw [Finset.sum_range_succ, ih]
      unfold vf919SquareShellSum
      ring

/-- An independent signed bound on individual shells would transfer
to the whole square-prefix sum without a complex-analytic detector.
The right side still contains the ACTUAL signed-shell amplitudes. -/
theorem vf919SquareShell_prefixNorm_le_shellNorms (R : ℕ) :
    ‖realMertensLength (R ^ 2)‖ ≤
      ∑ r ∈ Finset.range R, ‖vf919SquareShellSum r‖ := by
  rw [← vf919SquareShell_telescope R]
  exact norm_sum_le _ _

/-- There are exactly 2R+1 integer sites in a completed square shell. -/
theorem vf919SquareShell_width (R : ℕ) :
    (R + 1) ^ 2 - R ^ 2 = 2 * R + 1 := by
  have h : (R + 1) ^ 2 = R ^ 2 + (2 * R + 1) := by ring
  omega

/-- Each physical Mobius site contributes at most one unit of diagonal
mass. This elementary inequality does NOT assume a squarefree density. -/
theorem vf919Diagonal_interval_le (a b : ℕ) (hab : a ≤ b) :
    realMertensDiagonal b ≤
      realMertensDiagonal a + ((b - a : ℕ) : ℝ) := by
  induction b, hab using Nat.le_induction with
  | base =>
      simp
  | succ b hb ih =>
      have hstep := realMoebiusStep_sq_le_one b
      have hdiff : b + 1 - a = (b - a) + 1 := by omega
      rw [realMertensDiagonal_succ, hdiff]
      push_cast
      linarith

/-- UNCONDITIONAL square-shell diagonal K_R ≤ 2R+1. -/
theorem vf919SquareShell_diagonal_le_width (R : ℕ) :
    vf919SquareShellDiagonal R ≤ (2 : ℝ) * R + 1 := by
  have hle : R ^ 2 ≤ (R + 1) ^ 2 := by
    have hsq : (R + 1) ^ 2 = R ^ 2 + (2 * R + 1) := by ring
    omega
  have hbound := vf919Diagonal_interval_le (R ^ 2) ((R + 1) ^ 2) hle
  rw [vf919SquareShell_width] at hbound
  unfold vf919SquareShellDiagonal
  push_cast at hbound
  linarith

/-- Exact physical square-shell energy = diagonal + signed within-shell
off-diagonal pairs. It is true at EVERY R without spectral hypotheses. -/
theorem vf919SquareShell_signedGreenKubo (R : ℕ) :
    vf919SquareShellSum R ^ 2 =
      vf919SquareShellDiagonal R + 2 * vf919SquareShellCovariance R := by
  have hhigh :=
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum
      ((R + 1) ^ 2)
  have hlow :=
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum
      (R ^ 2)
  -- Unfold covariance FIRST: it contains a nested square-shell sum.
  -- Otherwise the mixed product is opaque to nonlinear arithmetic.
  unfold vf919SquareShellCovariance vf919SquareShellSum
    vf919SquareShellDiagonal
  nlinarith [hhigh, hlow]

/-- ALL signed covariance lies in a single scalar inequality.
This is an exact iff, not an upper bound proved unconditionally. -/
theorem vf919SquareShell_covarianceCeiling_iff (R : ℕ) (T : ℝ) :
    2 * vf919SquareShellCovariance R ≤
        T - vf919SquareShellDiagonal R ↔
      vf919SquareShellSum R ^ 2 ≤ T := by
  have h := vf919SquareShell_signedGreenKubo R
  constructor <;> intro hbound <;> linarith

/-- The entire diagonal is already paid at O(R); only POSITIVE
signed covariance excursions require additional arithmetic control. -/
theorem vf919SquareShell_energy_of_signedCovariance (R : ℕ) (T : ℝ)
    (hC : 2 * vf919SquareShellCovariance R ≤ T) :
    vf919SquareShellSum R ^ 2 ≤ (2 : ℝ) * R + 1 + T := by
  have h := vf919SquareShell_signedGreenKubo R
  have hK := vf919SquareShell_diagonal_le_width R
  linarith

#print axioms vf919SquareShell_telescope
#print axioms vf919SquareShell_prefixNorm_le_shellNorms
#print axioms vf919SquareShell_width
#print axioms vf919Diagonal_interval_le
#print axioms vf919SquareShell_diagonal_le_width
#print axioms vf919SquareShell_signedGreenKubo
#print axioms vf919SquareShell_covarianceCeiling_iff
#print axioms vf919SquareShell_energy_of_signedCovariance

end RHLean.Analysis
