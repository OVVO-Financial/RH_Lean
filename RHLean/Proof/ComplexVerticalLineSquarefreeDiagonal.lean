import Mathlib
import RHLean.Analysis.MathlibMertensHook
import RHLean.Proof.ComplexVerticalLineGreenKubo

/-!
# Exact squarefree diagonal for vertical-line birth/death energy

The Green--Kubo inequality for the physical child-line process was first proved
with the pointwise envelope `event^2 <= 1`.  That loses the exact forty-percent
zero population before the signed covariance is even reached.

This file keeps the same birth/death carrier and proves the sharper pointwise
statement

`event(n)^2 <= mu(n)^2`.

Consequently the complete line-event diagonal is bounded by the existing
Mertens diagonal, i.e. the exact finite squarefree population.  Using the
repository's zero-count identity, this is

`K - 1 - Z(K - 1)`

for `K = (b+1)^2`, where `Z(x)` is the exact number of sites `1 <= n <= x`
with `mu(n)=0`.

Thus the limiting `40/30/30` law is used only in the safe direction: the zero
population can sharpen the diagonal.  No `30/30` sign balance is asserted on
the arithmetically selected birth/death set, and no independence assumption is
introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- **Exact squarefree pointwise envelope.**  A physical child line either does
not change endpoint status, in which case its event is zero, or it is born/dies,
in which case its event is `+/- mu(n)`.  Hence its squared event is bounded by
`mu(n)^2`, not merely by one. -/
theorem signedVerticalLineEventStep_sq_le_moebius_sq
    (a b n : ℕ) :
    signedVerticalLineEventStep a b n ^ 2 ≤ realMoebiusStep n ^ 2 := by
  by_cases hb : n ∈ orderedEulerCutActiveChildren (b + 1)
  · by_cases ha : n ∈ orderedEulerCutActiveChildren a
    · have hsq : 0 ≤ realMoebiusStep n ^ 2 := sq_nonneg _
      simpa [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal, hb, ha] using hsq
    · have hrefl : realMoebiusStep n ^ 2 ≤ realMoebiusStep n ^ 2 := le_rfl
      simpa [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal,
        orderedEulerCutChildChargeReal, realMoebiusStep, hb, ha] using hrefl
  · by_cases ha : n ∈ orderedEulerCutActiveChildren a
    · have hrefl : realMoebiusStep n ^ 2 ≤ realMoebiusStep n ^ 2 := le_rfl
      simpa [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal,
        orderedEulerCutChildChargeReal, realMoebiusStep, hb, ha] using hrefl
    · have hsq : 0 ≤ realMoebiusStep n ^ 2 := sq_nonneg _
      simpa [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal, hb, ha] using hsq

/-- **Exact finite squarefree diagonal bound.**  The line-event diagonal is
bounded by the ordinary deterministic Mertens diagonal on the same physical
prefix.  The right side is exactly the number of nonzero Mobius sites there. -/
theorem signedVerticalLineRunDiagonal_le_mertensDiagonal
    (a b : ℕ) :
    signedVerticalLineRunDiagonal a b ≤
      realMertensDiagonal ((b + 1) ^ 2) := by
  unfold signedVerticalLineRunDiagonal signedBlockEnergy realMertensDiagonal
  exact Finset.sum_le_sum
    (fun n _hn => signedVerticalLineEventStep_sq_le_moebius_sq a b n)

/-- At the square endpoint, the existing Mertens diagonal is exactly the full
prefix population minus the `mu=0` population.  The `n=0` site contributes zero,
so the physical endpoint is `K-1` rather than `K`. -/
theorem realMertensDiagonal_squareEndpoint_eq_sub_zeroCount
    (b : ℕ) :
    realMertensDiagonal ((b + 1) ^ 2) =
      ((((b + 1) ^ 2 - 1 : ℕ) : ℝ)) -
        (realMertensZeroCount ((b + 1) ^ 2 - 1) : ℝ) := by
  have hKpos : 0 < (b + 1) ^ 2 := by positivity
  have hKone : 1 ≤ (b + 1) ^ 2 := Nat.succ_le_iff.mpr hKpos
  have hKsub : ((b + 1) ^ 2 - 1) + 1 = (b + 1) ^ 2 :=
    Nat.sub_add_cancel hKone
  have hzero :=
    realMertensDiagonal_add_zeroCount_eq_endpoint ((b + 1) ^ 2 - 1)
  rw [hKsub] at hzero
  linarith

/-- The diagonal bound with the exact finite Mobius-zero population exposed. -/
theorem signedVerticalLineRunDiagonal_le_endpoint_sub_zeroCount
    (a b : ℕ) :
    signedVerticalLineRunDiagonal a b ≤
      ((((b + 1) ^ 2 - 1 : ℕ) : ℝ)) -
        (realMertensZeroCount ((b + 1) ^ 2 - 1) : ℝ) := by
  have hdiag := signedVerticalLineRunDiagonal_le_mertensDiagonal a b
  rw [realMertensDiagonal_squareEndpoint_eq_sub_zeroCount b] at hdiag
  exact hdiag

/-- **Squarefree Green--Kubo inequality.**  This is the previous line-energy
inequality with the crude unit diagonal replaced by the exact squarefree
Mertens diagonal. -/
theorem norm_signedVerticalIntervalMass_sq_le_mertensDiagonal_add_two_mul_covariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      realMertensDiagonal ((b + 1) ^ 2) +
        2 * signedVerticalLineRunCovariance a b := by
  have hid :=
    norm_signedVerticalIntervalMass_sq_eq_lineDiagonal_add_two_mul_covariance
      a b hab
  have hdiag := signedVerticalLineRunDiagonal_le_mertensDiagonal a b
  linarith

/-- Negative covariance remains harmless after the squarefree sharpening. -/
theorem norm_signedVerticalIntervalMass_sq_le_mertensDiagonal_add_two_mul_positiveCovariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      realMertensDiagonal ((b + 1) ^ 2) +
        2 * max 0 (signedVerticalLineRunCovariance a b) := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_mertensDiagonal_add_two_mul_covariance
      a b hab
  have hcov : signedVerticalLineRunCovariance a b ≤
      max 0 (signedVerticalLineRunCovariance a b) := le_max_right _ _
  linarith

/-- **Exact finite-density inequality.**  The complete signed vertical mass is
bounded by the exact nonzero Mobius population plus the positive cross-line
covariance.  This is the rigorous finite replacement for inserting a heuristic
`60%` diagonal density. -/
theorem norm_signedVerticalIntervalMass_sq_le_endpoint_sub_zeroCount_add_covariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      ((((b + 1) ^ 2 - 1 : ℕ) : ℝ)) -
        (realMertensZeroCount ((b + 1) ^ 2 - 1) : ℝ) +
        2 * max 0 (signedVerticalLineRunCovariance a b) := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_mertensDiagonal_add_two_mul_positiveCovariance
      a b hab
  rw [realMertensDiagonal_squareEndpoint_eq_sub_zeroCount b] at hbase
  exact hbase

/-- Any finite lower bound for the zero density plugs into the line-energy
estimate without making a sign-balance assumption.  In particular a rigorous
version of `Z(x) >= delta*x - E` yields diagonal coefficient `1-delta`. -/
theorem norm_signedVerticalIntervalMass_sq_le_of_zeroCount_lowerBound
    (a b : ℕ) (hab : a ≤ b + 1) (δ E : ℝ)
    (hzero :
      δ * ((((b + 1) ^ 2 - 1 : ℕ) : ℝ)) - E ≤
        (realMertensZeroCount ((b + 1) ^ 2 - 1) : ℝ)) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      (1 - δ) * ((((b + 1) ^ 2 - 1 : ℕ) : ℝ)) + E +
        2 * max 0 (signedVerticalLineRunCovariance a b) := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_endpoint_sub_zeroCount_add_covariance
      a b hab
  nlinarith

/-- The converse pressure inequality is sharpened by the exact zero population:
large vertical mass must overcome the *squarefree* diagonal, not the full
physical prefix. -/
theorem signedVerticalLineRunCovariance_ge_half_squarefree_excess
    (a b : ℕ) (hab : a ≤ b + 1) :
    (‖signedVerticalIntervalMass a b‖ ^ 2 -
        realMertensDiagonal ((b + 1) ^ 2)) / 2 ≤
      signedVerticalLineRunCovariance a b := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_mertensDiagonal_add_two_mul_covariance
      a b hab
  linarith

end RHLean.Proof
