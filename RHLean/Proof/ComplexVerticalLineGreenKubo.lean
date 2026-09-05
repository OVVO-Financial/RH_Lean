import Mathlib
import RHLean.Analysis.BlockCovarianceDecomposition
import RHLean.Proof.ComplexVerticalFiberSpacing

/-!
# Green--Kubo inequality on physical squared-Fermat child lines

`ComplexVerticalFiberSpacing` reduces the ordered Euler frontier at each root to
one active atom per physical child integer and proves that a child present at
both endpoints contributes exactly zero to the run difference.  This file takes
the next quantitative step: square the *whole signed birth/death population*
before taking any absolute values.

For a run from root `a` to root `b+1`, define one real event variable at each
physical child integer `n`:

* `0` if the child has the same endpoint status;
* `-mu(n)` if the child is born into the active endpoint set;
* `+mu(n)` if the child dies from the active endpoint set.

The sum of these variables is exactly the complex vertical-interval mass after
casting to `C`.  Hence the generic deterministic Green--Kubo identity gives

`||V(a,b)||^2 = diagonal + 2 * lineCovariance`.

Every event variable lies in `{-1,0,1}`, and every active child at root `R` is
strictly below `R^2`.  Therefore, without counting births and deaths separately,

`diagonal <= (b+1)^2`.

This yields the unconditional one-sided inequality

`||V(a,b)||^2 <= (b+1)^2 + 2 * max 0 lineCovariance`.

Under strict subdoubling this becomes

`||V(a,b)||^2 <= 2*a^2 + 2 * max 0 lineCovariance`.

Thus the diagonal is already at the required root-square energy scale.  The
only quantity capable of producing supercritical growth is the *positive*
aggregate covariance among distinct physical birth/death lines.  No triangle
inequality over lines, unsigned population bound, PNT input, independence
hypothesis, or RH hypothesis is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Real endpoint charges on physical child lines -/

/-- Real form of the conserved physical-child charge `-mu(n)`. -/
def orderedEulerCutChildChargeReal (n : ℕ) : ℝ :=
  -((μ n : ℤ) : ℝ)

@[simp] theorem orderedEulerCutChildChargeReal_cast (n : ℕ) :
    ((orderedEulerCutChildChargeReal n : ℝ) : ℂ) =
      orderedEulerCutChildCharge n := by
  simp [orderedEulerCutChildChargeReal, orderedEulerCutChildCharge,
    canonicalMoebiusWeight]

/-- Real endpoint contribution of one physical child line. -/
def orderedEulerCutChildEndpointChargeReal (R n : ℕ) : ℝ :=
  if n ∈ orderedEulerCutActiveChildren R then
    orderedEulerCutChildChargeReal n
  else 0

@[simp] theorem orderedEulerCutChildEndpointChargeReal_cast (R n : ℕ) :
    ((orderedEulerCutChildEndpointChargeReal R n : ℝ) : ℂ) =
      orderedEulerCutChildEndpointCharge R n := by
  by_cases h : n ∈ orderedEulerCutActiveChildren R <;>
    simp [orderedEulerCutChildEndpointChargeReal,
      orderedEulerCutChildEndpointCharge, h]

/-- Every active physical child lies strictly below the square of its current
root.  This is the birth-root square cutoff, expressed directly on the child
coordinate. -/
theorem orderedEulerCutActiveChild_lt_root_sq
    {R n : ℕ} (hn : n ∈ orderedEulerCutActiveChildren R) :
    n < R ^ 2 := by
  rcases Finset.mem_image.mp hn with ⟨y, hy, rfl⟩
  have hshape := orderedEulerCutShape_of_mem_carrier hy
  have hocc := mem_orderedEulerCutCarrier.mp hy
  have hsqrt :=
    (orderedEulerCutOccursAt_sqrt_factor_window hshape hocc).2.1
  exact (Nat.sqrt_lt').1 hsqrt

/-- Hence the active-child set embeds in the physical integer prefix below
`R^2`. -/
theorem orderedEulerCutActiveChildren_subset_range_sq (R : ℕ) :
    orderedEulerCutActiveChildren R ⊆ Finset.range (R ^ 2) := by
  intro n hn
  exact Finset.mem_range.mpr (orderedEulerCutActiveChild_lt_root_sq hn)

/-- Summing the endpoint-charge field over any ambient prefix containing `R^2`
recovers exactly the active-child charge sum. -/
theorem signedBlockPrefix_childEndpointChargeReal_eq_activeChildSum
    (R K : ℕ) (hRK : R ^ 2 ≤ K) :
    signedBlockPrefix (orderedEulerCutChildEndpointChargeReal R) K =
      ∑ n ∈ orderedEulerCutActiveChildren R,
        orderedEulerCutChildChargeReal n := by
  unfold signedBlockPrefix orderedEulerCutChildEndpointChargeReal
  have hfilter :
      (Finset.range K).filter (fun n => n ∈ orderedEulerCutActiveChildren R) =
        orderedEulerCutActiveChildren R := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hn
      refine ⟨?_, hn⟩
      exact lt_of_lt_of_le (orderedEulerCutActiveChild_lt_root_sq hn) hRK
  rw [← Finset.sum_filter, hfilter]

/-! ## The signed line-event trajectory -/

/-- Endpoint change carried by one physical child line.  Internal transport of
a line present at both endpoints is already zero here. -/
def signedVerticalLineEventStep (a b n : ℕ) : ℝ :=
  orderedEulerCutChildEndpointChargeReal (b + 1) n -
    orderedEulerCutChildEndpointChargeReal a n

/-- Total real birth/death mass, evaluated on the physical child prefix large
enough to contain both endpoint carriers. -/
def signedVerticalLineRunMassReal (a b : ℕ) : ℝ :=
  signedBlockPrefix (signedVerticalLineEventStep a b) ((b + 1) ^ 2)

/-- Diagonal energy of the physical line-event trajectory. -/
def signedVerticalLineRunDiagonal (a b : ℕ) : ℝ :=
  signedBlockEnergy (signedVerticalLineEventStep a b) ((b + 1) ^ 2)

/-- Aggregate covariance over distinct physical birth/death lines.  This is a
signed pair sum; negative covariance helps and is never replaced by its
absolute value. -/
def signedVerticalLineRunCovariance (a b : ℕ) : ℝ :=
  signedBlockCrossCovariance (signedVerticalLineEventStep a b) ((b + 1) ^ 2)

/-- The real line-event sum is exactly the difference of the two active-child
charge sums. -/
theorem signedVerticalLineRunMassReal_eq_activeChildChargeDifference
    (a b : ℕ) (hab : a ≤ b + 1) :
    signedVerticalLineRunMassReal a b =
      (∑ n ∈ orderedEulerCutActiveChildren (b + 1),
        orderedEulerCutChildChargeReal n) -
      ∑ n ∈ orderedEulerCutActiveChildren a,
        orderedEulerCutChildChargeReal n := by
  unfold signedVerticalLineRunMassReal signedVerticalLineEventStep
    signedBlockPrefix
  rw [Finset.sum_sub_distrib]
  have haSq : a ^ 2 ≤ (b + 1) ^ 2 :=
    Nat.pow_le_pow_left hab 2
  have hright :=
    signedBlockPrefix_childEndpointChargeReal_eq_activeChildSum
      (b + 1) ((b + 1) ^ 2) (le_refl _)
  have hleft :=
    signedBlockPrefix_childEndpointChargeReal_eq_activeChildSum
      a ((b + 1) ^ 2) haSq
  unfold signedBlockPrefix at hright hleft
  rw [hright, hleft]

/-- The line-event mass is literally the already-formalized complex vertical
run mass. -/
theorem signedVerticalLineRunMassReal_cast_eq_verticalMass
    (a b : ℕ) (hab : a ≤ b + 1) :
    ((signedVerticalLineRunMassReal a b : ℝ) : ℂ) =
      signedVerticalIntervalMass a b := by
  rw [signedVerticalLineRunMassReal_eq_activeChildChargeDifference a b hab,
    signedVerticalIntervalMass_eq_activeChildChargeDifference]
  push_cast
  simp_rw [orderedEulerCutChildChargeReal_cast]

/-! ## Green--Kubo before every magnitude estimate -/

/-- Exact square expansion of the complete signed physical line-event
population. -/
theorem signedVerticalLineRunMassReal_sq_eq_diagonal_add_two_mul_covariance
    (a b : ℕ) :
    signedVerticalLineRunMassReal a b ^ 2 =
      signedVerticalLineRunDiagonal a b +
        2 * signedVerticalLineRunCovariance a b := by
  exact signedBlockPrefix_sq_eq_energy_add_two_mul_cross
    (signedVerticalLineEventStep a b) ((b + 1) ^ 2)

/-- Every physical line event has squared charge at most one.  This uses only
`mu(n) in {-1,0,1}` and keeps the birth/death sign intact. -/
theorem signedVerticalLineEventStep_sq_le_one
    (a b n : ℕ) :
    signedVerticalLineEventStep a b n ^ 2 ≤ 1 := by
  have hmu := realMoebiusStep_sq_le_one n
  by_cases hb : n ∈ orderedEulerCutActiveChildren (b + 1)
  · by_cases ha : n ∈ orderedEulerCutActiveChildren a
    · simp [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal, hb, ha]
    · simpa [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal,
        orderedEulerCutChildChargeReal, realMoebiusStep, hb, ha]
        using hmu
  · by_cases ha : n ∈ orderedEulerCutActiveChildren a
    · simpa [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal,
        orderedEulerCutChildChargeReal, realMoebiusStep, hb, ha]
        using hmu
    · simp [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal, hb, ha]

/-- **Root-square diagonal bound.**  The entire birth/death diagonal is already
at RH energy scale.  No estimate of the unsigned number of Euler atoms is used. -/
theorem signedVerticalLineRunDiagonal_le_endpoint_sq
    (a b : ℕ) :
    signedVerticalLineRunDiagonal a b ≤ (((b + 1) ^ 2 : ℕ) : ℝ) := by
  unfold signedVerticalLineRunDiagonal signedBlockEnergy
  calc
    (∑ n ∈ Finset.range ((b + 1) ^ 2),
        signedVerticalLineEventStep a b n ^ 2) ≤
      ∑ _n ∈ Finset.range ((b + 1) ^ 2), (1 : ℝ) := by
        exact Finset.sum_le_sum
          (fun n _hn => signedVerticalLineEventStep_sq_le_one a b n)
    _ = (((b + 1) ^ 2 : ℕ) : ℝ) := by simp

/-- Norm-square of the original complex vertical mass is the ordinary square
of the real birth/death line sum. -/
theorem norm_signedVerticalIntervalMass_sq_eq_lineRunMassReal_sq
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 =
      signedVerticalLineRunMassReal a b ^ 2 := by
  rw [← signedVerticalLineRunMassReal_cast_eq_verticalMass a b hab,
    Complex.norm_real, Real.norm_eq_abs]
  exact sq_abs _

/-- Exact Green--Kubo identity stated directly on the complex vertical mass. -/
theorem norm_signedVerticalIntervalMass_sq_eq_lineDiagonal_add_two_mul_covariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 =
      signedVerticalLineRunDiagonal a b +
        2 * signedVerticalLineRunCovariance a b := by
  rw [norm_signedVerticalIntervalMass_sq_eq_lineRunMassReal_sq a b hab]
  exact signedVerticalLineRunMassReal_sq_eq_diagonal_add_two_mul_covariance a b

/-- **Actual unconditional one-sided inequality.**  The diagonal is root-square,
so only positive aggregate covariance can push the signed birth/death mass
above root scale. -/
theorem norm_signedVerticalIntervalMass_sq_le_endpoint_sq_add_two_mul_covariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      (((b + 1) ^ 2 : ℕ) : ℝ) +
        2 * signedVerticalLineRunCovariance a b := by
  have hid :=
    norm_signedVerticalIntervalMass_sq_eq_lineDiagonal_add_two_mul_covariance
      a b hab
  have hdiag := signedVerticalLineRunDiagonal_le_endpoint_sq a b
  linarith

/-- Negative line covariance is harmless.  This is the unconditional envelope
with only the positive part of the genuine signed pair sum remaining. -/
theorem norm_signedVerticalIntervalMass_sq_le_endpoint_sq_add_two_mul_positiveCovariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      (((b + 1) ^ 2 : ℕ) : ℝ) +
        2 * max 0 (signedVerticalLineRunCovariance a b) := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_endpoint_sq_add_two_mul_covariance
      a b hab
  have hcov : signedVerticalLineRunCovariance a b ≤
      max 0 (signedVerticalLineRunCovariance a b) :=
    le_max_right _ _
  linarith

/-- Any proposed upper budget on the *one-sided signed covariance* immediately
bounds the whole birth/death population.  There is no absolute value on the
covariance hypothesis. -/
theorem norm_signedVerticalIntervalMass_sq_le_of_lineCovariance_le
    (a b : ℕ) (hab : a ≤ b + 1) (B : ℝ)
    (hcov : signedVerticalLineRunCovariance a b ≤ B) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      (((b + 1) ^ 2 : ℕ) : ℝ) + 2 * B := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_endpoint_sq_add_two_mul_covariance
      a b hab
  linarith

/-- Conversely, a super-root vertical mass forces positive covariance among
distinct birth/death lines.  This is the exact pressure inequality to attack
with the sequential Euler geometry. -/
theorem signedVerticalLineRunCovariance_ge_half_excess
    (a b : ℕ) (hab : a ≤ b + 1) :
    (‖signedVerticalIntervalMass a b‖ ^ 2 -
        (((b + 1) ^ 2 : ℕ) : ℝ)) / 2 ≤
      signedVerticalLineRunCovariance a b := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_endpoint_sq_add_two_mul_covariance
      a b hab
  linarith

/-- **Subdoubling root-scale inequality.**  On the frozen horizon the physical
diagonal is at most `2*a^2`, so the exact remaining obstruction is only the
positive cross-line covariance. -/
theorem norm_signedVerticalIntervalMass_sq_le_subdoubling_root_sq_add_covariance
    (a b : ℕ) (hab : a ≤ b + 1)
    (hsub : (b + 1) ^ 2 < 2 * a ^ 2) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      (((2 * a ^ 2 : ℕ) : ℝ)) +
        2 * max 0 (signedVerticalLineRunCovariance a b) := by
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_endpoint_sq_add_two_mul_positiveCovariance
      a b hab
  have hsqNat : (b + 1) ^ 2 ≤ 2 * a ^ 2 := Nat.le_of_lt hsub
  have hsqReal :
      ((((b + 1) ^ 2 : ℕ) : ℝ)) ≤ (((2 * a ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hsqNat
  linarith

end RHLean.Proof
