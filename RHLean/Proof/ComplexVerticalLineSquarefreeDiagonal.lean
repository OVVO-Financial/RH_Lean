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
in which case its event is plus or minus `mu(n)`.  Hence its squared event is bounded by
`mu(n)^2`, not merely by one. -/
theorem signedVerticalLineEventStep_sq_le_moebius_sq
    (a b n : ℕ) :
    signedVerticalLineEventStep a b n ^ 2 ≤ realMoebiusStep n ^ 2 := by
  by_cases hb : n ∈ orderedEulerCutActiveChildren (b + 1)
  · by_cases ha : n ∈ orderedEulerCutActiveChildren a
    · have hsq : 0 ≤ realMoebiusStep n ^ 2 := sq_nonneg _
      simpa [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal, hb, ha] using hsq
    · simp [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal,
        orderedEulerCutChildChargeReal, realMoebiusStep, hb, ha]
  · by_cases ha : n ∈ orderedEulerCutActiveChildren a
    · simp [signedVerticalLineEventStep,
        orderedEulerCutChildEndpointChargeReal,
        orderedEulerCutChildChargeReal, realMoebiusStep, hb, ha]
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

/-! ## Elementary finite squarefree-density estimate

We now discharge the density input by the first five prime squares
`4, 9, 25, 49, 121`.  The proof is the second Bonferroni inequality on these
five deterministic divisibility events.  Pair intersections are exact because
the prime squares are pairwise coprime.  Counting multiples in `1,...,x` uses
`Nat.card_multiples'`; the only loss is one floor-unit for each of the five
positive singleton terms.

The resulting coefficient is slightly larger than `3/8`, so uniformly

`Z(x) >= (3/8) x - 5`.

No asymptotic squarefree-density theorem or independence assumption is used.
-/

private def squareDivIndicator (d n : ℕ) : ℝ :=
  if d ∣ n then 1 else 0

private theorem sum_squareDivIndicator_Icc (d x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, squareDivIndicator d n) =
      ((x / d : ℕ) : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 x, squareDivIndicator d n) =
        (((Finset.Icc 1 x).filter fun n => d ∣ n).card : ℝ) := by
      simp [squareDivIndicator]
    _ = (((Finset.range x.succ).filter fun n => n ≠ 0 ∧ d ∣ n).card : ℝ) := by
      have hset :
          (Finset.Icc 1 x).filter (fun n => d ∣ n) =
            (Finset.range x.succ).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
        ext n
        simp
        omega
      rw [hset]
    _ = ((x / d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.card_multiples' x d)

private theorem squareDivIndicator_mul_of_coprime
    {a b n : ℕ} (hab : Nat.Coprime a b) :
    squareDivIndicator a n * squareDivIndicator b n =
      squareDivIndicator (a * b) n := by
  have haProd : a ∣ a * b := ⟨b, rfl⟩
  have hbProd : b ∣ a * b := ⟨a, by simp [mul_comm]⟩
  by_cases ha : a ∣ n
  · by_cases hb : b ∣ n
    · have habd : a * b ∣ n := hab.mul_dvd_of_dvd_of_dvd ha hb
      simp [squareDivIndicator, ha, hb, habd]
    · have hnab : ¬ a * b ∣ n := by
        intro hnab
        exact hb (dvd_trans hbProd hnab)
      simp [squareDivIndicator, ha, hb, hnab]
  · have hnab : ¬ a * b ∣ n := by
      intro hnab
      exact ha (dvd_trans haProd hnab)
    simp [squareDivIndicator, ha, hnab]

private theorem sum_squareDivIndicator_mul_Icc
    (a b x : ℕ) (hab : Nat.Coprime a b) :
    (∑ n ∈ Finset.Icc 1 x,
      squareDivIndicator a n * squareDivIndicator b n) =
      ((x / (a * b) : ℕ) : ℝ) := by
  calc
    (∑ n ∈ Finset.Icc 1 x,
      squareDivIndicator a n * squareDivIndicator b n) =
        ∑ n ∈ Finset.Icc 1 x, squareDivIndicator (a * b) n := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact squareDivIndicator_mul_of_coprime hab
    _ = ((x / (a * b) : ℕ) : ℝ) :=
      sum_squareDivIndicator_Icc (a * b) x

private theorem natCast_div_ge_realDiv_sub_one
    (x d : ℕ) (hd : 0 < d) :
    (x : ℝ) / (d : ℝ) - 1 ≤ ((x / d : ℕ) : ℝ) := by
  have hmod : x % d < d := Nat.mod_lt x hd
  have hdecomp : d * (x / d) + x % d = x := Nat.div_add_mod x d
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmodR : ((x % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmod
  have hdecompR :
      (d : ℝ) * ((x / d : ℕ) : ℝ) + ((x % d : ℕ) : ℝ) = (x : ℝ) := by
    exact_mod_cast hdecomp
  have hlt :
      (x : ℝ) < (((x / d : ℕ) : ℝ) + 1) * (d : ℝ) := by
    nlinarith
  have hdiv :
      (x : ℝ) / (d : ℝ) < ((x / d : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ hdR).2 hlt
  linarith

private theorem natCast_div_le_realDiv
    (x d : ℕ) (hd : 0 < d) :
    ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  apply (le_div_iff₀ hdR).2
  exact_mod_cast (Nat.div_mul_le_self x d)

private def fivePrimeSquareBonferroni (n : ℕ) : ℝ :=
  squareDivIndicator 4 n +
    squareDivIndicator 9 n +
    squareDivIndicator 25 n +
    squareDivIndicator 49 n +
    squareDivIndicator 121 n -
  (squareDivIndicator 4 n * squareDivIndicator 9 n +
    squareDivIndicator 4 n * squareDivIndicator 25 n +
    squareDivIndicator 4 n * squareDivIndicator 49 n +
    squareDivIndicator 4 n * squareDivIndicator 121 n +
    squareDivIndicator 9 n * squareDivIndicator 25 n +
    squareDivIndicator 9 n * squareDivIndicator 49 n +
    squareDivIndicator 9 n * squareDivIndicator 121 n +
    squareDivIndicator 25 n * squareDivIndicator 49 n +
    squareDivIndicator 25 n * squareDivIndicator 121 n +
    squareDivIndicator 49 n * squareDivIndicator 121 n)

private theorem fivePrimeSquareBonferroni_le_zeroIndicator (n : ℕ) :
    fivePrimeSquareBonferroni n ≤ realMoebiusZeroIndicator n := by
  by_cases hhit :
      4 ∣ n ∨ 9 ∣ n ∨ 25 ∣ n ∨ 49 ∣ n ∨ 121 ∣ n
  · have hnsq : ¬ Squarefree n := by
      intro hsq
      rw [Nat.squarefree_iff_prime_squarefree] at hsq
      rcases hhit with h4 | h9 | h25 | h49 | h121
      · exact (hsq 2 (by norm_num)) (by simpa using h4)
      · exact (hsq 3 (by norm_num)) (by simpa using h9)
      · exact (hsq 5 (by norm_num)) (by simpa using h25)
      · exact (hsq 7 (by norm_num)) (by simpa using h49)
      · exact (hsq 11 (by norm_num)) (by simpa using h121)
    have hmu : μ n = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
    by_cases h4 : 4 ∣ n <;>
    by_cases h9 : 9 ∣ n <;>
    by_cases h25 : 25 ∣ n <;>
    by_cases h49 : 49 ∣ n <;>
    by_cases h121 : 121 ∣ n <;>
      simp [fivePrimeSquareBonferroni, squareDivIndicator,
        realMoebiusZeroIndicator, hmu, h4, h9, h25, h49, h121] <;>
      norm_num
  · have h4 : ¬ 4 ∣ n := by tauto
    have h9 : ¬ 9 ∣ n := by tauto
    have h25 : ¬ 25 ∣ n := by tauto
    have h49 : ¬ 49 ∣ n := by tauto
    have h121 : ¬ 121 ∣ n := by tauto
    by_cases hmu : μ n = 0 <;>
      simp [fivePrimeSquareBonferroni, squareDivIndicator,
        realMoebiusZeroIndicator, hmu, h4, h9, h25, h49, h121]

/-- **Uniform elementary zero-density estimate.**  The first five prime-square
faces alone force at least three-eighths of the physical sites to be Möbius
zeros, up to the five floor errors. -/
theorem realMertensZeroCount_ge_three_eighths_sub_five (x : ℕ) :
    (3 / 8 : ℝ) * (x : ℝ) - 5 ≤ (realMertensZeroCount x : ℝ) := by
  have hsum :
      (∑ n ∈ Finset.Icc 1 x, fivePrimeSquareBonferroni n) ≤
        ∑ n ∈ Finset.Icc 1 x, realMoebiusZeroIndicator n :=
    Finset.sum_le_sum (fun n _hn => fivePrimeSquareBonferroni_le_zeroIndicator n)
  have hbonf :
      (∑ n ∈ Finset.Icc 1 x, fivePrimeSquareBonferroni n) =
        (((x / 4 : ℕ) : ℝ) +
          ((x / 9 : ℕ) : ℝ) +
          ((x / 25 : ℕ) : ℝ) +
          ((x / 49 : ℕ) : ℝ) +
          ((x / 121 : ℕ) : ℝ)) -
        (((x / 36 : ℕ) : ℝ) +
          ((x / 100 : ℕ) : ℝ) +
          ((x / 196 : ℕ) : ℝ) +
          ((x / 484 : ℕ) : ℝ) +
          ((x / 225 : ℕ) : ℝ) +
          ((x / 441 : ℕ) : ℝ) +
          ((x / 1089 : ℕ) : ℝ) +
          ((x / 1225 : ℕ) : ℝ) +
          ((x / 3025 : ℕ) : ℝ) +
          ((x / 5929 : ℕ) : ℝ)) := by
    simp only [fivePrimeSquareBonferroni, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [sum_squareDivIndicator_Icc 4 x,
      sum_squareDivIndicator_Icc 9 x,
      sum_squareDivIndicator_Icc 25 x,
      sum_squareDivIndicator_Icc 49 x,
      sum_squareDivIndicator_Icc 121 x,
      sum_squareDivIndicator_mul_Icc 4 9 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 4 25 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 4 49 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 4 121 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 9 25 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 9 49 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 9 121 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 25 49 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 25 121 x (by norm_num),
      sum_squareDivIndicator_mul_Icc 49 121 x (by norm_num)]
  rw [hbonf, sum_realMoebiusZeroIndicator_eq_zeroCount] at hsum
  have h4 := natCast_div_ge_realDiv_sub_one x 4 (by norm_num)
  have h9 := natCast_div_ge_realDiv_sub_one x 9 (by norm_num)
  have h25 := natCast_div_ge_realDiv_sub_one x 25 (by norm_num)
  have h49 := natCast_div_ge_realDiv_sub_one x 49 (by norm_num)
  have h121 := natCast_div_ge_realDiv_sub_one x 121 (by norm_num)
  have h36 := natCast_div_le_realDiv x 36 (by norm_num)
  have h100 := natCast_div_le_realDiv x 100 (by norm_num)
  have h196 := natCast_div_le_realDiv x 196 (by norm_num)
  have h484 := natCast_div_le_realDiv x 484 (by norm_num)
  have h225 := natCast_div_le_realDiv x 225 (by norm_num)
  have h441 := natCast_div_le_realDiv x 441 (by norm_num)
  have h1089 := natCast_div_le_realDiv x 1089 (by norm_num)
  have h1225 := natCast_div_le_realDiv x 1225 (by norm_num)
  have h3025 := natCast_div_le_realDiv x 3025 (by norm_num)
  have h5929 := natCast_div_le_realDiv x 5929 (by norm_num)
  let C : ℝ :=
    1 / 4 + 1 / 9 + 1 / 25 + 1 / 49 + 1 / 121 -
      (1 / 36 + 1 / 100 + 1 / 196 + 1 / 484 + 1 / 225 +
        1 / 441 + 1 / 1089 + 1 / 1225 + 1 / 3025 + 1 / 5929)
  have hfloor :
      C * (x : ℝ) - 5 ≤
        (((x / 4 : ℕ) : ℝ) +
          ((x / 9 : ℕ) : ℝ) +
          ((x / 25 : ℕ) : ℝ) +
          ((x / 49 : ℕ) : ℝ) +
          ((x / 121 : ℕ) : ℝ)) -
        (((x / 36 : ℕ) : ℝ) +
          ((x / 100 : ℕ) : ℝ) +
          ((x / 196 : ℕ) : ℝ) +
          ((x / 484 : ℕ) : ℝ) +
          ((x / 225 : ℕ) : ℝ) +
          ((x / 441 : ℕ) : ℝ) +
          ((x / 1089 : ℕ) : ℝ) +
          ((x / 1225 : ℕ) : ℝ) +
          ((x / 3025 : ℕ) : ℝ) +
          ((x / 5929 : ℕ) : ℝ)) := by
    dsimp [C]
    linarith
  have hC : (3 / 8 : ℝ) ≤ C := by
    norm_num [C]
  have hx : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hscale : (3 / 8 : ℝ) * (x : ℝ) ≤ C * (x : ℝ) :=
    mul_le_mul_of_nonneg_right hC hx
  linarith

/-- **Compiled finite-density Green--Kubo bound.**  Substituting the elementary
five-prime-square sieve into the exact line-energy identity leaves a `5/8`
diagonal coefficient and the same signed cross-line covariance term. -/
theorem norm_signedVerticalIntervalMass_sq_le_five_eighths_endpoint_add_covariance
    (a b : ℕ) (hab : a ≤ b + 1) :
    ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
      (5 / 8 : ℝ) * ((((b + 1) ^ 2 - 1 : ℕ) : ℝ)) + 5 +
        2 * max 0 (signedVerticalLineRunCovariance a b) := by
  have hzero :=
    realMertensZeroCount_ge_three_eighths_sub_five ((b + 1) ^ 2 - 1)
  have hbase :=
    norm_signedVerticalIntervalMass_sq_le_of_zeroCount_lowerBound
      a b hab (3 / 8) 5 hzero
  norm_num at hbase ⊢
  exact hbase

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
