import Mathlib
import «research.VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE»
import «research.EXACT_LI_PURE_MODEL_CLOSURE»

/-!
# Critical half-weight of the discrete floor-Li mismatch

The floor-Li event stream has primitive mismatch

  eta(q) = [pi(q)-floor(Li_2(q))] - [pi(q-1)-floor(Li_2(q-1))].

This file puts that signed {-1,0,1} stream in the exact RH-critical
q^(-1/2) coordinate already used by the continuous Li model.

Two facts are proved.

1. Finite Abel inversion is exact.  If every critical prefix from an anchor A
   through N has norm at most B, then the unweighted backlog increment obeys

       |E(N)-E(A)| <= 2 sqrt(N) B.

   In particular, at N=R^2 an O(log R) critical-prefix bound gives the desired
   O(R log R) root-to-square population balance.

2. Replacing continuous Li singleton mass by floor-Li event mass is essentially
   free in this critical coordinate.  If

       r(n) = Li_2(n) - floor(Li_2(n)) in [0,1),

   then the weighted rounding tail is

       sum_{A<q<=X} q^(-1/2) [r(q)-r(q-1)],

   and finite Abel summation bounds its norm by

       2 / sqrt(A+1).

Thus flooring does not consume the critical logarithmic budget; its cost
vanishes as the root anchor grows.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-! ## Critical prefix of the integer backlog -/

/-- The floor-Li backlog, frozen at the lower anchor A. -/
def vfMidFloorLiBacklogTailState (A n : ℕ) : ℂ :=
  ((vfMidPrimeFloorLiIntegerBacklog (max A n) -
      vfMidPrimeFloorLiIntegerBacklog A : ℤ) : ℂ)

/-- Critical half-weighted prefix of the frozen floor-Li backlog.  Because the
state is constant through A, its finite differences start only at A+1. -/
def vfMidFloorLiCriticalMismatchPrefix (A N : ℕ) : ℂ :=
  weightedForwardDifferencePrefix criticalSqrtWeight
    (vfMidFloorLiBacklogTailState A) N

private theorem sqrtAbelIncrement_weightedCriticalPrefix
    (F : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    sqrtAbelIncrement
        (fun N => weightedForwardDifferencePrefix criticalSqrtWeight F N) n =
      F n - F (n - 1) := by
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hs :=
    weightedForwardDifferencePrefix_succ
      criticalSqrtWeight F (n - 1)
  rw [hpred] at hs
  unfold sqrtAbelIncrement
  rw [hs]
  unfold criticalSqrtWeight
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 hnpos
  have hsqrtne : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hsqrtpos)
  field_simp [hsqrtne]
  ring

private theorem sum_Icc_forwardDifference_complex
    (F : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (F n - F (n - 1))) =
      F N - F 0 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1), ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- Abel increments of the critical floor-Li prefix reconstruct the frozen
unweighted backlog exactly. -/
theorem sum_sqrtAbelIncrement_vfMidFloorLiCriticalMismatchPrefix
    (A N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      sqrtAbelIncrement (vfMidFloorLiCriticalMismatchPrefix A) n) =
      vfMidFloorLiBacklogTailState A N -
        vfMidFloorLiBacklogTailState A 0 := by
  calc
    (∑ n ∈ Finset.Icc 1 N,
        sqrtAbelIncrement (vfMidFloorLiCriticalMismatchPrefix A) n) =
      ∑ n ∈ Finset.Icc 1 N,
        (vfMidFloorLiBacklogTailState A n -
          vfMidFloorLiBacklogTailState A (n - 1)) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact sqrtAbelIncrement_weightedCriticalPrefix
          (vfMidFloorLiBacklogTailState A)
          (Finset.mem_Icc.mp hn).1
    _ = vfMidFloorLiBacklogTailState A N -
        vfMidFloorLiBacklogTailState A 0 :=
      sum_Icc_forwardDifference_complex
        (vfMidFloorLiBacklogTailState A) N

/-- Once N is beyond the anchor, the frozen state is exactly the endpoint
backlog increment. -/
theorem vfMidFloorLiBacklogTailState_eq_backlog_increment
    {A N : ℕ} (hAN : A ≤ N) :
    vfMidFloorLiBacklogTailState A N -
        vfMidFloorLiBacklogTailState A 0 =
      ((vfMidPrimeFloorLiIntegerBacklog N -
        vfMidPrimeFloorLiIntegerBacklog A : ℤ) : ℂ) := by
  unfold vfMidFloorLiBacklogTailState
  rw [max_eq_right hAN, max_eq_left (Nat.zero_le A)]
  push_cast
  ring

/-- **Critical Abel return for the discrete mismatch.**
A uniform B bound on every half-weighted prefix through N yields the unweighted
backlog increment at square-root scale. -/
theorem norm_vfMidPrimeFloorLiBacklog_increment_le_of_criticalPrefix
    {A N : ℕ} (hN : 1 ≤ N) (hAN : A ≤ N)
    {B : ℝ} (hB : 0 ≤ B)
    (hcrit : ∀ n : ℕ, n ≤ N →
      ‖vfMidFloorLiCriticalMismatchPrefix A n‖ ≤ B) :
    ‖((vfMidPrimeFloorLiIntegerBacklog N -
        vfMidPrimeFloorLiIntegerBacklog A : ℤ) : ℂ)‖ ≤
      2 * Real.sqrt (N : ℝ) * B := by
  have habel :=
    norm_sum_sqrtAbelIncrement_le
      (vfMidFloorLiCriticalMismatchPrefix A) N B hN hB hcrit
  rw [sum_sqrtAbelIncrement_vfMidFloorLiCriticalMismatchPrefix A N,
    vfMidFloorLiBacklogTailState_eq_backlog_increment hAN] at habel
  exact habel

/-- Root-to-square specialization.  This is the exact scale conversion needed
for the floor-Li population attack. -/
theorem norm_vfMidPrimeFloorLi_rootSquare_increment_le_of_criticalPrefix
    {R : ℕ} (hR : 2 ≤ R)
    {B : ℝ} (hB : 0 ≤ B)
    (hcrit : ∀ n : ℕ, n ≤ R ^ 2 →
      ‖vfMidFloorLiCriticalMismatchPrefix R n‖ ≤ B) :
    ‖((vfMidPrimeFloorLiIntegerBacklog (R ^ 2) -
        vfMidPrimeFloorLiIntegerBacklog R : ℤ) : ℂ)‖ ≤
      2 * (R : ℝ) * B := by
  have hN : 1 ≤ R ^ 2 := by nlinarith
  have hAN : R ≤ R ^ 2 := by nlinarith
  have h :=
    norm_vfMidPrimeFloorLiBacklog_increment_le_of_criticalPrefix
      hN hAN hB hcrit
  have hR0 : (0 : ℝ) ≤ R := by positivity
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hR0] at h
  exact h

/-! ## Vanishing critical cost of floor-Li rounding -/

/-- Real critical half-weight. -/
def vfMidCriticalRealWeight (q : ℕ) : ℝ :=
  (Real.sqrt (q : ℝ))⁻¹

/-- Signed critical correction incurred by replacing continuous Li singleton
mass with the discrete floor-Li event mass. -/
def vfMidFloorLiCriticalRoundingTail (A X : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc A X,
    (vfMidCriticalRealWeight q : ℂ) *
      ((vfMidFloorLiEndpointRounding q -
        vfMidFloorLiEndpointRounding (q - 1) : ℝ) : ℂ)

/-- **Flooring is asymptotically free in the critical coordinate.**
The complete critical rounding correction above anchor A is at most
2/sqrt(A+1), uniformly in the upper endpoint. -/
theorem norm_vfMidFloorLiCriticalRoundingTail_le
    {A X : ℕ} (hAX : A < X) :
    ‖vfMidFloorLiCriticalRoundingTail A X‖ ≤
      2 * (Real.sqrt ((A + 1 : ℕ) : ℝ))⁻¹ := by
  let d : ℕ → ℝ := fun q => vfMidCriticalRealWeight q
  let F : ℕ → ℂ := fun q => (vfMidFloorLiEndpointRounding q : ℂ)
  have hd : ∀ q, A < q → 0 ≤ d q := by
    intro q _hq
    dsimp [d, vfMidCriticalRealWeight]
    positivity
  have hanti : ∀ q, A < q → d (q + 1) ≤ d q := by
    intro q hAq
    have hqpos : (0 : ℝ) < q := by
      exact_mod_cast (show 0 < q by omega)
    have hqppos : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < q + 1 by omega)
    have hsqrtq : 0 < Real.sqrt (q : ℝ) :=
      Real.sqrt_pos.2 hqpos
    have hsqrtqp : 0 < Real.sqrt ((q + 1 : ℕ) : ℝ) :=
      Real.sqrt_pos.2 hqppos
    have hsqrtle :
        Real.sqrt (q : ℝ) ≤
          Real.sqrt ((q + 1 : ℕ) : ℝ) := by
      apply Real.sqrt_le_sqrt
      norm_num
    dsimp [d, vfMidCriticalRealWeight]
    exact (inv_le_inv₀ hsqrtqp hsqrtq).2 hsqrtle
  have hF : ∀ q, A ≤ q → ‖F q‖ ≤ (1 : ℝ) := by
    intro q _hq
    rcases vfMidFloorLiEndpointRounding_nonneg_lt_one q with
      ⟨hq0, hq1⟩
    dsimp [F]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1.le
  have hi :=
    densityTight_weighted_difference_invariant
      d F A (B := (1 : ℝ)) (by norm_num) hd hanti hF X hAX
  let S : ℂ :=
    ∑ q ∈ Finset.Ioc A X,
      (d q : ℂ) * (F (q - 1) - F q)
  have htail :
      vfMidFloorLiCriticalRoundingTail A X = -S := by
    unfold vfMidFloorLiCriticalRoundingTail S
    dsimp [d, F]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    ring
  have hdx0 : 0 ≤ d X := hd X hAX
  have hFX : ‖F X‖ ≤ (1 : ℝ) := hF X hAX.le
  have hterminal :
      ‖(d X : ℂ) * F X‖ ≤ d X := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hdx0]
    simpa using mul_le_mul_of_nonneg_left hFX hdx0
  have hS : ‖S‖ ≤ 2 * d (A + 1) := by
    have hre :
        S = (S + (d X : ℂ) * F X) - (d X : ℂ) * F X := by
      ring
    rw [hre]
    calc
      ‖(S + (d X : ℂ) * F X) - (d X : ℂ) * F X‖
          ≤ ‖S + (d X : ℂ) * F X‖ +
              ‖(d X : ℂ) * F X‖ := norm_sub_le _ _
      _ ≤ (2 * d (A + 1) - d X) * 1 + d X :=
        add_le_add hi hterminal
      _ = 2 * d (A + 1) := by ring
  rw [htail, norm_neg]
  simpa [d, vfMidCriticalRealWeight] using hS

/-! ## Exact direct-tail identification -/


/-- The frozen weighted prefix is exactly the direct critical mismatch tail.
Terms at or below the anchor vanish identically. -/
theorem vfMidFloorLiCriticalMismatchPrefix_eq_direct
    (A X : ℕ) :
    vfMidFloorLiCriticalMismatchPrefix A X =
      vfMidFloorLiDirectCriticalMismatchTail A X := by
  by_cases hAX : A < X
  · unfold vfMidFloorLiCriticalMismatchPrefix
      weightedForwardDifferencePrefix
      vfMidFloorLiDirectCriticalMismatchTail
    symm
    refine Finset.sum_subset ?_ ?_
    · intro q hq
      rcases Finset.mem_Ioc.mp hq with ⟨hAq, hqX⟩
      exact Finset.mem_Icc.mpr ⟨by omega, hqX⟩
    · intro q hqBig hqNot
      rcases Finset.mem_Icc.mp hqBig with ⟨_hq1, hqX⟩
      have hqA : q ≤ A := by
        by_contra hnot
        have hAq : A < q := Nat.lt_of_not_ge hnot
        exact hqNot (Finset.mem_Ioc.mpr ⟨hAq, hqX⟩)
      have hpredA : q - 1 ≤ A := (Nat.sub_le q 1).trans hqA
      unfold vfMidFloorLiBacklogTailState
      rw [max_eq_left hqA, max_eq_left hpredA]
      simp
  · have hXA : X ≤ A := Nat.le_of_not_gt hAX
    unfold vfMidFloorLiCriticalMismatchPrefix
      weightedForwardDifferencePrefix
      vfMidFloorLiDirectCriticalMismatchTail
    rw [Finset.Ioc_eq_empty_of_le hXA, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro q hq
    have hqX := (Finset.mem_Icc.mp hq).2
    have hqA : q ≤ A := hqX.trans hXA
    have hpredA : q - 1 ≤ A := (Nat.sub_le q 1).trans hqA
    unfold vfMidFloorLiBacklogTailState
    rw [max_eq_left hqA, max_eq_left hpredA]
    simp


/-! ## Exact discrete-to-continuous critical transfer -/

/-- Direct critical tail of the integer prime-minus-floor-Li backlog. -/
def vfMidFloorLiDirectCriticalMismatchTail (A X : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc A X,
    criticalSqrtWeight q *
      (((vfMidPrimeFloorLiIntegerBacklog q -
        vfMidPrimeFloorLiIntegerBacklog (q - 1) : ℤ) : ℂ))

/-- Direct critical tail of the classical prime-minus-Li discrepancy. -/
def vfMidPrimeLiCriticalMismatchTail (A X : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc A X,
    criticalSqrtWeight q *
      ((vfMidPrimeLiIntegerDiscrepancyReal q -
        vfMidPrimeLiIntegerDiscrepancyReal (q - 1) : ℝ) : ℂ)

private theorem criticalSqrtWeight_eq_realWeight_cast (q : ℕ) :
    criticalSqrtWeight q = (vfMidCriticalRealWeight q : ℂ) := by
  unfold criticalSqrtWeight vfMidCriticalRealWeight
  push_cast
  rfl

/-- **Exact critical split.**
The discrete prime-minus-floor-Li critical tail is the continuous
prime-minus-Li critical tail plus only the endpoint-rounding difference tail. -/
theorem vfMidFloorLiDirectCriticalMismatchTail_eq_primeLi_add_rounding
    (A X : ℕ) :
    vfMidFloorLiDirectCriticalMismatchTail A X =
      vfMidPrimeLiCriticalMismatchTail A X +
        vfMidFloorLiCriticalRoundingTail A X := by
  unfold vfMidFloorLiDirectCriticalMismatchTail
    vfMidPrimeLiCriticalMismatchTail
    vfMidFloorLiCriticalRoundingTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hqBack :=
    vfMidPrimeFloorLiIntegerBacklog_cast_eq_primeLi_add_rounding q
  have hpredBack :=
    vfMidPrimeFloorLiIntegerBacklog_cast_eq_primeLi_add_rounding (q - 1)
  have hqComplex := congrArg (fun x : ℝ => (x : ℂ)) hqBack
  have hpredComplex := congrArg (fun x : ℝ => (x : ℂ)) hpredBack
  push_cast at hqComplex hpredComplex
  rw [criticalSqrtWeight_eq_realWeight_cast]
  linear_combination
    (vfMidCriticalRealWeight q : ℂ) * hqComplex -
      (vfMidCriticalRealWeight q : ℂ) * hpredComplex

/-- The exact transfer costs at most the already-proved vanishing rounding
budget. -/
theorem norm_vfMidFloorLiDirectCriticalMismatchTail_sub_primeLi_le
    {A X : ℕ} (hAX : A < X) :
    ‖vfMidFloorLiDirectCriticalMismatchTail A X -
        vfMidPrimeLiCriticalMismatchTail A X‖ ≤
      2 * (Real.sqrt ((A + 1 : ℕ) : ℝ))⁻¹ := by
  rw [vfMidFloorLiDirectCriticalMismatchTail_eq_primeLi_add_rounding,
    add_sub_cancel_left]
  exact norm_vfMidFloorLiCriticalRoundingTail_le hAX

/-- Consequently any logarithmic envelope for the continuous critical tail
transfers to the discrete floor-Li mismatch with only a vanishing additive
term. -/
theorem norm_vfMidFloorLiDirectCriticalMismatchTail_le_of_primeLi
    {A X : ℕ} (hAX : A < X) {B : ℝ}
    (hB : ‖vfMidPrimeLiCriticalMismatchTail A X‖ ≤ B) :
    ‖vfMidFloorLiDirectCriticalMismatchTail A X‖ ≤
      B + 2 * (Real.sqrt ((A + 1 : ℕ) : ℝ))⁻¹ := by
  rw [vfMidFloorLiDirectCriticalMismatchTail_eq_primeLi_add_rounding]
  calc
    ‖vfMidPrimeLiCriticalMismatchTail A X +
        vfMidFloorLiCriticalRoundingTail A X‖
        ≤ ‖vfMidPrimeLiCriticalMismatchTail A X‖ +
            ‖vfMidFloorLiCriticalRoundingTail A X‖ := norm_add_le _ _
    _ ≤ B + 2 * (Real.sqrt ((A + 1 : ℕ) : ℝ))⁻¹ :=
      add_le_add hB (norm_vfMidFloorLiCriticalRoundingTail_le hAX)


/-- The frozen prefix itself therefore differs from the continuous
prime-minus-Li critical tail only by the vanishing rounding correction. -/
theorem vfMidFloorLiCriticalMismatchPrefix_eq_primeLi_add_rounding
    (A X : ℕ) :
    vfMidFloorLiCriticalMismatchPrefix A X =
      vfMidPrimeLiCriticalMismatchTail A X +
        vfMidFloorLiCriticalRoundingTail A X := by
  rw [vfMidFloorLiCriticalMismatchPrefix_eq_direct,
    vfMidFloorLiDirectCriticalMismatchTail_eq_primeLi_add_rounding]

/-- **Complete critical reduction.**
If the continuous prime-minus-Li critical tail is uniformly bounded by B on
the root-to-square window, the integer floor-Li backlog moves by at most
2 R times B plus the vanishing floor-rounding budget. -/
theorem norm_vfMidPrimeFloorLi_rootSquare_increment_le_of_primeLiCritical
    {R : ℕ} (hR : 2 ≤ R) {B : ℝ} (hB : 0 ≤ B)
    (hcrit : ∀ n : ℕ, n ≤ R ^ 2 → R < n →
      ‖vfMidPrimeLiCriticalMismatchTail R n‖ ≤ B) :
    ‖((vfMidPrimeFloorLiIntegerBacklog (R ^ 2) -
        vfMidPrimeFloorLiIntegerBacklog R : ℤ) : ℂ)‖ ≤
      2 * (R : ℝ) *
        (B + 2 * (Real.sqrt ((R + 1 : ℕ) : ℝ))⁻¹) := by
  let E : ℝ :=
    B + 2 * (Real.sqrt ((R + 1 : ℕ) : ℝ))⁻¹
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hprefix : ∀ n : ℕ, n ≤ R ^ 2 →
      ‖vfMidFloorLiCriticalMismatchPrefix R n‖ ≤ E := by
    intro n hn
    by_cases hRn : R < n
    · rw [vfMidFloorLiCriticalMismatchPrefix_eq_primeLi_add_rounding]
      calc
        ‖vfMidPrimeLiCriticalMismatchTail R n +
            vfMidFloorLiCriticalRoundingTail R n‖
            ≤ ‖vfMidPrimeLiCriticalMismatchTail R n‖ +
                ‖vfMidFloorLiCriticalRoundingTail R n‖ :=
              norm_add_le _ _
        _ ≤ B + 2 * (Real.sqrt ((R + 1 : ℕ) : ℝ))⁻¹ :=
          add_le_add (hcrit n hn hRn)
            (norm_vfMidFloorLiCriticalRoundingTail_le hRn)
        _ = E := rfl
    · have hnR : n ≤ R := Nat.le_of_not_gt hRn
      rw [vfMidFloorLiCriticalMismatchPrefix_eq_direct]
      unfold vfMidFloorLiDirectCriticalMismatchTail
      rw [Finset.Ioc_eq_empty_of_le hnR, Finset.sum_empty, norm_zero]
      exact hE
  have hmain :=
    norm_vfMidPrimeFloorLi_rootSquare_increment_le_of_criticalPrefix
      hR hE hprefix
  simpa [E] using hmain


end RHLean.Analysis
