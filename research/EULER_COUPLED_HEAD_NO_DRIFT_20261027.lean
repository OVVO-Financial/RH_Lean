import Mathlib
import «research.EULER_ENDPOINT_CARRIER_SPARSITY_20261027»
import «research.MOBIUS_INVERSION_GLOBAL_CANCELLATION»

/-!
# Original Euler quotient windows: the already-proved global no-drift identity

An endpoint E_q is indexed by the explicit integer quotient q, NOT by
floor(N/r_q), which differs at a possibly empty terminal bucket.
The literal integer window satisfies E_(q+1)-E_q = |J_q| - L/b.

The truncated smooth Abel drift is *not* an independent cost:
the globally complete quotient Mertens sum equals 1 by the previously
certified Mobius inversion theorem. We retain the complete complementary
tail rather than declaring the truncated sum to be bounded.

No finite-C, fixed eta, or RH improvement is asserted.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- A genuinely wide historical quotient bucket cannot be empty. -/
theorem eulerBucket_nonempty_of_mul_succ_lt
    (R q : ℕ) (hq : 0 < q)
    (hsmall : q * (q + 1) < R - 1) :
    eulerBucketLow R q < eulerBucketHigh R q := by
  let N := R - 1
  let lo := eulerBucketLow R q
  let hi := eulerBucketHigh R q
  have hqle : q ≤ lo := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos q)).2
    change q * (q + 1) ≤ N
    omega
  have hmul : lo * (q + 1) ≤ N := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos q)).1
    change lo ≤ N / (q + 1)
    rfl
  have hstep : (lo + 1) * q ≤ N := by
    nlinarith [hqle, hmul]
  have hhi : lo + 1 ≤ hi := by
    apply (Nat.le_div_iff_mul_le hq).2
    simpa [Nat.mul_comm] using hstep
  omega

/-- Formal quotient-indexed endpoint. In an empty bucket the right endpoint
is not necessarily a representative of q, but THIS definition remains correct. -/
def eulerBucketIndexedEndpointQ (R q b : ℕ) : ℚ :=
  (eulerBucketJLower R q b : ℚ) -
    ((R + 1 : ℕ) : ℚ) * (q : ℚ) / (b : ℚ)

/-- The exact window-length-minus-smooth-drift identity. -/
theorem eulerEndpoint_diff_eq_window_sub (R q b : ℕ) :
    eulerBucketIndexedEndpointQ R (q + 1) b -
      eulerBucketIndexedEndpointQ R q b =
        ((eulerBucketJUpper R q b : ℕ) : ℚ) -
          ((eulerBucketJLower R q b : ℕ) : ℚ) -
          (((R + 1 : ℕ) : ℚ) / (b : ℚ)) := by
  unfold eulerBucketIndexedEndpointQ
  rw [← eulerBucketJUpper_eq_nextJLower R q b]
  push_cast
  ring

/-- Existing certified source, restated *without* a new analytic hypothesis.
All square-root Mertens quotient drift is globally annihilated by mu*1=delta. -/
theorem eulerGlobalHistoricalQuotientSum_eq_one
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ q ∈ Finset.Icc 1 N,
      mertensSummatoryInt (N / q)) = 1 := by
  have h := sum_moebius_prefix_floor_div_eq_one N hN
  simpa only [mertensSummatoryInt_eq_Icc] using h

/-- Exact truncated drift/payment identity. The smooth head is balanced
by the COMPLEMENTARY high-q Mertens tail, and hence is never an
independent uncontrolled variable. Importantly the complementary tail
is not asserted small: this is an exact inversion identity. -/
theorem eulerAbelSmoothDrift_eq_one_sub_complement
    (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQN : Q ≤ N) :
    (∑ q ∈ Finset.Ioc 1 Q,
       mertensSummatoryInt (N / q)) =
      1 - mertensSummatoryInt N -
        ∑ q ∈ Finset.Ioc Q N,
          mertensSummatoryInt (N / q) := by
  let f : ℕ → ℤ := fun q => mertensSummatoryInt (N / q)
  have hwhole :
      (∑ q ∈ Finset.Ioc 0 N, f q) = 1 := by
    simpa only [Ioc_zero_eq_Icc_one] using
      (eulerGlobalHistoricalQuotientSum_eq_one N hN)
  have hsplit1 := Finset.sum_Ioc_consecutive
    (f := f) (Nat.zero_le 1) hN
  have hsplit2 := Finset.sum_Ioc_consecutive
    (f := f) hQ hQN
  have hfirst :
      (∑ q ∈ Finset.Ioc 0 1, f q) = mertensSummatoryInt N := by
    simp [f]
  rw [hsplit1, hsplit2, hfirst] at hwhole
  change (∑ q ∈ Finset.Ioc 1 Q, f q) =
    1 - mertensSummatoryInt N -
      ∑ q ∈ Finset.Ioc Q N, f q
  omega

/-- Apply the already-proved no-drift identity to the exact rational
Abel coefficient d=(R+1)/b, retaining the whole complementary tail. -/
theorem eulerAbelSmoothDriftQ_eq_compensated
    (R Q b : ℕ) (hR : 2 ≤ R) (hQ : 1 ≤ Q) (hQN : Q ≤ R - 1) :
    - (((R + 1 : ℕ) : ℚ) / (b : ℚ)) *
      (∑ q ∈ Finset.Ioc 1 Q,
        eulerHistoricalMertensQ ((R - 1) / q)) =
        - (((R + 1 : ℕ) : ℚ) / (b : ℚ)) *
          (1 - eulerHistoricalMertensQ (R - 1) -
            ∑ q ∈ Finset.Ioc Q (R - 1),
              eulerHistoricalMertensQ ((R - 1) / q)) := by
  have hZ := eulerAbelSmoothDrift_eq_one_sub_complement
    (R - 1) Q (by omega : 1 ≤ R - 1) hQ hQN
  have hRat := congrArg (fun z : ℤ => (z : ℚ)) hZ
  have hCast :
      (∑ q ∈ Finset.Ioc 1 Q,
        eulerHistoricalMertensQ ((R - 1) / q)) =
      1 - eulerHistoricalMertensQ (R - 1) -
        ∑ q ∈ Finset.Ioc Q (R - 1),
          eulerHistoricalMertensQ ((R - 1) / q) := by
    simpa [eulerHistoricalMertensQ] using hRat
  rw [hCast]

#print axioms eulerBucket_nonempty_of_mul_succ_lt
#print axioms eulerEndpoint_diff_eq_window_sub
#print axioms eulerGlobalHistoricalQuotientSum_eq_one
#print axioms eulerAbelSmoothDrift_eq_one_sub_complement
#print axioms eulerAbelSmoothDriftQ_eq_compensated

end RHLean.Proof
