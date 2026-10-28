import Mathlib
import «research.EULER_CARRY_CLIPPED_INTERIOR_20261027»

/-!
# Genuine Euler endpoint carriers: small-a singleton tail and sharp carry payment

All objects refer to the ORIGINAL Mobius signs and the exact self-dual
integer horizon X_R=R^2-1. This is the next source-faithful reduction
after #1038: no finite-C, fixed eta, or RH claim is introduced.

The high quotient bucket tail is a complete partition of a historical
small-a prefix. It is NOT 968 separate contributing q populations at R=1000.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- The original endpoint carry vanishes on the first (q=1) bucket,
because its right endpoint is the exact divisor R-1. -/
theorem eulerEndpointCarry_q_one_zero (R b : ℕ) (hR : 2 ≤ R) :
    eulerBucketRightCarry R 1 b = 0 := by
  have hN : 0 < R - 1 := by omega
  have hdiv : (R - 1) / (R - 1) = 1 := Nat.div_self hN
  simpa [eulerBucketRightCarry, eulerBucketHigh] using
    (eulerBucketCarry_zero_of_dvd R 1 b (R - 1)
      hR hN (dvd_refl _) hdiv)

/-- The right endpoint's residual t=N-q*r is exactly N mod q.
A legitimate bucket endpoint is essential: this fails for arbitrary q
with r=floor(N/q) unless r belongs to the corresponding quotient bucket. -/
theorem eulerEndpointRight_remainder_eq_mod_q
    (R q : ℕ) (hq : 0 < q)
    (hne : eulerBucketLow R q < eulerBucketHigh R q) :
    (R - 1) % (eulerBucketHigh R q) = (R - 1) % q := by
  let r := eulerBucketHigh R q
  have hrMem : r ∈ eulerBucketIndices R q :=
    eulerBucketRight_mem R q hne
  have hr : 0 < r := by
    have h := (Finset.mem_Ioc.mp hrMem).1
    have hz : 0 ≤ eulerBucketLow R q := Nat.zero_le _
    omega
  have hqr : (R - 1) / r = q :=
    eulerBucketIndices_quotient R q r hq hrMem
  have hdq := Nat.div_add_mod (R - 1) q
  have hdr := Nat.div_add_mod (R - 1) r
  change q * r + (R - 1) % q = R - 1 at hdq
  rw [hqr] at hdr
  have hdr' : q * r + (R - 1) % r = R - 1 := by
    simpa only [Nat.mul_comm r q] using hdr
  change (R - 1) % r = (R - 1) % q
  exact Nat.add_left_cancel (hdr'.trans hdq.symm)

/-- Original endpoint carry has the sharp *q-dependent* upper bound.
In particular this is far below the whole-bucket N/b+1 budget when
q is small and the divisor remainder N mod q is small. -/
theorem eulerEndpointCarry_le_sharp
    (R q b : ℕ) (hR : 2 ≤ R) (hq : 0 < q) (hb : 0 < b)
    (hne : eulerBucketLow R q < eulerBucketHigh R q) :
    eulerBucketRightCarry R q b ≤
      ((R + 1) * (q - 1)) / (b * eulerBucketHigh R q) + 1 := by
  let r := eulerBucketHigh R q
  let rho := ((R + 1) * q) % b
  let t := (R - 1) % r
  have hrMem : r ∈ eulerBucketIndices R q :=
    eulerBucketRight_mem R q hne
  have hr : 0 < r := by
    have h := (Finset.mem_Ioc.mp hrMem).1
    have hz : 0 ≤ eulerBucketLow R q := Nat.zero_le _
    omega
  have hqexact : (R - 1) / r = q :=
    eulerBucketIndices_quotient R q r hq hrMem
  have hrho : rho < b := Nat.mod_lt _ hb
  have ht : t < q := by
    change (R - 1) % r < q
    have heq := eulerEndpointRight_remainder_eq_mod_q R q hq hne
    change (R - 1) % r = (R - 1) % q at heq
    rw [heq]
    exact Nat.mod_lt _ hq
  have hmul :
      r * rho + (R + 1) * t ≤
        r * b + (R + 1) * (q - 1) := by
    have hrhoLe : rho ≤ b := le_of_lt hrho
    have htLe : t ≤ q - 1 := by omega
    exact Nat.add_le_add
      (Nat.mul_le_mul_left r hrhoLe)
      (Nat.mul_le_mul_left (R + 1) htLe)
  have hdiv :
      (r * rho + (R + 1) * t) / (r * b) ≤
        (r * b + (R + 1) * (q - 1)) / (r * b) :=
    Nat.div_le_div_right hmul
  have hden : 0 < r * b := Nat.mul_pos hr hb
  have hadd :
      (r * b + (R + 1) * (q - 1)) / (r * b) =
        ((R + 1) * (q - 1)) / (r * b) + 1 := by
    calc
      _ = (r * b * 1 + (R + 1) * (q - 1)) / (r * b) := by ring
      _ = 1 + ((R + 1) * (q - 1)) / (r * b) :=
        Nat.mul_add_div hden 1 _
      _ = ((R + 1) * (q - 1)) / (r * b) + 1 := by omega
  have hformula := eulerBucketCarry_eq_euclidean R q b r hR hr hb hqexact
  change eulerBucketRightCarry R q b =
    (r * rho + (R + 1) * t) / (r * b) at hformula
  rw [hformula]
  calc
    _ ≤ (r * b + (R + 1) * (q - 1)) / (r * b) := hdiv
    _ = ((R + 1) * (q - 1)) / (b * r) + 1 := by
      rw [hadd, Nat.mul_comm r b]

/-- High-q historical buckets are literal singletons or empty, not
independent sum variables. -/
theorem eulerEndpointLargeBucket_eq_singleton
    (R q : ℕ) (hq : 0 < q)
    (hlarge : R - 1 ≤ q * (q + 1))
    (hne : eulerBucketLow R q < eulerBucketHigh R q) :
    eulerBucketIndices R q = {eulerBucketHigh R q} := by
  have hbound :=
    eulerBucketHigh_le_low_add_one_of_large_q R q hq hlarge
  have hEq : eulerBucketHigh R q = eulerBucketLow R q + 1 := by omega
  ext a
  simp only [eulerBucketIndices, Finset.mem_Ioc, Finset.mem_singleton]
  omega

/-- Punched signed singleton mass in one high-q quotient bucket. -/
theorem eulerEndpointLargeBucket_punched_mass
    (R q : ℕ) (hq : 0 < q)
    (hlarge : R - 1 ≤ q * (q + 1))
    (hne : eulerBucketLow R q < eulerBucketHigh R q) :
    (∑ a ∈ (eulerBucketIndices R q).filter (fun a => ¬ a ∣ R - 1),
      eulerMuQ a) =
        if eulerBucketHigh R q ∣ R - 1 then 0
        else eulerMuQ (eulerBucketHigh R q) := by
  rw [eulerEndpointLargeBucket_eq_singleton R q hq hlarge hne]
  rw [Finset.sum_filter]
  by_cases hd : eulerBucketHigh R q ∣ R - 1
  · simp [hd]
  · simp [hd]

/-- For q>=Q, every original historical a in its quotient bucket has
a<=floor(N/Q), and the quotient q is uniquely N/a. -/
theorem eulerEndpointBucket_mem_iff_small_historical
    (R Q q a : ℕ) (hQ : 0 < Q)
    (hq : q ∈ Finset.Icc Q (R - 1)) :
    a ∈ eulerBucketIndices R q ↔
      a ∈ Finset.Icc 1 ((R - 1) / Q) ∧ (R - 1) / a = q := by
  have hqQ : Q ≤ q := (Finset.mem_Icc.mp hq).1
  have hqN : q ≤ R - 1 := (Finset.mem_Icc.mp hq).2
  have hqpos : 0 < q := lt_of_lt_of_le hQ hqQ
  constructor
  · intro ha
    have hquot := eulerBucketIndices_quotient R q a hqpos ha
    have haLo := (Finset.mem_Ioc.mp ha).1
    have haHi := (Finset.mem_Ioc.mp ha).2
    have haPos : 0 < a := by
      have hz : 0 ≤ eulerBucketLow R q := Nat.zero_le _
      omega
    have hmul : q * a ≤ R - 1 := by
      have hdiv := (Nat.le_div_iff_mul_le hqpos).1 haHi
      simpa [Nat.mul_comm] using hdiv
    have hQmul : Q * a ≤ R - 1 := by
      nlinarith
    have hupper : a ≤ (R - 1) / Q :=
      (Nat.le_div_iff_mul_le hQ).2
        (by simpa [Nat.mul_comm] using hQmul)
    exact ⟨Finset.mem_Icc.mpr ⟨haPos, hupper⟩, hquot⟩
  · rintro ⟨haSmall, hquot⟩
    have haPos : 0 < a := (Finset.mem_Icc.mp haSmall).1
    have hdivLe : a ≤ (R - 1) / q := by
      apply (Nat.le_div_iff_mul_le hqpos).2
      have hmul := (Nat.le_div_iff_mul_le haPos).1
        (show q ≤ (R - 1) / a by omega)
      simpa [Nat.mul_comm] using hmul
    have hdivLt : (R - 1) / (q + 1) < a := by
      apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos q)).2
      have hmul := (Nat.div_lt_iff_lt_mul haPos).1
        (show (R - 1) / a < q + 1 by omega)
      simpa [Nat.mul_comm] using hmul
    exact Finset.mem_Ioc.mpr ⟨hdivLt, hdivLe⟩

/-- COMPLETE high-q partition identity, valid for any arithmetic weight f.
It is stronger than a singleton approximation: the original buckets
partition the literal small-a prefix without overcounting or omissions. -/
theorem eulerEndpointTail_buckets_partition
    (R Q : ℕ) (hQ : 0 < Q) (_hQN : Q ≤ R - 1)
    (f : ℕ → ℚ) :
    (∑ q ∈ Finset.Icc Q (R - 1),
        ∑ a ∈ eulerBucketIndices R q, f a) =
      ∑ a ∈ Finset.Icc 1 ((R - 1) / Q), f a := by
  let S := Finset.Icc 1 ((R - 1) / Q)
  let T := Finset.Icc Q (R - 1)
  have hinner (q : ℕ) (hq : q ∈ T) :
      (∑ a ∈ eulerBucketIndices R q, f a) =
        ∑ a ∈ S, if (R - 1) / a = q then f a else 0 := by
    have hset :
        S.filter (fun a => (R - 1) / a = q) =
        eulerBucketIndices R q := by
      ext a
      simp only [Finset.mem_filter]
      exact (eulerEndpointBucket_mem_iff_small_historical R Q q a hQ hq).symm
    rw [← Finset.sum_filter]
    rw [hset]
  calc
    (∑ q ∈ T, ∑ a ∈ eulerBucketIndices R q, f a) =
      ∑ q ∈ T, ∑ a ∈ S,
        if (R - 1) / a = q then f a else 0 := by
          apply Finset.sum_congr rfl
          intro q hq
          exact hinner q hq
    _ = ∑ a ∈ S, ∑ q ∈ T,
        if (R - 1) / a = q then f a else 0 := Finset.sum_comm
    _ = ∑ a ∈ S, f a := by
      apply Finset.sum_congr rfl
      intro a ha
      have haLo : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have haHi : a ≤ (R - 1) / Q := (Finset.mem_Icc.mp ha).2
      have hqLo : Q ≤ (R - 1) / a := by
        have hmul : a * Q ≤ R - 1 :=
          (Nat.le_div_iff_mul_le hQ).1 haHi
        exact (Nat.le_div_iff_mul_le (by omega : 0 < a)).2
          (by simpa [Nat.mul_comm] using hmul)
      have hqHi : (R - 1) / a ≤ R - 1 :=
        Nat.div_le_self _ _
      have hmem : (R - 1) / a ∈ T :=
        Finset.mem_Icc.mpr ⟨hqLo, hqHi⟩
      simp [T, hmem]

/-- The named original-source singleton-tail collapse.
All high-q endpoint carriers become a SHORT genuine Möbius prefix,
with the actual divisor punch and original one-sided floor kernel. -/
theorem eulerEndpoint_tail_singleton_collapse
    (R Q b : ℕ) (_hR : 2 ≤ R) (hQ : 0 < Q)
    (hQN : Q ≤ R - 1) (hlarge : R - 1 ≤ Q * (Q + 1)) :
    (∑ q ∈ Finset.Icc Q (R - 1),
      (∑ a ∈ (eulerBucketIndices R q).filter
        (fun a => ¬ a ∣ R - 1), eulerMuQ a) *
          eulerRankOneFloorKernelQ R (eulerBucketHigh R q) b) =
      ∑ a ∈ Finset.Icc 1 ((R - 1) / Q),
        if a ∣ R - 1 then 0 else
          eulerMuQ a * eulerRankOneFloorKernelQ R a b := by
  let f : ℕ → ℚ := fun a =>
    if a ∣ R - 1 then 0 else
      eulerMuQ a * eulerRankOneFloorKernelQ R a b
  have hlargeQ (q : ℕ) (hq : q ∈ Finset.Icc Q (R - 1)) :
      R - 1 ≤ q * (q + 1) := by
    have hqLo : Q ≤ q := (Finset.mem_Icc.mp hq).1
    nlinarith
  have hlocal (q : ℕ) (hq : q ∈ Finset.Icc Q (R - 1)) :
      (∑ a ∈ (eulerBucketIndices R q).filter
        (fun a => ¬ a ∣ R - 1), eulerMuQ a) *
        eulerRankOneFloorKernelQ R (eulerBucketHigh R q) b =
      ∑ a ∈ eulerBucketIndices R q, f a := by
    have hqPos : 0 < q := lt_of_lt_of_le hQ (Finset.mem_Icc.mp hq).1
    by_cases hne : eulerBucketLow R q < eulerBucketHigh R q
    · rw [eulerEndpointLargeBucket_eq_singleton R q hqPos
        (hlargeQ q hq) hne]
      rw [Finset.sum_filter]
      by_cases hd : eulerBucketHigh R q ∣ R - 1
      · simp [f, hd]
      · simp [f, hd]
    · have hempty : eulerBucketIndices R q = ∅ := by
        ext a
        simp [eulerBucketIndices, Finset.mem_Ioc]
        omega
      simp [hempty]
  calc
    _ = ∑ q ∈ Finset.Icc Q (R - 1),
          ∑ a ∈ eulerBucketIndices R q, f a := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hlocal q hq
    _ = ∑ a ∈ Finset.Icc 1 ((R - 1) / Q), f a :=
      eulerEndpointTail_buckets_partition R Q hQ hQN f
    _ = ∑ a ∈ Finset.Icc 1 ((R - 1) / Q),
        if a ∣ R - 1 then 0 else
          eulerMuQ a * eulerRankOneFloorKernelQ R a b := rfl


/-- The *strict* jump count has the stronger N/b+1 bound, already
contained in the total-level count bound certified in #1037.
The reciprocal-width lemma is important for geometry but not
required to prove this quantitative count. -/
theorem eulerBucket_jump_count_le
    (R q b : ℕ) (hR : 2 ≤ R) (hq : 0 < q) (hb : 0 < b) :
    eulerBucketLevelCount R q b -
      eulerBucketRightCarry R q b ≤ (R - 1) / b + 1 := by
  exact (Nat.sub_le _ _).trans
    (eulerBucketLevelCount_le_div_add_one R q b hR hq hb)

/-- The originally requested L/b+1 strict jump bound is a direct
corollary of the stronger historical N/b+1 estimate above. -/
theorem eulerBucket_jump_count_le_outer
    (R q b : ℕ) (hR : 2 ≤ R) (hq : 0 < q) (hb : 0 < b) :
    eulerBucketLevelCount R q b -
      eulerBucketRightCarry R q b ≤ (R + 1) / b + 1 := by
  have hc := eulerBucket_jump_count_le R q b hR hq hb
  have hdiv : (R - 1) / b ≤ (R + 1) / b :=
    Nat.div_le_div_right (by omega : R - 1 ≤ R + 1)
  omega

#print axioms eulerBucket_jump_count_le
#print axioms eulerBucket_jump_count_le_outer
#print axioms eulerEndpointCarry_q_one_zero
#print axioms eulerEndpointRight_remainder_eq_mod_q
#print axioms eulerEndpointCarry_le_sharp
#print axioms eulerEndpointLargeBucket_eq_singleton
#print axioms eulerEndpointTail_buckets_partition
#print axioms eulerEndpoint_tail_singleton_collapse

end RHLean.Proof
