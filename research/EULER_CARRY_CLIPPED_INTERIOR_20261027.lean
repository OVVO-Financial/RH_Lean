import Mathlib
import «research.EULER_CARRY_LEVELSET_MERTENS_20261027»

/-!
# Exact clipped and strict-interior decomposition of Euler carry levels

This file consumes the genuine historical Möbius level-set theorem from
#1037. It proves the full-bucket clipping threshold, strict interior jump
thresholds, an integer form of the universal reciprocal-bucket width, and
singleton sparsity above the square-root quotient threshold.

No finite-C or fixed-eta covariance bound is assumed or claimed.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The smallest carry inside a nonempty bucket is at its right endpoint. -/
def eulerBucketRightCarry (R q b : ℕ) : ℕ :=
  eulerBucketCarry R q b (eulerBucketHigh R q)

/-- The genuine right endpoint belongs to every nonempty quotient bucket. -/
theorem eulerBucketRight_mem (R q : ℕ)
    (hne : eulerBucketLow R q < eulerBucketHigh R q) :
    eulerBucketHigh R q ∈ eulerBucketIndices R q := by
  exact Finset.mem_Ioc.mpr ⟨hne, le_refl _⟩

/-- The minimum endpoint carry is below the nonempty-bucket maximum. -/
theorem eulerBucketRightCarry_le_levelCount (R q b : ℕ)
    (hne : eulerBucketLow R q < eulerBucketHigh R q) :
    eulerBucketRightCarry R q b ≤ eulerBucketLevelCount R q b := by
  exact eulerBucketCarry_le_levelCount R q b _
    (eulerBucketRight_mem R q hne)

/-- Every clipped level covers the entire real quotient bucket. -/
theorem eulerBucketJumpEnd_ge_right_of_clipped
    (R q b k : ℕ)
    (hne : eulerBucketLow R q < eulerBucketHigh R q)
    (hk : k ∈ Finset.Icc 1 (eulerBucketRightCarry R q b)) :
    eulerBucketHigh R q ≤ eulerBucketJumpEnd R q b k := by
  have hrpos : 0 < eulerBucketHigh R q := by omega
  have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
  have hkbound : k ≤ eulerBucketRightCarry R q b := (Finset.mem_Icc.mp hk).2
  exact (eulerBucketCarry_ge_iff_le_jumpEnd R q b
    (eulerBucketHigh R q) k hrpos hkpos).mp hkbound

/-- Every strict-interior level ends below the original right endpoint. -/
theorem eulerBucketJumpEnd_lt_right_of_strict
    (R q b k : ℕ)
    (hne : eulerBucketLow R q < eulerBucketHigh R q)
    (hk : k ∈ Finset.Ioc (eulerBucketRightCarry R q b)
      (eulerBucketLevelCount R q b)) :
    eulerBucketJumpEnd R q b k < eulerBucketHigh R q := by
  have hrpos : 0 < eulerBucketHigh R q := by omega
  have hkpos : 0 < k := by
    have h := (Finset.mem_Ioc.mp hk).1
    omega
  have hnot : ¬ k ≤ eulerBucketRightCarry R q b := by
    have h := (Finset.mem_Ioc.mp hk).1
    omega
  have hequiv := eulerBucketCarry_ge_iff_le_jumpEnd R q b
    (eulerBucketHigh R q) k hrpos hkpos
  by_contra hlt
  have hle : eulerBucketHigh R q ≤ eulerBucketJumpEnd R q b k := by omega
  exact hnot (hequiv.mpr hle)

/-- Strict interior levels also start AFTER the bucket's lower endpoint;
no clipping or external Mertens argument survives. -/
theorem eulerBucketJumpEnd_gt_low_of_strict
    (R q b k : ℕ)
    (hne : eulerBucketLow R q < eulerBucketHigh R q)
    (hk : k ∈ Finset.Ioc (eulerBucketRightCarry R q b)
      (eulerBucketLevelCount R q b)) :
    eulerBucketLow R q < eulerBucketJumpEnd R q b k := by
  have hkpos : 0 < k := by
    have h := (Finset.mem_Ioc.mp hk).1
    omega
  have hK : k ≤ eulerBucketLevelCount R q b := (Finset.mem_Ioc.mp hk).2
  have hc : k ≤ eulerBucketCarry R q b (eulerBucketLow R q + 1) := by
    simpa [eulerBucketLevelCount, hne] using hK
  have hend :=
    (eulerBucketCarry_ge_iff_le_jumpEnd R q b
      (eulerBucketLow R q + 1) k (Nat.succ_pos _) hkpos).mp hc
  omega

/-- The reciprocal-width saving has a completely integer formulation:
 N*(r-l-1)<r*(l+1) rewritten without subtraction. -/
theorem eulerBucket_reciprocal_width_integer
    (R q : ℕ) (hq : 0 < q)
    (hne : eulerBucketLow R q < eulerBucketHigh R q) :
    (R - 1) * eulerBucketHigh R q <
      ((R - 1) + eulerBucketHigh R q) *
        (eulerBucketLow R q + 1) := by
  let N := R - 1
  let lo := eulerBucketLow R q
  let hi := eulerBucketHigh R q
  have hhi : 0 < hi := by dsimp [hi] at *; omega
  have hmul : q * hi ≤ N := by
    have hle : hi ≤ N / q := by rfl
    have hdiv := (Nat.le_div_iff_mul_le hq).1 hle
    simpa [Nat.mul_comm] using hdiv
  have hless : N < (lo + 1) * (q + 1) := by
    have hlt : N / (q + 1) < lo + 1 := by
      dsimp [lo, eulerBucketLow, N]
      omega
    exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos q)).1 hlt
  change N * hi < (N + hi) * (lo + 1)
  calc
    N * hi < ((lo + 1) * (q + 1)) * hi :=
      Nat.mul_lt_mul_of_pos_right hless hhi
    _ = (q * hi) * (lo + 1) + hi * (lo + 1) := by ring
    _ ≤ N * (lo + 1) + hi * (lo + 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right (lo + 1) hmul) _
    _ = (N + hi) * (lo + 1) := by ring

/-- Once q(q+1)>=N, the quotient bucket contains at most ONE integer. -/
theorem eulerBucketHigh_le_low_add_one_of_large_q
    (R q : ℕ) (hq : 0 < q)
    (hlarge : R - 1 ≤ q * (q + 1)) :
    eulerBucketHigh R q ≤ eulerBucketLow R q + 1 := by
  let N := R - 1
  let lo := eulerBucketLow R q
  let hi := eulerBucketHigh R q
  have hmul : q * hi ≤ N := by
    have hle : hi ≤ N / q := by rfl
    have hdiv := (Nat.le_div_iff_mul_le hq).1 hle
    simpa [Nat.mul_comm] using hdiv
  have hless : N < (lo + 1) * (q + 1) := by
    have hlt : N / (q + 1) < lo + 1 := by
      dsimp [lo, eulerBucketLow, N]
      omega
    exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos q)).1 hlt
  change hi ≤ lo + 1
  by_contra hbad
  have hgap : lo + 2 ≤ hi := by omega
  have hmulGap : q * (lo + 2) ≤ q * hi :=
    Nat.mul_le_mul_left q hgap
  have hqlo : q < lo + 1 := by
    have hv : q * (lo + 2) < (lo + 1) * (q + 1) :=
      lt_of_le_of_lt (hmulGap.trans hmul) hless
    nlinarith
  have hhiBound : hi ≤ q + 1 := by
    by_contra hbad'
    have hgap2 : q + 2 ≤ hi := by omega
    have hmult : q * (q + 2) ≤ q * hi :=
      Nat.mul_le_mul_left q hgap2
    nlinarith [hlarge, hmul, hmult]
  omega

/-- A nonempty large-q bucket is a SINGLETON; its full carry is an
endpoint carry and has no strict interior level. -/
theorem eulerBucketLevelCount_eq_rightCarry_of_large_q
    (R q b : ℕ) (hq : 0 < q)
    (hlarge : R - 1 ≤ q * (q + 1))
    (hne : eulerBucketLow R q < eulerBucketHigh R q) :
    eulerBucketLevelCount R q b = eulerBucketRightCarry R q b := by
  have hbound :=
    eulerBucketHigh_le_low_add_one_of_large_q R q hq hlarge
  have heq :
      eulerBucketHigh R q = eulerBucketLow R q + 1 := by omega
  simp [eulerBucketLevelCount, eulerBucketRightCarry, heq]

/-- There are NO strict interior jump indices above the square-root
quotient threshold, though the singleton endpoint phase still survives. -/
theorem eulerBucket_strict_levels_empty_of_large_q
    (R q b : ℕ) (hq : 0 < q)
    (hlarge : R - 1 ≤ q * (q + 1))
    (hne : eulerBucketLow R q < eulerBucketHigh R q) :
    Finset.Ioc (eulerBucketRightCarry R q b)
      (eulerBucketLevelCount R q b) = ∅ := by
  rw [eulerBucketLevelCount_eq_rightCarry_of_large_q R q b hq hlarge hne]
  simp

/-- If q divides the historical endpoint, the complete clipped endpoint
carry is zero: true source-specific arithmetic, not a generic kernel bound. -/
theorem eulerBucketRightCarry_zero_of_q_dvd
    (R q b : ℕ) (hR : 2 ≤ R) (hq : 0 < q)
    (hne : eulerBucketLow R q < eulerBucketHigh R q)
    (hd : q ∣ R - 1) :
    eulerBucketRightCarry R q b = 0 := by
  have hmod : (R - 1) % q = 0 := Nat.mod_eq_zero_of_dvd hd
  have hEq : q * ((R - 1) / q) = R - 1 := by
    have h := Nat.div_add_mod (R - 1) q
    rw [hmod, add_zero] at h
    exact h
  have hdiv : eulerBucketHigh R q ∣ R - 1 := by
    refine ⟨q, ?_⟩
    dsimp [eulerBucketHigh]
    simpa [Nat.mul_comm] using hEq.symm
  exact eulerBucketCarry_zero_on_divisor_member
    R q b (eulerBucketHigh R q) hR hq
    (eulerBucketRight_mem R q hne) hdiv


/-- The complete genuine signed Mertens staircase splits into a full-bucket
endpoint amplitude and a residual strict-interior staircase. It is crucial
that the true *signed* bucket increment is not absolutized. -/
theorem eulerBucketCarry_sum_eq_endpoint_add_strict
    (R q b : ℕ)
    (hne : eulerBucketLow R q < eulerBucketHigh R q) :
    (∑ a ∈ eulerBucketIndices R q,
        (μ a : ℤ) * (eulerBucketCarry R q b a : ℤ)) =
      (eulerBucketRightCarry R q b : ℤ) *
        (mertensSummatoryInt (eulerBucketHigh R q) -
          mertensSummatoryInt (eulerBucketLow R q)) +
      ∑ k ∈ Finset.Ioc (eulerBucketRightCarry R q b)
        (eulerBucketLevelCount R q b),
          (mertensSummatoryInt (eulerBucketJumpEnd R q b k) -
            mertensSummatoryInt (eulerBucketLow R q)) := by
  let c := eulerBucketRightCarry R q b
  let K := eulerBucketLevelCount R q b
  let lo := eulerBucketLow R q
  let hi := eulerBucketHigh R q
  let f : ℕ → ℤ := fun k =>
    mertensSummatoryInt (min hi (eulerBucketJumpEnd R q b k)) -
      mertensSummatoryInt lo
  have hck : c ≤ K :=
    eulerBucketRightCarry_le_levelCount R q b hne
  have hzero (n : ℕ) :
      Finset.Ioc 0 n = Finset.Icc 1 n := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hsplit :
      (∑ k ∈ Finset.Icc 1 K, f k) =
        (∑ k ∈ Finset.Icc 1 c, f k) +
          ∑ k ∈ Finset.Ioc c K, f k := by
    have hs := Finset.sum_Ioc_consecutive (f := f)
      (Nat.zero_le c) hck
    rw [hzero c, hzero K] at hs
    omega
  have hfull :
      (∑ k ∈ Finset.Icc 1 c, f k) =
        (c : ℤ) * (mertensSummatoryInt hi - mertensSummatoryInt lo) := by
    calc
      _ = ∑ k ∈ Finset.Icc 1 c,
            (mertensSummatoryInt hi - mertensSummatoryInt lo) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hge := eulerBucketJumpEnd_ge_right_of_clipped
                R q b k hne hk
              dsimp [f, hi, lo]
              rw [min_eq_left hge]
      _ = (c : ℤ) *
            (mertensSummatoryInt hi - mertensSummatoryInt lo) := by
              simp
              ring
  have hstrict :
      (∑ k ∈ Finset.Ioc c K, f k) =
        ∑ k ∈ Finset.Ioc c K,
          (mertensSummatoryInt (eulerBucketJumpEnd R q b k) -
            mertensSummatoryInt lo) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hlt := eulerBucketJumpEnd_lt_right_of_strict
      R q b k hne hk
    dsimp [f, hi]
    rw [min_eq_right (le_of_lt hlt)]
  calc
    _ = ∑ k ∈ Finset.Icc 1 K, f k := by
      simpa [f, K, hi, lo] using
        eulerBucketCarry_sum_eq_historicalMertens R q b
    _ = (∑ k ∈ Finset.Icc 1 c, f k) +
          ∑ k ∈ Finset.Ioc c K, f k := hsplit
    _ = (c : ℤ) *
          (mertensSummatoryInt hi - mertensSummatoryInt lo) +
        ∑ k ∈ Finset.Ioc c K,
          (mertensSummatoryInt (eulerBucketJumpEnd R q b k) -
            mertensSummatoryInt lo) := by rw [hfull, hstrict]

/-- A strict interior carry jump is possible only in a genuinely large
historical quotient bucket: q(q+1)<R-1. The singleton endpoint channels
are deliberately NOT discarded. -/
theorem eulerBucket_strict_level_implies_small_q
    (R q b k : ℕ) (hq : 0 < q)
    (hne : eulerBucketLow R q < eulerBucketHigh R q)
    (hk : k ∈ Finset.Ioc (eulerBucketRightCarry R q b)
      (eulerBucketLevelCount R q b)) :
    q * (q + 1) < R - 1 := by
  by_contra hbad
  have hlarge : R - 1 ≤ q * (q + 1) := by omega
  have hnone := eulerBucket_strict_levels_empty_of_large_q
    R q b hq hlarge hne
  rw [hnone] at hk
  simp at hk

#print axioms eulerBucketJumpEnd_ge_right_of_clipped
#print axioms eulerBucketJumpEnd_lt_right_of_strict
#print axioms eulerBucketJumpEnd_gt_low_of_strict
#print axioms eulerBucket_reciprocal_width_integer
#print axioms eulerBucketHigh_le_low_add_one_of_large_q
#print axioms eulerBucket_strict_levels_empty_of_large_q
#print axioms eulerBucketRightCarry_zero_of_q_dvd
#print axioms eulerBucketCarry_sum_eq_endpoint_add_strict
#print axioms eulerBucket_strict_level_implies_small_q

end RHLean.Proof
