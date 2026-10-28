import Mathlib
import «research.EULER_RANK_ONE_FRACTIONAL_ROWS_20261027»

/-!
# Quotient-bucket historical carry staircase

On X = R^2-1, N=R-1, L=R+1:
  I_q = (floor(N/(q+1)), floor(N/q)]
  c_(q,b)(a) = floor(floor(X/b)/a) - floor(L*q/b).

The complete carry is a monotone integer staircase. Its kth level is
a <= floor(floor(X/b)/(floor(L*q/b)+k)), with no post-root argument.

The carry VANISHES on divisor rows a|N. No signed cancellation or finite-C
hypothesis is assumed in these structural theorems.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- Historical quotient-bucket lower endpoint. -/
def eulerBucketLow (R q : ℕ) : ℕ := (R - 1) / (q + 1)

/-- Historical quotient-bucket upper endpoint. -/
def eulerBucketHigh (R q : ℕ) : ℕ := (R - 1) / q

/-- All genuine historical a with the fixed reciprocal quotient q. -/
def eulerBucketIndices (R q : ℕ) : Finset ℕ :=
  Finset.Ioc (eulerBucketLow R q) (eulerBucketHigh R q)

/-- Upper hyperbola quotient, computed once for each b. -/
def eulerBucketY (R b : ℕ) : ℕ := squareRootEndpoint R / b

/-- The phase's integer quotient, constant across the entire a-bucket. -/
def eulerBucketPhaseQuot (R q b : ℕ) : ℕ := (R + 1) * q / b

/-- Genuine nonnegative carry, before combining with the modular residue. -/
def eulerBucketCarry (R q b a : ℕ) : ℕ :=
  eulerBucketY R b / a - eulerBucketPhaseQuot R q b

/-- The exact kth integer jump threshold. -/
def eulerBucketJumpEnd (R q b k : ℕ) : ℕ :=
  eulerBucketY R b / (eulerBucketPhaseQuot R q b + k)

/-- Every a in the original interval I_q has its exact quotient q. -/
theorem eulerBucketIndices_quotient (R q a : ℕ) (hq : 0 < q)
    (ha : a ∈ eulerBucketIndices R q) :
    (R - 1) / a = q := by
  have hlo : (R - 1) / (q + 1) < a :=
    (Finset.mem_Ioc.mp ha).1
  have hhi : a ≤ (R - 1) / q :=
    (Finset.mem_Ioc.mp ha).2
  have hloNonneg : 0 ≤ (R - 1) / (q + 1) := Nat.zero_le _
  have ha0 : 0 < a := by omega
  have hqle : q ≤ (R - 1) / a := by
    apply (Nat.le_div_iff_mul_le ha0).2
    have hmul := (Nat.le_div_iff_mul_le hq).1 hhi
    simpa [Nat.mul_comm] using hmul
  have hlt : (R - 1) / a < q + 1 := by
    apply (Nat.div_lt_iff_lt_mul ha0).2
    have hraw := (Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1)).1 hlo
    simpa [Nat.mul_comm] using hraw
  omega

/-- Carry is pointwise non-increasing along each historical a-bucket. -/
theorem eulerBucketCarry_antitone
    (R q b a a' : ℕ) (ha : 0 < a) (haa' : a ≤ a') :
    eulerBucketCarry R q b a' ≤ eulerBucketCarry R q b a := by
  have ha' : 0 < a' := lt_of_lt_of_le ha haa'
  have hmul := Nat.div_mul_le_self (eulerBucketY R b) a'
  have hmul' :
      (eulerBucketY R b / a') * a ≤
        (eulerBucketY R b / a') * a' := Nat.mul_le_mul_left _ haa'
  have hdiv :
      eulerBucketY R b / a' ≤ eulerBucketY R b / a :=
    (Nat.le_div_iff_mul_le ha).2 (hmul'.trans hmul)
  unfold eulerBucketCarry
  omega

/-- An integer carry reaches level k iff the historical index stays below
the corresponding exact, clipped quotient endpoint. -/
theorem eulerBucketCarry_ge_iff_le_jumpEnd
    (R q b a k : ℕ) (ha : 0 < a) (hk : 0 < k) :
    k ≤ eulerBucketCarry R q b a ↔
      a ≤ eulerBucketJumpEnd R q b k := by
  let Y := eulerBucketY R b
  let m := eulerBucketPhaseQuot R q b
  have hmk : 0 < m + k := by omega
  change k ≤ Y / a - m ↔ a ≤ Y / (m + k)
  constructor
  · intro h
    have hquot : m + k ≤ Y / a := by omega
    have hmul := (Nat.le_div_iff_mul_le ha).1 hquot
    apply (Nat.le_div_iff_mul_le hmk).2
    simpa [Nat.mul_comm] using hmul
  · intro h
    have hmul := (Nat.le_div_iff_mul_le hmk).1 h
    have hquot : m + k ≤ Y / a :=
      (Nat.le_div_iff_mul_le ha).2 (by simpa [Nat.mul_comm] using hmul)
    omega

/-- For divisor rows, the FULL original carry vanishes: no terms must be
excised from the signed carry sum when passing to complete buckets. -/
theorem eulerBucketCarry_zero_of_dvd
    (R q b a : ℕ) (hR : 2 ≤ R) (ha : 0 < a)
    (hadiv : a ∣ R - 1) (hq : (R - 1) / a = q) :
    eulerBucketCarry R q b a = 0 := by
  have hmod : (R - 1) % a = 0 := Nat.mod_eq_zero_of_dvd hadiv
  have hdivmod := Nat.div_add_mod (R - 1) a
  rw [hq, hmod, add_zero] at hdivmod
  have hN : R - 1 = a * q := hdivmod.symm
  have hX : squareRootEndpoint R = a * ((R + 1) * q) := by
    rw [eulerRootEndpoint_factor R hR, hN]
    ring
  have hfloor :
      squareRootEndpoint R / (a * b) = ((R + 1) * q) / b := by
    rw [hX]
    exact Nat.mul_div_mul_left (m := a) ((R + 1) * q) b ha
  have hnested :
      eulerBucketY R b / a = squareRootEndpoint R / (a * b) := by
    unfold eulerBucketY
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  unfold eulerBucketCarry eulerBucketPhaseQuot
  rw [hnested, hfloor]
  omega

/-- The preceding vanishing holds for EVERY divisor row in the
corresponding actual quotient bucket. -/
theorem eulerBucketCarry_zero_on_divisor_member
    (R q b a : ℕ) (hR : 2 ≤ R) (hq : 0 < q)
    (ha : a ∈ eulerBucketIndices R q) (hadiv : a ∣ R - 1) :
    eulerBucketCarry R q b a = 0 := by
  have ha0 : 0 < a := by
    have h := (Finset.mem_Ioc.mp ha).1
    unfold eulerBucketLow at h
    have hz : 0 ≤ (R - 1) / (q + 1) := Nat.zero_le _
    omega
  exact eulerBucketCarry_zero_of_dvd R q b a hR ha0 hadiv
    (eulerBucketIndices_quotient R q a hq ha)

#print axioms eulerBucketIndices_quotient
#print axioms eulerBucketCarry_antitone
#print axioms eulerBucketCarry_ge_iff_le_jumpEnd
#print axioms eulerBucketCarry_zero_on_divisor_member

end RHLean.Proof
