import Mathlib
import RHLean.Arithmetic.PrimeWheelFiniteSystem

open scoped BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- Prefix sum over the natural interval `0, ..., x`. -/
def natPrefix (f : ℕ → ℤ) (x : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (x + 1), f n

/-- Prefix sum over the positive interval `1, ..., x`, written in a form that
is convenient for exact reindexing through `Finset.range`. -/
def positivePrefix (f : ℕ → ℤ) (x : ℕ) : ℤ :=
  natPrefix f x - f 0

/-- Multiplicative finite difference at the prime scale `p`. -/
def primeMultDiff (p : ℕ) (F : ℕ → ℤ) (x : ℕ) : ℤ :=
  F x - F (x / p)

/-- Integer-valued divisibility indicator. -/
def divisibilityIndicator (d n : ℕ) : ℤ :=
  if d ∣ n then 1 else 0

/-- The square-sensitive local prime comb is exactly the second finite-difference
kernel `1 - 2 1_{p|n} + 1_{p^2|n}`. -/
theorem localPrimeComb_eq_indicator_kernel (p n : ℕ) :
    localPrimeComb p n =
      1 - 2 * divisibilityIndicator p n + divisibilityIndicator (p ^ 2) n := by
  unfold localPrimeComb divisibilityIndicator
  by_cases hsq : p ^ 2 ∣ n
  · have hp : p ∣ n :=
      dvd_trans (dvd_pow_self p (by norm_num)) hsq
    simp [hsq, hp]
  · by_cases hp : p ∣ n <;> simp [hsq, hp]

/-- Reindexing multiples of `p` in a natural prefix.  This is the exact floor
identity behind the multiplicative finite-difference recursion. -/
theorem sum_dvd_div_range (p : ℕ) (f : ℕ → ℤ) :
    ∀ x : ℕ,
      ∑ n ∈ Finset.range (x + 1),
          (if p ∣ n then f (n / p) else 0) =
        ∑ m ∈ Finset.range (x / p + 1), f m := by
  intro x
  induction x with
  | zero => simp [Nat.zero_div]
  | succ x ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hdvd : p ∣ (x + 1)
      · have hdiv : (x + 1) / p = x / p + 1 := by
          rw [Nat.succ_div, if_pos hdvd]
        rw [if_pos hdvd, hdiv, ← Finset.sum_range_succ]
      · have hdiv : (x + 1) / p = x / p := by
          rw [Nat.succ_div, if_neg hdvd, add_zero]
        rw [if_neg hdvd, add_zero, hdiv]

/-- If multiplication by `p` leaves a field unchanged, then the sum over the
`p`-divisible sites of a prefix is exactly the same field at the smaller floor
endpoint. -/
theorem sum_dvd_range_of_mul_invariant
    (p : ℕ) (f : ℕ → ℤ)
    (hinv : ∀ m : ℕ, f (p * m) = f m)
    (x : ℕ) :
    (∑ n ∈ Finset.range (x + 1), if p ∣ n then f n else 0) =
      natPrefix f (x / p) := by
  calc
    (∑ n ∈ Finset.range (x + 1), if p ∣ n then f n else 0) =
        ∑ n ∈ Finset.range (x + 1),
          (if p ∣ n then f (n / p) else 0) := by
            apply Finset.sum_congr rfl
            intro n hn
            by_cases hdvd : p ∣ n
            · have hprod : p * (n / p) = n := Nat.mul_div_cancel' hdvd
              have hfn : f n = f (n / p) := by
                rw [← hprod]
                exact hinv (n / p)
              simp [hdvd, hfn]
            · simp [hdvd]
    _ = ∑ m ∈ Finset.range (x / p + 1), f m :=
      sum_dvd_div_range p f x
    _ = natPrefix f (x / p) := rfl

/-- Multiplicative invariance under `p` automatically gives invariance under
`p^2`. -/
theorem mul_sq_invariant_of_mul_invariant
    (p : ℕ) (f : ℕ → ℤ)
    (hinv : ∀ m : ℕ, f (p * m) = f m) :
    ∀ m : ℕ, f (p ^ 2 * m) = f m := by
  intro m
  have h1 := hinv (p * m)
  have h2 := hinv m
  simpa [pow_two, mul_assoc] using h1.trans h2

/-- Exact raw-comb prefix recurrence at an arbitrary endpoint.  No complete CRT
period is assumed: the two boundary terms are simply the old field evaluated at
`floor(x/p)` and `floor(x/p^2)`. -/
theorem natPrefix_localPrimeComb_mul
    (p : ℕ) (f : ℕ → ℤ)
    (hinv : ∀ m : ℕ, f (p * m) = f m)
    (x : ℕ) :
    natPrefix (fun n => localPrimeComb p n * f n) x =
      natPrefix f x - 2 * natPrefix f (x / p) + natPrefix f (x / p ^ 2) := by
  have hinv2 := mul_sq_invariant_of_mul_invariant p f hinv
  unfold natPrefix
  calc
    (∑ n ∈ Finset.range (x + 1), localPrimeComb p n * f n) =
        ∑ n ∈ Finset.range (x + 1),
          (f n - 2 * (if p ∣ n then f n else 0) +
            (if p ^ 2 ∣ n then f n else 0)) := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [localPrimeComb_eq_indicator_kernel]
              unfold divisibilityIndicator
              by_cases hp : p ∣ n <;>
                by_cases hsq : p ^ 2 ∣ n <;> simp [hp, hsq] <;> ring
    _ =
        (∑ n ∈ Finset.range (x + 1), f n) -
          2 * (∑ n ∈ Finset.range (x + 1), if p ∣ n then f n else 0) +
          (∑ n ∈ Finset.range (x + 1), if p ^ 2 ∣ n then f n else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [← Finset.mul_sum]
    _ =
        (∑ n ∈ Finset.range (x + 1), f n) -
          2 * natPrefix f (x / p) + natPrefix f (x / p ^ 2) := by
            rw [sum_dvd_range_of_mul_invariant p f hinv x]
            rw [sum_dvd_range_of_mul_invariant (p ^ 2) f hinv2 x]
    _ = natPrefix f x - 2 * natPrefix f (x / p) + natPrefix f (x / p ^ 2) := rfl

/-- Positive-prefix form of the same recurrence.  The value at zero cancels
with coefficients `1,-2,1`, while the new local comb itself vanishes at zero. -/
theorem positivePrefix_localPrimeComb_mul
    (p : ℕ) (f : ℕ → ℤ)
    (hinv : ∀ m : ℕ, f (p * m) = f m)
    (x : ℕ) :
    positivePrefix (fun n => localPrimeComb p n * f n) x =
      positivePrefix f x - 2 * positivePrefix f (x / p) +
        positivePrefix f (x / p ^ 2) := by
  unfold positivePrefix
  rw [natPrefix_localPrimeComb_mul p f hinv x]
  have hzero : localPrimeComb p 0 = 0 := by
    simp [localPrimeComb]
  rw [hzero]
  ring

/-- Two successive multiplicative finite differences give the same
`1,-2,1` floor recursion. -/
theorem primeMultDiff_sq_apply
    (p : ℕ) (F : ℕ → ℤ) (x : ℕ) :
    primeMultDiff p (primeMultDiff p F) x =
      F x - 2 * F (x / p) + F (x / p ^ 2) := by
  unfold primeMultDiff
  rw [Nat.div_div_eq_div_mul]
  simp [pow_two]
  ring

/-- Distinct multiplicative finite-difference coordinates commute; in fact the
identity is valid for arbitrary natural dilation parameters. -/
theorem primeMultDiff_comm
    (p q : ℕ) (F : ℕ → ℤ) :
    primeMultDiff p (primeMultDiff q F) =
      primeMultDiff q (primeMultDiff p F) := by
  funext x
  unfold primeMultDiff
  simp only [Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm p q]
  ring

/-- Exact finite-difference form of one local prime-comb prefix step. -/
theorem positivePrefix_localPrimeComb_eq_primeMultDiff_sq
    (p : ℕ) (f : ℕ → ℤ)
    (hinv : ∀ m : ℕ, f (p * m) = f m)
    (x : ℕ) :
    positivePrefix (fun n => localPrimeComb p n * f n) x =
      primeMultDiff p (primeMultDiff p (positivePrefix f)) x := by
  rw [positivePrefix_localPrimeComb_mul p f hinv x]
  rw [primeMultDiff_sq_apply]

/-- Inserting one fresh comb coordinate multiplies the seeded field by exactly
that local prime comb. -/
theorem seededPrimeComb_insert
    (S : Finset ℕ) (p n : ℕ) (hpS : p ∉ S) :
    seededPrimeComb (insert p S) n =
      localPrimeComb p n * seededPrimeComb S n := by
  classical
  simp [seededPrimeComb, hpS]
  ring

/-- Positive prefix of the existing seeded prime-comb field. -/
def seededPrimeCombPrefix (S : Finset ℕ) (x : ℕ) : ℤ :=
  positivePrefix (seededPrimeComb S) x

/-- Once the old seeded field is known to be invariant under multiplication by
a fresh prime `p`, adjoining `p` is exactly the second multiplicative finite
difference of its prefix. -/
theorem seededPrimeCombPrefix_insert_of_mul_invariant
    (S : Finset ℕ) (p x : ℕ) (hpS : p ∉ S)
    (hinv : ∀ m : ℕ, seededPrimeComb S (p * m) = seededPrimeComb S m) :
    seededPrimeCombPrefix (insert p S) x =
      primeMultDiff p (primeMultDiff p (seededPrimeCombPrefix S)) x := by
  unfold seededPrimeCombPrefix
  have hfield :
      seededPrimeComb (insert p S) =
        fun n => localPrimeComb p n * seededPrimeComb S n := by
    funext n
    exact seededPrimeComb_insert S p n hpS
  rw [hfield]
  exact positivePrefix_localPrimeComb_eq_primeMultDiff_sq
    p (seededPrimeComb S) hinv x

/-- The all-minus seed has prefix `-x`, so iterating the exact second-difference
step starts from the elementary identity function. -/
theorem seededPrimeCombPrefix_empty (x : ℕ) :
    seededPrimeCombPrefix ∅ x = -(x : ℤ) := by
  simp [seededPrimeCombPrefix, positivePrefix, natPrefix, seededPrimeComb]

end RHLean.Arithmetic
