import RHLean.Analysis.AlpogeNativeSquareCandidateCapacity
import Mathlib.Data.Nat.Log

/-!
# Centering the complete prime towers before taking an absolute value

The linear Euler term for a finite prime tower uses the same prime as its
physical von Mangoldt coefficients. The stopping error is nonnegative and
at most log N + 2 log p, uniformly in the cutoff.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- The original physical kernel summed once for each positive exponent. -/
def nativePrimeTower (N p a : ℕ) : ℝ :=
  ∑ k ∈ Finset.range a, Λ (p ^ (k + 1)) * nativeSquareCandidateKernel N (p ^ (k + 1))

def nativePrimeTowerRemainder (N p a : ℕ) : ℝ :=
  Real.log (p : ℝ) * ((a : ℝ) + (N : ℝ) / (((p : ℝ) - 1) * (p : ℝ) ^ a))

theorem nativePrimeTower_add_remainder (N p a : ℕ) (hp : p.Prime) :
    nativePrimeTower N p a + nativePrimeTowerRemainder N p a =
      (N : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h0 : (p : ℝ) ≠ 0 := (zero_lt_one.trans hp1).ne'
  have h1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hp1).ne'
  induction a with
  | zero =>
    simp only [nativePrimeTower, Finset.range_zero, Finset.sum_empty, nativePrimeTowerRemainder,
      Nat.cast_zero, pow_zero, mul_one, zero_add]
    ring
  | succ a ih =>
    have hstep : Λ (p ^ (a + 1)) * nativeSquareCandidateKernel N (p ^ (a + 1)) +
        nativePrimeTowerRemainder N p (a + 1) = nativePrimeTowerRemainder N p a := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      simp only [nativeSquareCandidateKernel, nativePrimeTowerRemainder, Nat.cast_pow,
        Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp [h0, h1] <;> ring
    change (∑ k ∈ Finset.range (a + 1), _) + _ = _
    rw [Finset.sum_range_succ, add_assoc, hstep]
    exact ih

/-- Stopping at the actual last power incurs a logarithmic error per prime. -/
theorem nativePrimeTowerRemainder_bounds (N p : ℕ) (hp : p.Prime) (hN : N ≠ 0) :
    0 ≤ nativePrimeTowerRemainder N p (Nat.log p N) ∧
    nativePrimeTowerRemainder N p (Nat.log p N) ≤ Real.log (N : ℝ) + 2 * Real.log (p : ℝ) := by
  let a := Nat.log p N
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p : ℝ) := by linarith
  have hsub : 0 < (p : ℝ) - 1 := by linarith
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hpN : (p : ℝ) ^ a ≤ N := by exact_mod_cast Nat.pow_log_le_self p hN
  have hfloor := Real.log_le_log (pow_pos hp0 a) hpN
  rw [Real.log_pow] at hfloor
  have hnext : (N : ℝ) < (p : ℝ) ^ (a + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self hp.one_lt N
  rw [pow_succ] at hnext
  have hrat : (N : ℝ) / (((p : ℝ) - 1) * (p : ℝ) ^ a) ≤ 2 := by
    apply (div_le_iff₀ (mul_pos hsub (pow_pos hp0 a))).2
    nlinarith [mul_nonneg (show 0 ≤ (p : ℝ) - 2 by linarith) (pow_pos hp0 a).le]
  change 0 ≤ Real.log (p : ℝ) * ((a : ℝ) + _) ∧
    Real.log (p : ℝ) * ((a : ℝ) + _) ≤ _
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hrat hlog]

/-- The low-prime Euler credit and its stopping loss use identical towers. -/
theorem nativePrimeTower_finite_payment (N z : ℕ) (hN : N ≠ 0) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ z) :
    let credit := ∑ p ∈ S, (N : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1)
    let actual := ∑ p ∈ S, nativePrimeTower N p (Nat.log p N)
    0 ≤ credit - actual ∧ credit - actual ≤ S.card * (Real.log N + 2 * Real.log z) := by
  dsimp only
  have heq : (∑ p ∈ S, (N : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1)) -
      (∑ p ∈ S, nativePrimeTower N p (Nat.log p N)) =
      ∑ p ∈ S, nativePrimeTowerRemainder N p (Nat.log p N) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    linarith [nativePrimeTower_add_remainder N p (Nat.log p N) (hS p hp).1]
  rw [heq]
  constructor
  · exact Finset.sum_nonneg fun p hp => (nativePrimeTowerRemainder_bounds N p (hS p hp).1 hN).1
  · calc
      _ ≤ ∑ _p ∈ S, (Real.log (N : ℝ) + 2 * Real.log (z : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hprime, hle⟩ := hS p hp
        have hl := Real.log_le_log (by exact_mod_cast hprime.pos : 0 < (p : ℝ))
          (by exact_mod_cast hle : (p : ℝ) ≤ z)
        linarith [(nativePrimeTowerRemainder_bounds N p hprime hN).2]
      _ = _ := by simp

end RHLean.Analysis

end
