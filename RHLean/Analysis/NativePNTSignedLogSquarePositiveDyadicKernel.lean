import Mathlib
import RHLean.Analysis.NativePNTSignedLogSquarePrimeCells
import RHLean.Arithmetic.MoebiusDoubling

/-!
# Positive dyadic kernel inside the signed second Selberg transform

The raw identity `Lambda_2 = mu * log^2` is split by parity of the Mobius
cofactor.  The odd-cofactor part is retained as one kernel `K`.  Every even
cofactor is either twice an odd cofactor, where Mobius changes sign, or twice
an even cofactor, where the Mobius value is zero.  Consequently

`Lambda_2(d) = K(d)` for odd `d`,

`Lambda_2(d) = K(d) - K(d/2)` for positive even `d`.

Since `Lambda_2` is nonnegative, this recurrence also proves `K(d) >= 0` for
every `d`.  Thus the dyadic cross-endpoint cells arise inside the actual
second-Selberg coefficient, not from an auxiliary scalar good-mass hypothesis.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Odd-Mobius part of the log-square coefficient at product `d`. -/
def nativePNTLambdaTwoOddMobiusKernel (d : ℕ) : ℝ :=
  ∑ m ∈ d.divisors,
    if Odd m then
      (μ : ArithmeticFunction ℝ) m * (Real.log ((d / m : ℕ) : ℝ)) ^ 2
    else 0

/-- Complementary even-Mobius part of the same divisor fibre. -/
def nativePNTLambdaTwoEvenMobiusPart (d : ℕ) : ℝ :=
  ∑ m ∈ d.divisors,
    if Even m then
      (μ : ArithmeticFunction ℝ) m * (Real.log ((d / m : ℕ) : ℝ)) ^ 2
    else 0

private theorem nativePNT_dvd_odd_is_odd
    {m d : ℕ} (hmd : m ∣ d) (hd : Odd d) : Odd m := by
  by_contra hm
  have hmeven : Even m := Nat.not_odd_iff_even.mp hm
  have hdEven : Even d := by
    rcases hmd with ⟨t, rfl⟩
    rcases hmeven with ⟨a, ha⟩
    refine ⟨a * t, ?_⟩
    rw [ha]
    ring
  exact (Nat.not_even_iff_odd.mpr hd) hdEven

private theorem nativePNTMobiusReal_two_mul (m : ℕ) :
    (μ : ArithmeticFunction ℝ) (2 * m) =
      if Odd m then -(μ : ArithmeticFunction ℝ) m else 0 := by
  by_cases hm : Odd m
  · rw [if_pos hm]
    change (((μ (2 * m) : ℤ) : ℝ)) = -(((μ m : ℤ) : ℝ))
    rw [moebius_two_mul_of_odd m hm]
    push_cast
    rfl
  · rw [if_neg hm]
    have heven : Even m := Nat.not_odd_iff_even.mp hm
    have hzero : μ (2 * m) = 0 := by
      apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      intro hsq
      have hnot := (Nat.squarefree_iff_prime_squarefree.mp hsq) 2 Nat.prime_two
      apply hnot
      rcases heven with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk]
      ring
    change (((μ (2 * m) : ℤ) : ℝ)) = 0
    rw [hzero]
    simp

/-- The full Mobius log-square coefficient splits exactly by cofactor parity. -/
theorem nativeMobiusLogSquareDivisorFiber_eq_oddKernel_add_evenPart
    (d : ℕ) :
    nativeMobiusLogSquareDivisorFiber d =
      nativePNTLambdaTwoOddMobiusKernel d +
        nativePNTLambdaTwoEvenMobiusPart d := by
  unfold nativeMobiusLogSquareDivisorFiber
    nativePNTLambdaTwoOddMobiusKernel nativePNTLambdaTwoEvenMobiusPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hodd : Odd m
  · have hnotEven : ¬Even m := Nat.not_even_iff_odd.mpr hodd
    simp [hodd, hnotEven]
  · have heven : Even m := Nat.not_odd_iff_even.mp hodd
    simp [hodd, heven]

/-- On an odd product every divisor is odd, so the positive dyadic kernel is
literally `Lambda_2`. -/
theorem nativePNTLambdaTwoOddMobiusKernel_eq_lambdaTwo_of_odd
    (d : ℕ) (hd : Odd d) :
    nativePNTLambdaTwoOddMobiusKernel d = nativeLambdaTwo d := by
  rw [← nativeMobiusLogSquareDivisorFiber_eq_lambdaTwo d]
  unfold nativePNTLambdaTwoOddMobiusKernel nativeMobiusLogSquareDivisorFiber
  apply Finset.sum_congr rfl
  intro m hm
  have hmd : m ∣ d := (Nat.mem_divisors.mp hm).1
  have hodd := nativePNT_dvd_odd_is_odd hmd hd
  simp [hodd]

/-- The even cofactor contribution at a positive even product is exactly the
negative odd kernel at half the product. -/
theorem nativePNTLambdaTwoEvenMobiusPart_eq_neg_half
    (d : ℕ) (hdpos : 0 < d) (hdeven : Even d) :
    nativePNTLambdaTwoEvenMobiusPart d =
      -nativePNTLambdaTwoOddMobiusKernel (d / 2) := by
  classical
  have hdne : d ≠ 0 := Nat.ne_of_gt hdpos
  have hdouble : 2 * (d / 2) = d := Nat.two_mul_div_two_of_even hdeven
  have hdgt : 1 < d := Nat.one_lt_of_ne_zero_of_even hdne hdeven
  have hhalfpos : 0 < d / 2 := by omega
  unfold nativePNTLambdaTwoEvenMobiusPart nativePNTLambdaTwoOddMobiusKernel
  conv_lhs => rw [← Finset.sum_filter]
  rw [← Finset.sum_neg_distrib]
  symm
  refine Finset.sum_bij (fun r _ => 2 * r) ?_ ?_ ?_ ?_
  · intro r hr
    have hrd : r ∣ d / 2 := (Nat.mem_divisors.mp hr).1
    have h2rd : 2 * r ∣ d := by
      rcases hrd with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [← hdouble, ht]
      ring
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨h2rd, hdne⟩, even_two_mul r⟩
  · intro r₁ _hr₁ r₂ _hr₂ h
    change 2 * r₁ = 2 * r₂ at h
    omega
  · intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmdMem, hmeven⟩
    have hmd : m ∣ d := (Nat.mem_divisors.mp hmdMem).1
    let r : ℕ := m / 2
    have hmrep : 2 * r = m := by
      dsimp [r]
      exact Nat.two_mul_div_two_of_even hmeven
    have hrd : r ∣ d / 2 := by
      rcases hmd with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      have hEq : 2 * (d / 2) = 2 * (r * t) := by
        rw [hdouble, ht, ← hmrep]
        ring
      omega
    refine ⟨r, Nat.mem_divisors.mpr ⟨hrd, Nat.ne_of_gt hhalfpos⟩, hmrep⟩
  · intro r _hr
    have hmu := nativePNTMobiusReal_two_mul r
    by_cases hodd : Odd r
    · rw [if_pos hodd] at hmu
      simp [hodd, hmu, Nat.div_div_eq_div_mul, Nat.mul_comm]
    · rw [if_neg hodd] at hmu
      simp [hodd, hmu]

/-- Positive-even coefficient recurrence. -/
theorem nativeLambdaTwo_eq_oddKernel_sub_half_of_even
    (d : ℕ) (hdpos : 0 < d) (hdeven : Even d) :
    nativeLambdaTwo d =
      nativePNTLambdaTwoOddMobiusKernel d -
        nativePNTLambdaTwoOddMobiusKernel (d / 2) := by
  rw [← nativeMobiusLogSquareDivisorFiber_eq_lambdaTwo]
  rw [nativeMobiusLogSquareDivisorFiber_eq_oddKernel_add_evenPart,
    nativePNTLambdaTwoEvenMobiusPart_eq_neg_half d hdpos hdeven]
  ring

/-- **Positive dyadic kernel.**  The odd-Mobius log-square kernel is
nonnegative at every product. -/
theorem nativePNTLambdaTwoOddMobiusKernel_nonneg (d : ℕ) :
    0 ≤ nativePNTLambdaTwoOddMobiusKernel d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hd0 : d = 0
      · subst d
        simp [nativePNTLambdaTwoOddMobiusKernel]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        by_cases hodd : Odd d
        · rw [nativePNTLambdaTwoOddMobiusKernel_eq_lambdaTwo_of_odd d hodd]
          exact nativeLambdaTwo_nonneg d (by omega)
        · have heven : Even d := Nat.not_odd_iff_even.mp hodd
          have hhalfLt : d / 2 < d := Nat.div_lt_self hdpos (by norm_num)
          have hhalf0 := ih (d / 2) hhalfLt
          have hrec := nativeLambdaTwo_eq_oddKernel_sub_half_of_even
            d hdpos heven
          have hlam0 := nativeLambdaTwo_nonneg d (by omega)
          linarith

end RHLean.Analysis
