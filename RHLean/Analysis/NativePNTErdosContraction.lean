import Mathlib
import RHLean.Analysis.NativePNTErrorMass

/-!
# The generic Erdos cubic contraction

The elementary Selberg--Erdos proof of PNT produces nonnegative linear error
envelopes with a one-sided cubic improvement.  The natural abstract input is
therefore an inequality

`alpha_(n+1) <= alpha_n - C * alpha_n^3`, `C > 0`,

not an exact recurrence.

This module proves, independently of all number theory, that any nonnegative
envelope satisfying that inequality tends to zero.  The nonnegativity
hypothesis is intentionally explicit: together with the cubic improvement it
forces `C * alpha_n^2 <= 1` whenever `alpha_n > 0`, so it encodes the
localization needed to keep the next envelope in the admissible range.
Establishing that localization belongs to the prime-specific application, not
to this generic limit argument.

The final section starts that prime-specific application.  The key elementary
regularity fact is much sharper than a generic Lipschitz estimate: since
`nativePsi` is monotone, a positive error spike can fall forward with slope at
most one, while a negative error spike can rise backward with slope at most
one.  Thus a spike of height `H` forces a one-sided interval of length `H / 2`
on which the absolute error stays at least `H / 2`.  These are the native
``good interval'' persistence lemmas used by the Erdos compensation step.
-/

noncomputable section

open Filter Set
open scoped ArithmeticFunction.vonMangoldt BigOperators Topology

namespace RHLean.Analysis

/-- A nonnegative cubic-improvement envelope has no positive limiting fixed
point: its only possible limit is zero.

The hypothesis is one-sided rather than an equality.  This is the form needed
for Selberg--Erdos applications, where the next envelope is obtained from an
upper bound rather than from an exact recurrence. -/
theorem tendsto_zero_of_cubic_recurrence
    (a : ℕ → ℝ) (C : ℝ)
    (hC : 0 < C)
    (hnonneg : ∀ n, 0 ≤ a n)
    (hrec : ∀ n, a (n + 1) ≤ a n - C * (a n) ^ 3) :
    Tendsto a atTop (𝓝 0) := by
  have hstep : ∀ n, a (n + 1) ≤ a n := by
    intro n
    have hcube : 0 ≤ (a n) ^ 3 := pow_nonneg (hnonneg n) 3
    have hdrop : 0 ≤ C * (a n) ^ 3 := mul_nonneg hC.le hcube
    exact (hrec n).trans (sub_le_self _ hdrop)
  have hanti : Antitone a := antitone_nat_of_succ_le hstep
  have hbdd : BddBelow (Set.range a) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact hnonneg n
  let L : ℝ := ⨅ n, a n
  have hconv : Tendsto a atTop (𝓝 L) := by
    dsimp [L]
    exact tendsto_atTop_ciInf hanti hbdd
  have hLnonneg : 0 ≤ L :=
    ge_of_tendsto' hconv hnonneg
  have hshiftIndex : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    exact Filter.eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hshift : Tendsto (fun n : ℕ => a (n + 1)) atTop (𝓝 L) :=
    hconv.comp hshiftIndex
  have hpoly :
      Tendsto (fun n : ℕ => a n - C * (a n) ^ 3) atTop
        (𝓝 (L - C * L ^ 3)) := by
    exact hconv.sub (tendsto_const_nhds.mul (hconv.pow 3))
  have hdiff :
      Tendsto
        (fun n : ℕ => a (n + 1) - (a n - C * (a n) ^ 3)) atTop
        (𝓝 (L - (L - C * L ^ 3))) := by
    exact hshift.sub hpoly
  have hprod_nonpos : C * L ^ 3 ≤ 0 := by
    have hlim_nonpos : L - (L - C * L ^ 3) ≤ 0 :=
      le_of_tendsto' hdiff fun n => sub_nonpos.mpr (hrec n)
    linarith
  have hprod_nonneg : 0 ≤ C * L ^ 3 :=
    mul_nonneg hC.le (pow_nonneg hLnonneg 3)
  have hprod_zero : C * L ^ 3 = 0 :=
    le_antisymm hprod_nonpos hprod_nonneg
  have hcube : L ^ 3 = 0 :=
    (mul_eq_zero.mp hprod_zero).resolve_left (ne_of_gt hC)
  have hL : L = 0 := by
    exact pow_eq_zero hcube
  simpa [hL] using hconv

/-! ## Signed Selberg recurrence and linear control -/

/-- The summatory Selberg estimate also retains its signed form.  This is the
version that can be iterated once more: the endpoint error plus its
von-Mangoldt transform is `O(N)`, with the same explicit constant as the first
absolute recurrence. -/
theorem nativePNTError_signed_log_sum_abs_le
    (N : ℕ) (hN : 3 ≤ N) :
    |nativePNTError N * Real.log N +
      ∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)| ≤
      (3 * (Real.log 4 + 2) + 173) * (N : ℝ) := by
  have hsel := nativeSelbergPair_sub_two_mul_log_abs_le N hN
  have hfac := nativeLogFactorial_sub_Nlog_abs_le N (by omega)
  have hdecomp := nativePNTError_selberg_decomposition N
  have heq :
      nativePNTError N * Real.log N +
          (∑ d ∈ Finset.Icc 1 N, Λ d * nativePNTError (N / d)) =
        (nativeSelbergPair N - 2 * (N : ℝ) * Real.log N) -
          (Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N) := by
    linarith [hdecomp]
  rw [heq]
  calc
    |(nativeSelbergPair N - 2 * (N : ℝ) * Real.log N) -
        (Real.log ((Nat.factorial N : ℕ) : ℝ) -
          (N : ℝ) * Real.log N)| ≤
        |nativeSelbergPair N - 2 * (N : ℝ) * Real.log N| +
          |Real.log ((Nat.factorial N : ℕ) : ℝ) -
            (N : ℝ) * Real.log N| := abs_sub _ _
    _ ≤ (3 * (Real.log 4 + 2) + 172) * (N : ℝ) + (N : ℝ) :=
      add_le_add hsel hfac
    _ = (3 * (Real.log 4 + 2) + 173) * (N : ℝ) := by ring

/-- A global linear bound for the native PNT error.  It uses only the
architecture-native Chebyshev upper bound and nonnegativity of `psi`. -/
theorem nativePNTError_abs_le_const_mul (N : ℕ) :
    |nativePNTError N| ≤ (Real.log 4 + 3) * (N : ℝ) := by
  have hpsi0 := nativePsi_nonneg N
  have hpsi := nativePsi_le_const_mul N
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold nativePNTError
  rw [abs_le]
  constructor <;> nlinarith

/-! ## Positivity and local mass of the Selberg kernel -/

/-- The Dirichlet self-convolution of von Mangoldt is pointwise nonnegative. -/
theorem nativeLambdaConvolution_nonneg (n : ℕ) :
    0 ≤ (Λ * Λ) n := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_nonneg
  intro ab _hab
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    ArithmeticFunction.vonMangoldt_nonneg

/-- The second von Mangoldt kernel is nonnegative at every positive integer. -/
theorem nativeLambdaTwo_nonneg (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ nativeLambdaTwo n := by
  rw [nativeLambdaTwo_eq_logWeight_vonMangoldt_add_convolution]
  simp only [ArithmeticFunction.add_apply, arithmeticLogWeight_apply]
  exact add_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.log_nonneg (by exact_mod_cast hn)))
    (nativeLambdaConvolution_nonneg n)

/-- The differentiated von Mangoldt term is one nonnegative summand of
`Lambda_2`. -/
theorem nativeLambda_mul_log_le_lambdaTwo (n : ℕ) (hn : 1 ≤ n) :
    Λ n * Real.log (n : ℝ) ≤ nativeLambdaTwo n := by
  rw [nativeLambdaTwo_eq_logWeight_vonMangoldt_add_convolution]
  simp only [ArithmeticFunction.add_apply, arithmeticLogWeight_apply]
  exact le_add_of_nonneg_right (nativeLambdaConvolution_nonneg n)

/-- The summatory second von Mangoldt mass is monotone. -/
theorem nativeLambdaTwoSummatory_monotone : Monotone nativeLambdaTwoSummatory := by
  intro a b hab
  unfold nativeLambdaTwoSummatory
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hna⟩
    exact Finset.mem_Icc.mpr ⟨hn1, hna.trans hab⟩
  · intro n hn _hna
    exact nativeLambdaTwo_nonneg n (Finset.mem_Icc.mp hn).1

/-- On an integer interval, the `psi` increment times the left-end logarithm
is dominated by the corresponding `Lambda_2` mass.  This is the local
regularity input for the Erdos good-interval argument. -/
theorem nativePsi_interval_mul_log_le_lambdaTwo_interval
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (nativePsi b - nativePsi a) * Real.log (a : ℝ) ≤
      nativeLambdaTwoSummatory b - nativeLambdaTwoSummatory a := by
  have hsub : Finset.Icc 1 a ⊆ Finset.Icc 1 b := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hna⟩
    exact Finset.mem_Icc.mpr ⟨hn1, hna.trans hab⟩
  calc
    (nativePsi b - nativePsi a) * Real.log (a : ℝ) =
        (∑ n ∈ Finset.Icc 1 b \ Finset.Icc 1 a, Λ n) *
          Real.log (a : ℝ) := by
      unfold nativePsi
      rw [← Finset.sum_sdiff hsub]
      ring
    _ = ∑ n ∈ Finset.Icc 1 b \ Finset.Icc 1 a,
          Λ n * Real.log (a : ℝ) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ n ∈ Finset.Icc 1 b \ Finset.Icc 1 a,
          nativeLambdaTwo n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnDiff := Finset.mem_sdiff.mp hn
      have hnI := Finset.mem_Icc.mp hnDiff.1
      have hna : a < n := by
        by_contra hnot
        have hna' : n ≤ a := Nat.le_of_not_gt hnot
        exact hnDiff.2 (Finset.mem_Icc.mpr ⟨hnI.1, hna'⟩)
      have hlog : Real.log (a : ℝ) ≤ Real.log (n : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast (show 0 < a by omega)
        · exact_mod_cast (Nat.le_of_lt hna)
      exact (mul_le_mul_of_nonneg_left hlog ArithmeticFunction.vonMangoldt_nonneg).trans
        (nativeLambda_mul_log_le_lambdaTwo n hnI.1)
    _ = nativeLambdaTwoSummatory b - nativeLambdaTwoSummatory a := by
      unfold nativeLambdaTwoSummatory
      rw [← Finset.sum_sdiff hsub]
      ring

/-- Combining the local `Lambda_2` domination with the summatory Selberg
formula gives an explicit local upper bound for Chebyshev increments. -/
theorem nativePsi_interval_mul_log_le_explicit
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b) :
    (nativePsi b - nativePsi a) * Real.log (a : ℝ) ≤
      2 * (b : ℝ) * Real.log (b : ℝ) -
        2 * (a : ℝ) * Real.log (a : ℝ) +
        (2 * (Real.log 4 + 2) + 172) * ((a : ℝ) + (b : ℝ)) := by
  have hlocal := nativePsi_interval_mul_log_le_lambdaTwo_interval a b (by omega) hab
  have haSel := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le a ha
  have hbSel := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le b (ha.trans hab)
  rw [abs_le] at haSel hbSel
  calc
    (nativePsi b - nativePsi a) * Real.log (a : ℝ) ≤
        nativeLambdaTwoSummatory b - nativeLambdaTwoSummatory a := hlocal
    _ ≤ 2 * (b : ℝ) * Real.log (b : ℝ) -
          2 * (a : ℝ) * Real.log (a : ℝ) +
          (2 * (Real.log 4 + 2) + 172) * ((a : ℝ) + (b : ℝ)) := by
      nlinarith [haSel.1, hbSel.2]

/-! ## Prime-specific one-sided excursions -/

/-- The finite Chebyshev mass is monotone.  This is purely coefficientwise:
every von Mangoldt weight is nonnegative. -/
theorem nativePsi_monotone : Monotone nativePsi := by
  intro a b hab
  unfold nativePsi
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hna⟩
    exact Finset.mem_Icc.mpr ⟨hn1, hna.trans hab⟩
  · intro n _hn _hna
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- A positive error spike can decay forward only with slope one: increasing
`psi` cannot make `R = psi - id` fall faster than the linear term. -/
theorem nativePNTError_forward_lower (N h : ℕ) :
    nativePNTError N - (h : ℝ) ≤ nativePNTError (N + h) := by
  have hpsi : nativePsi N ≤ nativePsi (N + h) :=
    nativePsi_monotone (by omega)
  unfold nativePNTError
  rw [Nat.cast_add]
  linarith

/-- Dually, a negative error spike can rise backward only with slope one. -/
theorem nativePNTError_backward_upper (N h : ℕ) (hh : h ≤ N) :
    nativePNTError (N - h) ≤ nativePNTError N + (h : ℝ) := by
  have hpsi : nativePsi (N - h) ≤ nativePsi N :=
    nativePsi_monotone (Nat.sub_le N h)
  unfold nativePNTError
  rw [Nat.cast_sub hh]
  linarith

/-- **Positive good interval.**  If `R(N) >= H >= 0`, then throughout every
forward displacement `h <= H/2` the absolute error remains at least `H/2`. -/
theorem nativePNTError_positive_excursion
    (N h : ℕ) (H : ℝ) (hH0 : 0 ≤ H)
    (hpin : H ≤ nativePNTError N) (hh : (h : ℝ) ≤ H / 2) :
    H / 2 ≤ |nativePNTError (N + h)| := by
  have hstep := nativePNTError_forward_lower N h
  have hhalf : H / 2 ≤ nativePNTError (N + h) := by
    linarith
  have hnonneg : 0 ≤ nativePNTError (N + h) := by
    linarith
  rw [abs_of_nonneg hnonneg]
  exact hhalf

/-- **Negative good interval.**  If `R(N) <= -H` with `H >= 0`, then throughout
every backward displacement `h <= min N (H/2)` the absolute error remains at
least `H/2`. -/
theorem nativePNTError_negative_excursion
    (N h : ℕ) (H : ℝ) (hH0 : 0 ≤ H) (hhN : h ≤ N)
    (hpin : nativePNTError N ≤ -H) (hh : (h : ℝ) ≤ H / 2) :
    H / 2 ≤ |nativePNTError (N - h)| := by
  have hstep := nativePNTError_backward_upper N h hhN
  have hhalf : nativePNTError (N - h) ≤ -(H / 2) := by
    linarith
  have hnonpos : nativePNTError (N - h) ≤ 0 := by
    linarith
  rw [abs_of_nonpos hnonpos]
  linarith

end RHLean.Analysis
