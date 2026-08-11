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


/-! ## Erdos PNT1: a small point in a long multiplicative interval -/

/-- Exact one-step identity for the Chebyshev error. -/
theorem nativePNTError_succ_eq (n : ℕ) :
    nativePNTError (n + 1) - nativePNTError n = Λ (n + 1) - 1 := by
  unfold nativePNTError
  rw [nativePsi_succ]
  push_cast
  ring

/-- Pointwise elementary bound `Lambda(n) <= log n` for positive integers. -/
theorem nativeVonMangoldt_le_log (n : ℕ) (hn : 1 ≤ n) :
    Λ n ≤ Real.log (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hnmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hn0⟩
  calc
    Λ n ≤ ∑ d ∈ n.divisors, Λ d :=
      Finset.single_le_sum
        (fun d _hd => ArithmeticFunction.vonMangoldt_nonneg) hnmem
    _ = Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_sum

/-- A positive excursion cannot jump across zero in one step once its two
endpoint margins exceed the unit downward slope. -/
private theorem nativePNT_no_positive_to_negative
    (n : ℕ) (ε : ℝ)
    (hsize : 1 < ε * (2 * (n : ℝ) + 1))
    (hpos : ε * (n : ℝ) ≤ nativePNTError n)
    (hneg : nativePNTError (n + 1) ≤ -ε * ((n + 1 : ℕ) : ℝ)) : False := by
  have hstep := nativePNTError_succ_eq n
  have hLambda0 : 0 ≤ Λ (n + 1) := ArithmeticFunction.vonMangoldt_nonneg
  have hlower : -1 ≤ nativePNTError (n + 1) - nativePNTError n := by
    linarith
  push_cast at hneg
  nlinarith

/-- A negative excursion cannot jump across zero in one step once the local
von Mangoldt jump is small compared with the two endpoint margins. -/
private theorem nativePNT_no_negative_to_positive
    (n : ℕ) (ε : ℝ)
    (hn : 1 ≤ n)
    (hsize : Real.log ((n + 1 : ℕ) : ℝ) - 1 < ε * (2 * (n : ℝ) + 1))
    (hneg : nativePNTError n ≤ -ε * (n : ℝ))
    (hpos : ε * ((n + 1 : ℕ) : ℝ) ≤ nativePNTError (n + 1)) : False := by
  have hstep := nativePNTError_succ_eq n
  have hLambda := nativeVonMangoldt_le_log (n + 1) (by omega)
  have hupper :
      nativePNTError (n + 1) - nativePNTError n ≤
        Real.log ((n + 1 : ℕ) : ℝ) - 1 := by
    linarith
  push_cast at hpos
  nlinarith

/-- If the normalized error stays outside an `ε`-tube and adjacent sign
changes are quantitatively impossible, then the error has one sign throughout
the integer interval. -/
theorem nativePNTError_sign_constant_of_away
    (A B : ℕ) (ε : ℝ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hε : 0 < ε)
    (hdown : ∀ n, A ≤ n → n < B →
      1 < ε * (2 * (n : ℝ) + 1))
    (hup : ∀ n, A ≤ n → n < B →
      Real.log ((n + 1 : ℕ) : ℝ) - 1 < ε * (2 * (n : ℝ) + 1))
    (haway : ∀ n ∈ Finset.Icc A B,
      ε * (n : ℝ) ≤ |nativePNTError n|) :
    (∀ n ∈ Finset.Icc A B, 0 ≤ nativePNTError n) ∨
      (∀ n ∈ Finset.Icc A B, nativePNTError n ≤ 0) := by
  by_cases hsign : 0 ≤ nativePNTError A
  · left
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hAn, hnB⟩
    have hprop : ∀ m, A ≤ m → m ≤ B → 0 ≤ nativePNTError m := by
      intro m hAm
      induction m, hAm using Nat.le_induction with
      | base =>
          intro _hAB
          exact hsign
      | succ m hAm ih =>
          intro hmB
          have hmBlt : m < B := by omega
          have him : 0 ≤ nativePNTError m := ih (by omega)
          have hmMem : m ∈ Finset.Icc A B := Finset.mem_Icc.mpr ⟨hAm, by omega⟩
          have hsMem : m + 1 ∈ Finset.Icc A B :=
            Finset.mem_Icc.mpr ⟨by omega, hmB⟩
          have hmAway := haway m hmMem
          have hsAway := haway (m + 1) hsMem
          have hmLower : ε * (m : ℝ) ≤ nativePNTError m := by
            rw [abs_of_nonneg him] at hmAway
            exact hmAway
          by_contra hnext
          have hnextNeg : nativePNTError (m + 1) < 0 := lt_of_not_ge hnext
          have hsUpper :
              nativePNTError (m + 1) ≤ -ε * (((m + 1 : ℕ) : ℝ)) := by
            rw [abs_of_nonpos hnextNeg.le] at hsAway
            linarith
          exact nativePNT_no_positive_to_negative m ε
            (hdown m hAm hmBlt) hmLower hsUpper
    exact hprop n hAn hnB
  · right
    have hsign' : nativePNTError A ≤ 0 := le_of_not_ge hsign
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hAn, hnB⟩
    have hprop : ∀ m, A ≤ m → m ≤ B → nativePNTError m ≤ 0 := by
      intro m hAm
      induction m, hAm using Nat.le_induction with
      | base =>
          intro _hAB
          exact hsign'
      | succ m hAm ih =>
          intro hmB
          have hmBlt : m < B := by omega
          have him : nativePNTError m ≤ 0 := ih (by omega)
          have hmMem : m ∈ Finset.Icc A B := Finset.mem_Icc.mpr ⟨hAm, by omega⟩
          have hsMem : m + 1 ∈ Finset.Icc A B :=
            Finset.mem_Icc.mpr ⟨by omega, hmB⟩
          have hmAway := haway m hmMem
          have hsAway := haway (m + 1) hsMem
          have hmUpper : nativePNTError m ≤ -ε * (m : ℝ) := by
            rw [abs_of_nonpos him] at hmAway
            linarith
          by_contra hnext
          have hnextPos : 0 < nativePNTError (m + 1) := lt_of_not_ge hnext
          have hsLower :
              ε * (((m + 1 : ℕ) : ℝ)) ≤ nativePNTError (m + 1) := by
            rw [abs_of_nonneg hnextPos.le] at hsAway
            exact hsAway
          exact nativePNT_no_negative_to_positive m ε (by omega)
            (hup m hAm hmBlt) hmUpper hsLower
    exact hprop n hAn hnB

/-- Reciprocal signed error mass on an arbitrary positive integer interval. -/
def nativePNTWeightedErrorIntervalMass (A B : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc A B,
    nativePNTError n / ((n : ℝ) * (n + 1 : ℝ))

private theorem nativePNTWeightedErrorIntervalMass_eq_prefix_sub
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    nativePNTWeightedErrorIntervalMass A B =
      nativePNTWeightedErrorMass B - nativePNTWeightedErrorMass (A - 1) := by
  let f : ℕ → ℝ := fun n =>
    nativePNTError n / ((n : ℝ) * (n + 1 : ℝ))
  have hsets :
      Finset.Icc 1 B = Finset.Icc 1 (A - 1) ∪ Finset.Icc A B := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdis : Disjoint (Finset.Icc 1 (A - 1)) (Finset.Icc A B) := by
    refine Finset.disjoint_left.mpr ?_
    intro n hn1 hn2
    rw [Finset.mem_Icc] at hn1 hn2
    omega
  unfold nativePNTWeightedErrorIntervalMass nativePNTWeightedErrorMass
  change (∑ n ∈ Finset.Icc A B, f n) =
    (∑ n ∈ Finset.Icc 1 B, f n) - (∑ n ∈ Finset.Icc 1 (A - 1), f n)
  rw [hsets, Finset.sum_union hdis]
  ring

private theorem nativePNTWeightedErrorIntervalMass_abs_le
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    |nativePNTWeightedErrorIntervalMass A B| ≤
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) := by
  rw [nativePNTWeightedErrorIntervalMass_eq_prefix_sub A B hA hAB]
  calc
    |nativePNTWeightedErrorMass B - nativePNTWeightedErrorMass (A - 1)| ≤
        |nativePNTWeightedErrorMass B| +
          |nativePNTWeightedErrorMass (A - 1)| := abs_sub _ _
    _ ≤ (2 * (Real.log 4 + 2) + Real.log 2 + 3) +
          (2 * (Real.log 4 + 2) + Real.log 2 + 3) :=
      add_le_add (nativePNTWeightedErrorMass_abs_le B)
        (nativePNTWeightedErrorMass_abs_le (A - 1))
    _ = 2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) := by ring

/-- Exact reciprocal sum on an integer interval. -/
private theorem nativePNTRecipSuccInterval_eq_harmonic_sub
    (A : ℕ) : ∀ B : ℕ, A ≤ B →
    (∑ n ∈ Finset.Icc A B, 1 / (((n + 1 : ℕ) : ℝ))) =
      (harmonic (B + 1) : ℝ) - (harmonic A : ℝ) := by
  intro B hAB
  induction B, hAB using Nat.le_induction with
  | base =>
      rw [Finset.Icc_self, Finset.sum_singleton, harmonic_succ]
      push_cast
      simp [div_eq_mul_inv]
  | succ B hAB ih =>
      rw [Finset.sum_Icc_succ_top (by omega : A ≤ B + 1), ih, harmonic_succ]
      push_cast
      ring

/-- The reciprocal interval has the elementary logarithmic lower bound. -/
private theorem nativePNTRecipSuccInterval_log_lower
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    Real.log ((B + 2 : ℕ) : ℝ) - Real.log (A : ℝ) - 1 ≤
      ∑ n ∈ Finset.Icc A B, 1 / (((n + 1 : ℕ) : ℝ)) := by
  rw [nativePNTRecipSuccInterval_eq_harmonic_sub A B hAB]
  have hlo := log_add_one_le_harmonic (B + 1)
  have hup := harmonic_le_one_add_log A
  push_cast at hlo hup ⊢
  linarith

/-- On the dyadic span `[A, A*2^K]`, the reciprocal interval mass is at least
`K log 2 - 1`. -/
private theorem nativePNTRecipSuccDyadic_lower
    (A K : ℕ) (hA : 1 ≤ A) :
    (K : ℝ) * Real.log 2 - 1 ≤
      ∑ n ∈ Finset.Icc A (A * 2 ^ K),
        1 / (((n + 1 : ℕ) : ℝ)) := by
  have hpow1 : 1 ≤ 2 ^ K := one_le_pow₀ (by norm_num : 0 ≤ (2 : ℕ))
  have hAB : A ≤ A * 2 ^ K := by
    calc A = A * 1 := by omega
      _ ≤ A * 2 ^ K := Nat.mul_le_mul_left A hpow1
  have hlog := nativePNTRecipSuccInterval_log_lower A (A * 2 ^ K) hA hAB
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  have hpowpos : (0 : ℝ) < ((2 ^ K : ℕ) : ℝ) := by positivity
  have hBpos : (0 : ℝ) < ((A * 2 ^ K : ℕ) : ℝ) := by positivity
  have hmono :
      Real.log ((A * 2 ^ K : ℕ) : ℝ) ≤
        Real.log ((A * 2 ^ K + 2 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact hBpos
    · exact_mod_cast (show A * 2 ^ K ≤ A * 2 ^ K + 2 by omega)
  have hprod :
      Real.log ((A * 2 ^ K : ℕ) : ℝ) =
        Real.log (A : ℝ) + (K : ℝ) * Real.log 2 := by
    rw [Nat.cast_mul, Nat.cast_pow]
    rw [Real.log_mul (ne_of_gt hApos) (ne_of_gt hpowpos), Real.log_pow]
  rw [hprod] at hmono
  linarith

private theorem nativePNTWeightedErrorIntervalMass_lower_of_nonneg
    (A B : ℕ) (ε : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B)
    (hsign : ∀ n ∈ Finset.Icc A B, 0 ≤ nativePNTError n)
    (haway : ∀ n ∈ Finset.Icc A B,
      ε * (n : ℝ) ≤ |nativePNTError n|) :
    ε * (∑ n ∈ Finset.Icc A B, 1 / (((n + 1 : ℕ) : ℝ))) ≤
      nativePNTWeightedErrorIntervalMass A B := by
  unfold nativePNTWeightedErrorIntervalMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1.trans' hA
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hspos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
  have herr := haway n hn
  rw [abs_of_nonneg (hsign n hn)] at herr
  calc
    ε * (1 / (((n + 1 : ℕ) : ℝ))) =
        (ε * (n : ℝ)) / ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) := by
      field_simp [ne_of_gt hnpos, ne_of_gt hspos]
      ring
    _ ≤ nativePNTError n / ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) :=
      div_le_div_of_nonneg_right herr (mul_nonneg hnpos.le hspos.le)

private theorem nativePNTWeightedErrorIntervalMass_neg_lower_of_nonpos
    (A B : ℕ) (ε : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B)
    (hsign : ∀ n ∈ Finset.Icc A B, nativePNTError n ≤ 0)
    (haway : ∀ n ∈ Finset.Icc A B,
      ε * (n : ℝ) ≤ |nativePNTError n|) :
    ε * (∑ n ∈ Finset.Icc A B, 1 / (((n + 1 : ℕ) : ℝ))) ≤
      -nativePNTWeightedErrorIntervalMass A B := by
  unfold nativePNTWeightedErrorIntervalMass
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1.trans' hA
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hspos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
  have herr := haway n hn
  rw [abs_of_nonpos (hsign n hn)] at herr
  calc
    ε * (1 / (((n + 1 : ℕ) : ℝ))) =
        (ε * (n : ℝ)) / ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) := by
      field_simp [ne_of_gt hnpos, ne_of_gt hspos]
      ring
    _ ≤ (-nativePNTError n) / ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) :=
      div_le_div_of_nonneg_right herr (mul_nonneg hnpos.le hspos.le)
    _ = -(nativePNTError n / ((n : ℝ) * (((n + 1 : ℕ) : ℝ)))) := by ring

/-- **Erdos PNT1 in dyadic form.**  A sufficiently long dyadic span cannot
stay uniformly outside an `ε`-tube once adjacent sign changes are excluded.
The contradiction is exactly the bounded signed reciprocal error mass. -/
theorem nativePNT_exists_small_error_dyadic
    (A K : ℕ) (ε : ℝ)
    (hA : 1 ≤ A) (hε : 0 < ε)
    (hdown : ∀ n, A ≤ n → n < A * 2 ^ K →
      1 < ε * (2 * (n : ℝ) + 1))
    (hup : ∀ n, A ≤ n → n < A * 2 ^ K →
      Real.log ((n + 1 : ℕ) : ℝ) - 1 < ε * (2 * (n : ℝ) + 1))
    (hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        ε * ((K : ℝ) * Real.log 2 - 1)) :
    ∃ n ∈ Finset.Icc A (A * 2 ^ K),
      |nativePNTError n| < ε * (n : ℝ) := by
  have hpow1 : 1 ≤ 2 ^ K := one_le_pow₀ (by norm_num : 0 ≤ (2 : ℕ))
  have hAB : A ≤ A * 2 ^ K := by
    calc A = A * 1 := by omega
      _ ≤ A * 2 ^ K := Nat.mul_le_mul_left A hpow1
  by_contra hno
  push_neg at hno
  have haway : ∀ n ∈ Finset.Icc A (A * 2 ^ K),
      ε * (n : ℝ) ≤ |nativePNTError n| := by
    intro n hn
    exact le_of_not_gt (hno n hn)
  have hsign := nativePNTError_sign_constant_of_away
    A (A * 2 ^ K) ε hA hAB hε hdown hup haway
  have hrecip := nativePNTRecipSuccDyadic_lower A K hA
  have hupper := nativePNTWeightedErrorIntervalMass_abs_le
    A (A * 2 ^ K) hA hAB
  have hscale :
      ε * ((K : ℝ) * Real.log 2 - 1) ≤
        ε * (∑ n ∈ Finset.Icc A (A * 2 ^ K),
          1 / (((n + 1 : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_left hrecip hε.le
  rcases hsign with hpos | hneg
  · have hlower := nativePNTWeightedErrorIntervalMass_lower_of_nonneg
      A (A * 2 ^ K) ε hA hAB hpos haway
    have hmass0 : 0 ≤ nativePNTWeightedErrorIntervalMass A (A * 2 ^ K) := by
      unfold nativePNTWeightedErrorIntervalMass
      apply Finset.sum_nonneg
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1.trans' hA
      exact div_nonneg (hpos n hn)
        (mul_nonneg (by exact_mod_cast hn1) (by positivity))
    rw [abs_of_nonneg hmass0] at hupper
    linarith
  · have hlower := nativePNTWeightedErrorIntervalMass_neg_lower_of_nonpos
      A (A * 2 ^ K) ε hA hAB hneg haway
    have hmass0 : nativePNTWeightedErrorIntervalMass A (A * 2 ^ K) ≤ 0 := by
      unfold nativePNTWeightedErrorIntervalMass
      apply Finset.sum_nonpos
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1.trans' hA
      exact div_nonpos_of_nonpos_of_nonneg (hneg n hn)
        (mul_nonneg (by exact_mod_cast hn1) (by positivity))
    rw [abs_of_nonpos hmass0] at hupper
    linarith


/-! ## Erdos PNT2: thicken a small point into a good interval -/

/-- A convenient explicit local Chebyshev increment estimate extracted from
the summatory Selberg formula.  The constants are deliberately coarse. -/
theorem nativePsi_interval_mul_log_le_gap_tail
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b) (hb2 : b ≤ 2 * a) :
    (nativePsi b - nativePsi a) * Real.log (a : ℝ) ≤
      2 * ((b : ℝ) - (a : ℝ)) * Real.log (a : ℝ) + 550 * (a : ℝ) := by
  have hlocal := nativePsi_interval_mul_log_le_explicit a b ha hab
  have haR0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hbR0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hb2R : (b : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hb2
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlogb : Real.log (b : ℝ) ≤ Real.log (a : ℝ) + 1 := by
    calc
      Real.log (b : ℝ) ≤ Real.log (2 * (a : ℝ)) := by
        apply Real.log_le_log
        · exact hbR0
        · exact hb2R
      _ = Real.log 2 + Real.log (a : ℝ) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt haR0)]
      _ ≤ Real.log (a : ℝ) + 1 := by linarith
  have hmain1 :
      2 * (b : ℝ) * Real.log (b : ℝ) ≤
        2 * (b : ℝ) * (Real.log (a : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hlogb (by positivity)
  have hmain :
      2 * (b : ℝ) * Real.log (b : ℝ) -
          2 * (a : ℝ) * Real.log (a : ℝ) ≤
        2 * ((b : ℝ) - (a : ℝ)) * Real.log (a : ℝ) + 4 * (a : ℝ) := by
    nlinarith
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h ⊢
    exact h
  have hC : 2 * (Real.log 4 + 2) + 172 ≤ (182 : ℝ) := by
    linarith
  have hab3 : (a : ℝ) + (b : ℝ) ≤ 3 * (a : ℝ) := by
    linarith
  have htail :
      (2 * (Real.log 4 + 2) + 172) * ((a : ℝ) + (b : ℝ)) ≤
        546 * (a : ℝ) := by
    calc
      (2 * (Real.log 4 + 2) + 172) * ((a : ℝ) + (b : ℝ)) ≤
          182 * ((a : ℝ) + (b : ℝ)) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ 182 * (3 * (a : ℝ)) :=
        mul_le_mul_of_nonneg_left hab3 (by norm_num)
      _ = 546 * (a : ℝ) := by ring
  linarith

/-- Divided form of the local increment estimate. -/
theorem nativePsi_interval_le_gap_tail
    (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b) (hb2 : b ≤ 2 * a)
    (hlog : 1 ≤ Real.log (a : ℝ)) :
    nativePsi b - nativePsi a ≤
      2 * ((b : ℝ) - (a : ℝ)) + 550 * (a : ℝ) / Real.log (a : ℝ) := by
  have hprod := nativePsi_interval_mul_log_le_gap_tail a b ha hab hb2
  have hlogpos : 0 < Real.log (a : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have heq :
      2 * ((b : ℝ) - (a : ℝ)) + 550 * (a : ℝ) / Real.log (a : ℝ) =
        (2 * ((b : ℝ) - (a : ℝ)) * Real.log (a : ℝ) + 550 * (a : ℝ)) /
          Real.log (a : ℝ) := by
    field_simp [ne_of_gt hlogpos]
    ring
  rw [heq, le_div_iff₀ hlogpos]
  exact hprod

/-- **Erdos PNT2 in forward-interval form.**  If one endpoint has normalized
error at most `ε/4`, and the endpoint is large enough that the Selberg linear
remainder is at most `ε/4`, then every forward displacement of relative size
at most `ε/8` has normalized error at most `ε`. -/
theorem nativePNTError_good_forward_interval
    (A h : ℕ) (ε : ℝ)
    (hA : 3 ≤ A) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ Real.log (A : ℝ))
    (htail : 2200 ≤ ε * Real.log (A : ℝ))
    (hsmall : |nativePNTError A| ≤ ε * (A : ℝ) / 4)
    (hh : (h : ℝ) ≤ ε * (A : ℝ) / 8) :
    |nativePNTError (A + h)| ≤ ε * ((A + h : ℕ) : ℝ) := by
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  have hlogpos : 0 < Real.log (A : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hε0 : 0 ≤ ε := hε.le
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := by positivity
  have hhAreal : (h : ℝ) ≤ (A : ℝ) := by
    calc
      (h : ℝ) ≤ ε * (A : ℝ) / 8 := hh
      _ ≤ (A : ℝ) / 8 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hε1 (by positivity)) (by norm_num)
      _ ≤ (A : ℝ) := by nlinarith
  have hhA : h ≤ A := by exact_mod_cast hhAreal
  have hAB : A ≤ A + h := by omega
  have hB2 : A + h ≤ 2 * A := by omega
  have hinc := nativePsi_interval_le_gap_tail A (A + h) hA hAB hB2 hlog
  have htailTerm :
      550 * (A : ℝ) / Real.log (A : ℝ) ≤ ε * (A : ℝ) / 4 := by
    rw [div_le_iff₀ hlogpos]
    have hmul := mul_le_mul_of_nonneg_right htail (show 0 ≤ (A : ℝ) / 4 by positivity)
    nlinarith
  have hgap :
      2 * (((A + h : ℕ) : ℝ) - (A : ℝ)) ≤ ε * (A : ℝ) / 4 := by
    push_cast
    nlinarith
  have hpsi :
      nativePsi (A + h) - nativePsi A ≤ ε * (A : ℝ) / 2 := by
    calc
      nativePsi (A + h) - nativePsi A ≤
          2 * (((A + h : ℕ) : ℝ) - (A : ℝ)) +
            550 * (A : ℝ) / Real.log (A : ℝ) := hinc
      _ ≤ ε * (A : ℝ) / 4 + ε * (A : ℝ) / 4 :=
        add_le_add hgap htailTerm
      _ = ε * (A : ℝ) / 2 := by ring
  have hsmall' := hsmall
  rw [abs_le] at hsmall'
  have hlowerStep := nativePNTError_forward_lower A h
  have hupperRel :
      nativePNTError (A + h) =
        nativePNTError A + (nativePsi (A + h) - nativePsi A) - (h : ℝ) := by
    unfold nativePNTError
    push_cast
    ring
  rw [abs_le]
  constructor
  · have : -ε * ((A + h : ℕ) : ℝ) ≤ nativePNTError (A + h) := by
      push_cast
      nlinarith [hlowerStep, hsmall'.1]
    exact this
  · rw [hupperRel]
    push_cast
    nlinarith [hsmall'.2, hpsi]

end RHLean.Analysis
