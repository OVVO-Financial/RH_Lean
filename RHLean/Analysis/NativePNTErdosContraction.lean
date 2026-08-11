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
theorem nativeLambda_mul_log_le_lambdaTwo (n : ℕ) (_hn : 1 ≤ n) :
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
    Λ n ≤ ∑ d ∈ n.divisors, Λ d := by
      exact Finset.single_le_sum
        (s := n.divisors) (f := fun d => Λ d)
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
    (hA : 1 ≤ A) (_hAB : A ≤ B) (_hε : 0 < ε)
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
      rw [Finset.sum_Icc_succ_top (by omega : A ≤ B + 1), ih]
      rw [show B + 2 = (B + 1) + 1 by omega, harmonic_succ (B + 1)]
      push_cast
      ring

/-- The reciprocal interval has the elementary logarithmic lower bound. -/
private theorem nativePNTRecipSuccInterval_log_lower
    (A B : ℕ) (_hA : 1 ≤ A) (hAB : A ≤ B) :
    Real.log ((B + 2 : ℕ) : ℝ) - Real.log (A : ℝ) - 1 ≤
      ∑ n ∈ Finset.Icc A B, 1 / (((n + 1 : ℕ) : ℝ)) := by
  rw [nativePNTRecipSuccInterval_eq_harmonic_sub A B hAB]
  have hlo : Real.log ((B + 2 : ℕ) : ℝ) ≤ (harmonic (B + 1) : ℝ) := by
    simpa [show B + 2 = (B + 1) + 1 by omega] using
      (log_add_one_le_harmonic (B + 1))
  have hup : (harmonic A : ℝ) ≤ 1 + Real.log (A : ℝ) := by
    simpa using (harmonic_le_one_add_log A)
  linarith

/-- On the dyadic span `[A, A*2^K]`, the reciprocal interval mass is at least
`K log 2 - 1`. -/
private theorem nativePNTRecipSuccDyadic_lower
    (A K : ℕ) (hA : 1 ≤ A) :
    (K : ℝ) * Real.log 2 - 1 ≤
      ∑ n ∈ Finset.Icc A (A * 2 ^ K),
        1 / (((n + 1 : ℕ) : ℝ)) := by
  have hpow1 : 1 ≤ 2 ^ K := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
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
    rw [Real.log_mul (ne_of_gt hApos) (by positivity), Real.log_pow]
    norm_num
  rw [hprod] at hmono
  linarith

private theorem nativePNTWeightedErrorIntervalMass_lower_of_nonneg
    (A B : ℕ) (ε : ℝ) (hA : 1 ≤ A) (_hAB : A ≤ B)
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
  push_cast at hspos ⊢
  calc
    ε * (1 / ((n : ℝ) + 1)) =
        (ε * (n : ℝ)) / ((n : ℝ) * ((n : ℝ) + 1)) := by
      field_simp [ne_of_gt hnpos]
    _ ≤ nativePNTError n / ((n : ℝ) * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right herr (mul_nonneg hnpos.le hspos.le)

private theorem nativePNTWeightedErrorIntervalMass_neg_lower_of_nonpos
    (A B : ℕ) (ε : ℝ) (hA : 1 ≤ A) (_hAB : A ≤ B)
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
  push_cast at hspos ⊢
  calc
    ε * (1 / ((n : ℝ) + 1)) =
        (ε * (n : ℝ)) / ((n : ℝ) * ((n : ℝ) + 1)) := by
      field_simp [ne_of_gt hnpos]
    _ ≤ (-nativePNTError n) / ((n : ℝ) * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right herr (mul_nonneg hnpos.le hspos.le)
    _ = -(nativePNTError n / ((n : ℝ) * ((n : ℝ) + 1))) := by ring

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
  have hpow1 : 1 ≤ 2 ^ K := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
  have hAB : A ≤ A * 2 ^ K := by
    calc A = A * 1 := by omega
      _ ≤ A * 2 ^ K := Nat.mul_le_mul_left A hpow1
  by_contra hno
  push_neg at hno
  have haway : ∀ n ∈ Finset.Icc A (A * 2 ^ K),
      ε * (n : ℝ) ≤ |nativePNTError n| := by
    intro n hn
    exact hno n hn
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
        (mul_nonneg (by positivity) (by positivity))
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
        (mul_nonneg (by positivity) (by positivity))
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
        have hmulA : ε * (A : ℝ) ≤ 1 * (A : ℝ) :=
          mul_le_mul_of_nonneg_right hε1 (by positivity)
        nlinarith
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
  · have hlow : -ε * ((A + h : ℕ) : ℝ) ≤ nativePNTError (A + h) := by
      push_cast
      nlinarith [hlowerStep, hsmall'.1]
    simpa only [neg_mul] using hlow
  · rw [hupperRel]
    push_cast
    nlinarith [hsmall'.2, hpsi]


/-! ## Erdos PNT3: reciprocal mass of the second Selberg kernel -/

/-- Reciprocal mass of the nonnegative second von Mangoldt kernel. -/
def nativeLambdaTwoRecipMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, nativeLambdaTwo n / (n : ℝ)

/-- Reciprocal `Lambda_2` mass on the interval `(A,B]`. -/
def nativeLambdaTwoRecipIntervalMass (A B : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (A + 1) B, nativeLambdaTwo n / (n : ℝ)

/-- Exact Abel summation formula for the reciprocal `Lambda_2` mass. -/
theorem nativeLambdaTwoRecipMass_abel (N : ℕ) :
    nativeLambdaTwoRecipMass N =
      nativeLambdaTwoSummatory N / (N : ℝ) +
        ∑ n ∈ Finset.Ico 1 N,
          nativeLambdaTwoSummatory n *
            (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ))) := by
  have h := nativeAbelIccOne nativeLambdaTwo
    (fun n : ℕ => 1 / (n : ℝ)) N
  unfold nativeLambdaTwoRecipMass nativeLambdaTwoSummatory
  simpa [div_eq_mul_inv] using h

/-- The reciprocal second-kernel mass is nonnegative. -/
theorem nativeLambdaTwoRecipMass_nonneg (N : ℕ) :
    0 ≤ nativeLambdaTwoRecipMass N := by
  unfold nativeLambdaTwoRecipMass
  apply Finset.sum_nonneg
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  exact div_nonneg (nativeLambdaTwo_nonneg n hn1) (by positivity)

/-- The difference of two summatory `Lambda_2` values is exactly the kernel
mass on the intervening integer interval. -/
theorem nativeLambdaTwoSummatory_sub_eq_interval
    (A B : ℕ) (hAB : A ≤ B) :
    nativeLambdaTwoSummatory B - nativeLambdaTwoSummatory A =
      ∑ n ∈ Finset.Icc (A + 1) B, nativeLambdaTwo n := by
  have hsub : Finset.Icc 1 A ⊆ Finset.Icc 1 B := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnA⟩
    exact Finset.mem_Icc.mpr ⟨hn1, hnA.trans hAB⟩
  have hset :
      Finset.Icc 1 B \ Finset.Icc 1 A = Finset.Icc (A + 1) B := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  unfold nativeLambdaTwoSummatory
  rw [← Finset.sum_sdiff hsub, hset]
  ring

/-- Positivity converts summatory `Lambda_2` mass into reciprocal mass: on
`(A,B]`, every reciprocal is at least `1/B`. -/
theorem nativeLambdaTwoRecipIntervalMass_lower
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    (nativeLambdaTwoSummatory B - nativeLambdaTwoSummatory A) / (B : ℝ) ≤
      nativeLambdaTwoRecipIntervalMass A B := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (show 0 < B by omega)
  rw [nativeLambdaTwoSummatory_sub_eq_interval A B hAB]
  unfold nativeLambdaTwoRecipIntervalMass
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  have hnI := Finset.mem_Icc.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hnB : (n : ℝ) ≤ (B : ℝ) := by exact_mod_cast hnI.2
  have hLambda : 0 ≤ nativeLambdaTwo n :=
    nativeLambdaTwo_nonneg n (by omega)
  rw [div_le_div_iff₀ hBpos hnpos]
  exact mul_le_mul_of_nonneg_left hnB hLambda

/-- Explicit lower main term for `Lambda_2` mass on `(A,B]`. -/
theorem nativeLambdaTwoSummatory_interval_main_lower
    (A B : ℕ) (hA : 3 ≤ A) (hAB : A ≤ B) :
    2 * (B : ℝ) * Real.log (B : ℝ) -
        2 * (A : ℝ) * Real.log (A : ℝ) -
        (2 * (Real.log 4 + 2) + 172) * ((A : ℝ) + (B : ℝ)) ≤
      nativeLambdaTwoSummatory B - nativeLambdaTwoSummatory A := by
  have hASel := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le A hA
  have hBSel := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le B (hA.trans hAB)
  rw [abs_le] at hASel hBSel
  nlinarith [hASel.2, hBSel.1]

/-- The Selberg main term therefore gives an explicit reciprocal `Lambda_2`
mass on every positive block.  This is the coefficient lower bound used by
the cubic deficit. -/
theorem nativeLambdaTwoRecipIntervalMass_main_lower
    (A B : ℕ) (hA : 3 ≤ A) (hAB : A ≤ B) :
    (2 * (B : ℝ) * Real.log (B : ℝ) -
        2 * (A : ℝ) * Real.log (A : ℝ) -
        (2 * (Real.log 4 + 2) + 172) * ((A : ℝ) + (B : ℝ))) / (B : ℝ) ≤
      nativeLambdaTwoRecipIntervalMass A B := by
  have hB0 : 0 ≤ (B : ℝ) := by positivity
  have hmain := nativeLambdaTwoSummatory_interval_main_lower A B hA hAB
  have hdiv := div_le_div_of_nonneg_right hmain hB0
  exact hdiv.trans (nativeLambdaTwoRecipIntervalMass_lower A B (by omega) hAB)


/-! ## Quantified PNT1/PNT2 block -/

/-- The pointwise no-crossing hypotheses in `nativePNT_exists_small_error_dyadic`
follow from two scalar endpoint inequalities.  This is the form used in the
geometric packing argument. -/
theorem nativePNT_exists_small_error_dyadic_of_endpoint
    (A K : ℕ) (ε : ℝ)
    (hA : 1 ≤ A) (hε : 0 < ε)
    (hdownA : 1 < ε * (2 * (A : ℝ) + 1))
    (hupA :
      Real.log ((A * 2 ^ K : ℕ) : ℝ) - 1 <
        ε * (2 * (A : ℝ) + 1))
    (hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        ε * ((K : ℝ) * Real.log 2 - 1)) :
    ∃ n ∈ Finset.Icc A (A * 2 ^ K),
      |nativePNTError n| < ε * (n : ℝ) := by
  have hpow1 : 1 ≤ 2 ^ K := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
  have hAB : A ≤ A * 2 ^ K := by
    calc A = A * 1 := by omega
      _ ≤ A * 2 ^ K := Nat.mul_le_mul_left A hpow1
  refine nativePNT_exists_small_error_dyadic A K ε hA hε ?_ ?_ hdepth
  · intro n hAn _hnB
    have hAnR : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAn
    have hε0 : 0 ≤ ε := hε.le
    nlinarith
  · intro n hAn hnB
    have hn1B : n + 1 ≤ A * 2 ^ K := by omega
    have hn1pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hBpos : (0 : ℝ) < ((A * 2 ^ K : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < A * 2 ^ K by positivity)
    have hlog :
        Real.log ((n + 1 : ℕ) : ℝ) ≤
          Real.log ((A * 2 ^ K : ℕ) : ℝ) := by
      apply Real.log_le_log
      · exact hn1pos
      · exact_mod_cast hn1B
    have hAnR : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAn
    have hε0 : 0 ≤ ε := hε.le
    nlinarith

/-- **Combined Erdos PNT1/PNT2 good block.**  A dyadic search block satisfying
only scalar endpoint and depth conditions contains a point whose forward
relative `ε/8` interval stays inside the `ε`-tube. -/
theorem nativePNT_exists_good_forward_dyadic
    (A K : ℕ) (ε : ℝ)
    (hA : 3 ≤ A) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlogA : 1 ≤ Real.log (A : ℝ))
    (htailA : 2200 ≤ ε * Real.log (A : ℝ))
    (hdownA : 1 < (ε / 4) * (2 * (A : ℝ) + 1))
    (hupA :
      Real.log ((A * 2 ^ K : ℕ) : ℝ) - 1 <
        (ε / 4) * (2 * (A : ℝ) + 1))
    (hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        (ε / 4) * ((K : ℝ) * Real.log 2 - 1)) :
    ∃ t ∈ Finset.Icc A (A * 2 ^ K),
      |nativePNTError t| ≤ ε * (t : ℝ) / 4 ∧
        ∀ h : ℕ, (h : ℝ) ≤ ε * (t : ℝ) / 8 →
          |nativePNTError (t + h)| ≤ ε * ((t + h : ℕ) : ℝ) := by
  have hδ : 0 < ε / 4 := by positivity
  rcases nativePNT_exists_small_error_dyadic_of_endpoint
      A K (ε / 4) (by omega) hδ hdownA hupA hdepth with
    ⟨t, ht, hsmall⟩
  have htA : A ≤ t := (Finset.mem_Icc.mp ht).1
  have ht3 : 3 ≤ t := hA.trans htA
  have hApos : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast (show 0 < A by omega)
  have htpos : (0 : ℝ) < (t : ℝ) := by
    exact_mod_cast (show 0 < t by omega)
  have hlogmono : Real.log (A : ℝ) ≤ Real.log (t : ℝ) := by
    apply Real.log_le_log
    · exact hApos
    · exact_mod_cast htA
  have hlogt : 1 ≤ Real.log (t : ℝ) := hlogA.trans hlogmono
  have htailt : 2200 ≤ ε * Real.log (t : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlogmono hε.le
    linarith
  have hsmall' : |nativePNTError t| ≤ ε * (t : ℝ) / 4 := by
    nlinarith [hsmall]
  refine ⟨t, ht, hsmall', ?_⟩
  intro h hh
  exact nativePNTError_good_forward_interval
    t h ε ht3 hε hε1 hlogt htailt hsmall' hh


/-! ## Sharp total reciprocal mass of the second Selberg kernel -/

private theorem nativeSelbergLinearConstant_le_182 :
    2 * (Real.log 4 + 2) + 172 ≤ (182 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  norm_num at h ⊢
  linarith

private theorem nativeLambdaTwoSummatory_upper_all (N : ℕ) :
    nativeLambdaTwoSummatory N ≤
      2 * (N : ℝ) * Real.log (N : ℝ) + 182 * (N : ℝ) + 600 := by
  by_cases hN3 : 3 ≤ N
  · have hsel := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le N hN3
    rw [abs_le] at hsel
    have hNR0 : 0 ≤ (N : ℝ) := by positivity
    have hC := nativeSelbergLinearConstant_le_182
    nlinarith [hsel.2, mul_le_mul_of_nonneg_right hC hNR0]
  · have hNle : N ≤ 2 := by omega
    have hsub := nativeLambdaTwoSummatory_sub_eq_interval N 3 (by omega)
    have hinterval0 :
        0 ≤ ∑ n ∈ Finset.Icc (N + 1) 3, nativeLambdaTwo n := by
      apply Finset.sum_nonneg
      intro n hn
      exact nativeLambdaTwo_nonneg n (by
        have hnI := Finset.mem_Icc.mp hn
        omega)
    have hmono : nativeLambdaTwoSummatory N ≤ nativeLambdaTwoSummatory 3 := by
      linarith [hsub]
    have h3 := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le 3 (by norm_num)
    rw [abs_le] at h3
    have hlog3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    have hC := nativeSelbergLinearConstant_le_182
    norm_num at hlog3
    have hC3 :
        (2 * (Real.log 4 + 2) + 172) * (3 : ℝ) ≤ 546 := by
      nlinarith
    have hlogpart : 2 * (3 : ℝ) * Real.log 3 ≤ 12 := by
      nlinarith
    have hrho3 : nativeLambdaTwoSummatory 3 ≤ 600 := by
      calc
        nativeLambdaTwoSummatory 3 ≤
            2 * (3 : ℝ) * Real.log 3 +
              (2 * (Real.log 4 + 2) + 172) * (3 : ℝ) := by
          have h := (sub_le_iff_le_add.mp h3.2)
          simpa [add_comm] using h
        _ ≤ 12 + 546 := add_le_add hlogpart hC3
        _ ≤ 600 := by norm_num
    have hlogN0 : 0 ≤ Real.log (N : ℝ) := by
      rcases Nat.eq_zero_or_pos N with rfl | hNpos
      · simp
      · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have hNR0 : 0 ≤ (N : ℝ) := by positivity
    nlinarith

private theorem nativeRecipDiff_eq
    (n : ℕ) (hn : 1 ≤ n) :
    1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)) =
      1 / ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hs0 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hn0, hs0]
  push_cast
  ring

private theorem nativeRecipDiffSum_eq
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N,
      (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) =
        1 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN, ih]
      push_cast
      ring

private theorem nativeLambdaTwoAbelPoint_upper
    (n : ℕ) (hn : 1 ≤ n) :
    nativeLambdaTwoSummatory n *
        (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ))) ≤
      2 * Real.log (n : ℝ) / (n : ℝ) + 182 / (n : ℝ) +
        600 * (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ))) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hspos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hk := nativeRecipDiff_eq n hn
  have hkernel0 :
      0 ≤ 1 / ((n : ℝ) * (((n + 1 : ℕ) : ℝ))) := by positivity
  have hrho := nativeLambdaTwoSummatory_upper_all n
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hlogfrac :
      2 * Real.log (n : ℝ) / (((n + 1 : ℕ) : ℝ)) ≤
        2 * Real.log (n : ℝ) / (n : ℝ) := by
    rw [div_le_div_iff₀ hspos hnpos]
    push_cast
    nlinarith
  have hconstfrac :
      (182 : ℝ) / (((n + 1 : ℕ) : ℝ)) ≤ 182 / (n : ℝ) := by
    rw [div_le_div_iff₀ hspos hnpos]
    push_cast
    nlinarith
  rw [hk]
  calc
    nativeLambdaTwoSummatory n *
        (1 / ((n : ℝ) * (((n + 1 : ℕ) : ℝ)))) ≤
      (2 * (n : ℝ) * Real.log (n : ℝ) + 182 * (n : ℝ) + 600) *
        (1 / ((n : ℝ) * (((n + 1 : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_right hrho hkernel0
    _ = 2 * Real.log (n : ℝ) / (((n + 1 : ℕ) : ℝ)) +
        182 / (((n + 1 : ℕ) : ℝ)) +
        600 * (1 / ((n : ℝ) * (((n + 1 : ℕ) : ℝ)))) := by
      field_simp [ne_of_gt hnpos, ne_of_gt hspos]
    _ ≤ 2 * Real.log (n : ℝ) / (n : ℝ) + 182 / (n : ℝ) +
        600 * (1 / ((n : ℝ) * (((n + 1 : ℕ) : ℝ)))) := by
      linarith

private theorem nativeLogRecipIco_le_mass
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N, Real.log (n : ℝ) / (n : ℝ)) ≤
      nativeLogRecipMass N := by
  unfold nativeLogRecipMass
  have hset : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext n
    simp
    omega
  rw [hset, Finset.sum_Ico_succ_top hN]
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  exact le_add_of_nonneg_right (div_nonneg hlog0 (by positivity))

private theorem nativeRecipIco_le_harmonic
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N, 1 / (n : ℝ)) ≤ (harmonic N : ℝ) := by
  have hharm :
      (harmonic N : ℝ) = ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hharm]
  have hset : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext n
    simp
    omega
  rw [hset, Finset.sum_Ico_succ_top hN]
  exact le_add_of_nonneg_right (by positivity)

/-- **Sharp reciprocal second-kernel upper bound.**  Finite Abel summation of
`rho(N) = 2 N log N + O(N)` preserves the leading coefficient `1`:

`sum_{n<=N} Lambda_2(n)/n <= log^2 N + O(log N)`.

The deliberately loose lower-order constants keep the proof robust while the
leading coefficient remains exact, which is the feature needed by the cubic
compensation argument. -/
theorem nativeLambdaTwoRecipMass_upper
    (N : ℕ) (hN : 3 ≤ N) :
    nativeLambdaTwoRecipMass N ≤
      (Real.log N) ^ 2 + 1000 * Real.log N + 2000 := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  have hsel := nativeLambdaTwoSummatory_sub_two_mul_log_abs_le N hN
  rw [abs_le] at hsel
  have hC := nativeSelbergLinearConstant_le_182
  have hendpoint :
      nativeLambdaTwoSummatory N / (N : ℝ) ≤ 2 * Real.log N + 182 := by
    rw [div_le_iff₀ hNpos]
    have hCR := mul_le_mul_of_nonneg_right hC (show 0 ≤ (N : ℝ) by positivity)
    nlinarith [hsel.2]
  have hinterior0 :
      (∑ n ∈ Finset.Ico 1 N,
        nativeLambdaTwoSummatory n *
          (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) ≤
        ∑ n ∈ Finset.Ico 1 N,
          (2 * Real.log (n : ℝ) / (n : ℝ) + 182 / (n : ℝ) +
            600 * (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) := by
    apply Finset.sum_le_sum
    intro n hnmem
    exact nativeLambdaTwoAbelPoint_upper n (Finset.mem_Ico.mp hnmem).1
  have hinterior :
      (∑ n ∈ Finset.Ico 1 N,
        nativeLambdaTwoSummatory n *
          (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) ≤
        2 * nativeLogRecipMass N + 182 * (harmonic N : ℝ) + 600 := by
    have hlogsum := nativeLogRecipIco_le_mass N hN1
    have hrecipsum := nativeRecipIco_le_harmonic N hN1
    have hkernelEq := nativeRecipDiffSum_eq N hN1
    have hkernelLe :
        (∑ n ∈ Finset.Ico 1 N,
          (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) ≤ 1 := by
      rw [hkernelEq]
      have hrecip0 : 0 ≤ 1 / (N : ℝ) := by positivity
      linarith
    have hlogScale :
        (∑ n ∈ Finset.Ico 1 N, 2 * Real.log (n : ℝ) / (n : ℝ)) =
          2 * (∑ n ∈ Finset.Ico 1 N, Real.log (n : ℝ) / (n : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    have hrecipScale :
        (∑ n ∈ Finset.Ico 1 N, 182 / (n : ℝ)) =
          182 * (∑ n ∈ Finset.Ico 1 N, 1 / (n : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    have hkernelScale :
        (∑ n ∈ Finset.Ico 1 N,
          600 * (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) =
          600 * (∑ n ∈ Finset.Ico 1 N,
            (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) := by
      rw [Finset.mul_sum]
    calc
      (∑ n ∈ Finset.Ico 1 N,
        nativeLambdaTwoSummatory n *
          (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) ≤
          ∑ n ∈ Finset.Ico 1 N,
            (2 * Real.log (n : ℝ) / (n : ℝ) + 182 / (n : ℝ) +
              600 * (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) :=
        hinterior0
      _ = 2 * (∑ n ∈ Finset.Ico 1 N, Real.log (n : ℝ) / (n : ℝ)) +
          182 * (∑ n ∈ Finset.Ico 1 N, 1 / (n : ℝ)) +
          600 * (∑ n ∈ Finset.Ico 1 N,
            (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ)))) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          hlogScale, hrecipScale, hkernelScale]
      _ ≤ 2 * nativeLogRecipMass N + 182 * (harmonic N : ℝ) + 600 * 1 := by
        gcongr
      _ = 2 * nativeLogRecipMass N + 182 * (harmonic N : ℝ) + 600 := by ring
  have hdef := nativeLogRecipDefect_abs_le_four N hN
  rw [abs_le] at hdef
  unfold nativeLogRecipDefect at hdef
  have hJ :
      nativeLogRecipMass N ≤ (1 / 2 : ℝ) * (Real.log N) ^ 2 + 4 := by
    linarith [hdef.2]
  have hH := harmonic_le_one_add_log N
  rw [nativeLambdaTwoRecipMass_abel]
  calc
    nativeLambdaTwoSummatory N / (N : ℝ) +
        ∑ n ∈ Finset.Ico 1 N,
          nativeLambdaTwoSummatory n *
            (1 / (n : ℝ) - 1 / (((n + 1 : ℕ) : ℝ))) ≤
      (2 * Real.log N + 182) +
        (2 * nativeLogRecipMass N + 182 * (harmonic N : ℝ) + 600) :=
      add_le_add hendpoint hinterior
    _ ≤ (2 * Real.log N + 182) +
        (2 * ((1 / 2 : ℝ) * (Real.log N) ^ 2 + 4) +
          182 * (1 + Real.log N) + 600) := by
      gcongr
    _ ≤ (Real.log N) ^ 2 + 1000 * Real.log N + 2000 := by
      nlinarith


/-! ## Good-fibre compensation -/

/-- Fibres on which the normalized Chebyshev error is at most `beta`. -/
def nativePNTGoodFiberSet (N : ℕ) (beta : ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n =>
    |nativePNTError (N / n)| ≤ beta * ((N : ℝ) / (n : ℝ)))

/-- Reciprocal second-kernel mass carried by the good fibres. -/
def nativeLambdaTwoGoodRecipMass (N : ℕ) (beta : ℝ) : ℝ :=
  ∑ n ∈ nativePNTGoodFiberSet N beta, nativeLambdaTwo n / (n : ℝ)

/-- The good reciprocal mass is nonnegative. -/
theorem nativeLambdaTwoGoodRecipMass_nonneg (N : ℕ) (beta : ℝ) :
    0 ≤ nativeLambdaTwoGoodRecipMass N beta := by
  unfold nativeLambdaTwoGoodRecipMass nativePNTGoodFiberSet
  apply Finset.sum_nonneg
  intro n hn
  have hnI := (Finset.mem_filter.mp hn).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
  exact div_nonneg (nativeLambdaTwo_nonneg n hn1) (by positivity)

/-- The good set is contained in the positive endpoint range. -/
theorem nativePNTGoodFiberSet_subset (N : ℕ) (beta : ℝ) :
    nativePNTGoodFiberSet N beta ⊆ Finset.Icc 1 N := by
  intro n hn
  exact (Finset.mem_filter.mp hn).1

private theorem nativeLambdaTwoRecipSplit
    (N : ℕ) (beta : ℝ) :
    nativeLambdaTwoGoodRecipMass N beta +
      (∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => ¬ |nativePNTError (N / n)| ≤
          beta * ((N : ℝ) / (n : ℝ))),
        nativeLambdaTwo n / (n : ℝ)) =
      nativeLambdaTwoRecipMass N := by
  unfold nativeLambdaTwoGoodRecipMass nativePNTGoodFiberSet
    nativeLambdaTwoRecipMass
  exact Finset.sum_filter_add_sum_filter_not
    (s := Finset.Icc 1 N)
    (p := fun n => |nativePNTError (N / n)| ≤
      beta * ((N : ℝ) / (n : ℝ)))
    (f := fun n => nativeLambdaTwo n / (n : ℝ))

private theorem nativeLambdaTwoMassSplit
    (N : ℕ) (beta : ℝ) :
    (∑ n ∈ nativePNTGoodFiberSet N beta, nativeLambdaTwo n) +
      (∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => ¬ |nativePNTError (N / n)| ≤
          beta * ((N : ℝ) / (n : ℝ))),
        nativeLambdaTwo n) = nativeLambdaTwoSummatory N := by
  unfold nativePNTGoodFiberSet nativeLambdaTwoSummatory
  exact Finset.sum_filter_add_sum_filter_not
    (s := Finset.Icc 1 N)
    (p := fun n => |nativePNTError (N / n)| ≤
      beta * ((N : ℝ) / (n : ℝ)))
    (f := fun n => nativeLambdaTwo n)

/-- **Good-fibre compensation identity.**  If every reciprocal fibre obeys an
`alpha` envelope up to an additive constant `D`, then fibres already inside a
smaller `beta` envelope subtract their reciprocal `LambdaTwo` mass from the
worst-case bound:

`errorMass <= alpha*N*S2 - (alpha-beta)*N*goodMass + D*rho`.

This is the exact algebraic deficit used by the Erdos cubic improvement. -/
theorem nativeLambdaTwoErrorMass_compensation
    (N : ℕ) (alpha beta D : ℝ)
    (_halpha : 0 ≤ alpha) (_hbeta : 0 ≤ beta) (_hba : beta ≤ alpha)
    (hD : 0 ≤ D)
    (hall : ∀ n ∈ Finset.Icc 1 N,
      |nativePNTError (N / n)| ≤ alpha * ((N : ℝ) / (n : ℝ)) + D) :
    nativeLambdaTwoErrorMass N ≤
      alpha * (N : ℝ) * nativeLambdaTwoRecipMass N -
        (alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta +
        D * nativeLambdaTwoSummatory N := by
  let p : ℕ → Prop := fun n =>
    |nativePNTError (N / n)| ≤ beta * ((N : ℝ) / (n : ℝ))
  let G := (Finset.Icc 1 N).filter p
  let B := (Finset.Icc 1 N).filter (fun n => ¬ p n)
  have hsplit :
      nativeLambdaTwoErrorMass N =
        (∑ n ∈ G, nativeLambdaTwo n * |nativePNTError (N / n)|) +
          ∑ n ∈ B, nativeLambdaTwo n * |nativePNTError (N / n)| := by
    unfold nativeLambdaTwoErrorMass
    dsimp [G, B]
    rw [Finset.sum_filter_add_sum_filter_not]
  have hgood :
      (∑ n ∈ G, nativeLambdaTwo n * |nativePNTError (N / n)|) ≤
        ∑ n ∈ G, nativeLambdaTwo n *
          (beta * ((N : ℝ) / (n : ℝ)) + D) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnF := Finset.mem_filter.mp hn
    have hnI := hnF.1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hp : |nativePNTError (N / n)| ≤
        beta * ((N : ℝ) / (n : ℝ)) := hnF.2
    have hpD : |nativePNTError (N / n)| ≤
        beta * ((N : ℝ) / (n : ℝ)) + D :=
      hp.trans (le_add_of_nonneg_right hD)
    exact mul_le_mul_of_nonneg_left hpD (nativeLambdaTwo_nonneg n hn1)
  have hbad :
      (∑ n ∈ B, nativeLambdaTwo n * |nativePNTError (N / n)|) ≤
        ∑ n ∈ B, nativeLambdaTwo n *
          (alpha * ((N : ℝ) / (n : ℝ)) + D) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnF := Finset.mem_filter.mp hn
    have hnI := hnF.1
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    exact mul_le_mul_of_nonneg_left (hall n hnI)
      (nativeLambdaTwo_nonneg n hn1)
  have hbound :
      nativeLambdaTwoErrorMass N ≤
        (∑ n ∈ G, nativeLambdaTwo n *
          (beta * ((N : ℝ) / (n : ℝ)) + D)) +
        ∑ n ∈ B, nativeLambdaTwo n *
          (alpha * ((N : ℝ) / (n : ℝ)) + D) := by
    rw [hsplit]
    exact add_le_add hgood hbad
  have hGrec :
      (∑ n ∈ G, nativeLambdaTwo n * ((N : ℝ) / (n : ℝ))) =
        (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta := by
    dsimp [G, p]
    unfold nativeLambdaTwoGoodRecipMass nativePNTGoodFiberSet
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  have hBrec :
      (∑ n ∈ B, nativeLambdaTwo n * ((N : ℝ) / (n : ℝ))) =
        (N : ℝ) *
          (∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => ¬ |nativePNTError (N / n)| ≤
              beta * ((N : ℝ) / (n : ℝ))),
            nativeLambdaTwo n / (n : ℝ)) := by
    dsimp [B, p]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  have hGmass :
      (∑ n ∈ G, nativeLambdaTwo n) =
        ∑ n ∈ nativePNTGoodFiberSet N beta, nativeLambdaTwo n := by
    rfl
  have hBmass :
      (∑ n ∈ B, nativeLambdaTwo n) =
        ∑ n ∈ (Finset.Icc 1 N).filter
          (fun n => ¬ |nativePNTError (N / n)| ≤
            beta * ((N : ℝ) / (n : ℝ))), nativeLambdaTwo n := by
    rfl
  have hGexpand :
      (∑ n ∈ G, nativeLambdaTwo n *
        (beta * ((N : ℝ) / (n : ℝ)) + D)) =
        beta * ((N : ℝ) * nativeLambdaTwoGoodRecipMass N beta) +
          D * (∑ n ∈ nativePNTGoodFiberSet N beta, nativeLambdaTwo n) := by
    calc
      (∑ n ∈ G, nativeLambdaTwo n *
        (beta * ((N : ℝ) / (n : ℝ)) + D)) =
          (∑ n ∈ G,
            beta * (nativeLambdaTwo n * ((N : ℝ) / (n : ℝ)))) +
          ∑ n ∈ G, D * nativeLambdaTwo n := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ = beta * (∑ n ∈ G,
            nativeLambdaTwo n * ((N : ℝ) / (n : ℝ))) +
          D * (∑ n ∈ G, nativeLambdaTwo n) := by
        rw [Finset.mul_sum, Finset.mul_sum]
      _ = _ := by rw [hGrec, hGmass]
  have hBexpand :
      (∑ n ∈ B, nativeLambdaTwo n *
        (alpha * ((N : ℝ) / (n : ℝ)) + D)) =
        alpha * ((N : ℝ) *
          (∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => ¬ |nativePNTError (N / n)| ≤
              beta * ((N : ℝ) / (n : ℝ))),
            nativeLambdaTwo n / (n : ℝ))) +
          D * (∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => ¬ |nativePNTError (N / n)| ≤
              beta * ((N : ℝ) / (n : ℝ))), nativeLambdaTwo n) := by
    calc
      (∑ n ∈ B, nativeLambdaTwo n *
        (alpha * ((N : ℝ) / (n : ℝ)) + D)) =
          (∑ n ∈ B,
            alpha * (nativeLambdaTwo n * ((N : ℝ) / (n : ℝ)))) +
          ∑ n ∈ B, D * nativeLambdaTwo n := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
      _ = alpha * (∑ n ∈ B,
            nativeLambdaTwo n * ((N : ℝ) / (n : ℝ))) +
          D * (∑ n ∈ B, nativeLambdaTwo n) := by
        rw [Finset.mul_sum, Finset.mul_sum]
      _ = _ := by rw [hBrec, hBmass]
  rw [hGexpand, hBexpand] at hbound
  have hrecSplit := nativeLambdaTwoRecipSplit N beta
  have hmassSplit := nativeLambdaTwoMassSplit N beta
  calc
    nativeLambdaTwoErrorMass N ≤
        beta * ((N : ℝ) * nativeLambdaTwoGoodRecipMass N beta) +
          D * (∑ n ∈ nativePNTGoodFiberSet N beta, nativeLambdaTwo n) +
          (alpha * ((N : ℝ) *
            (∑ n ∈ (Finset.Icc 1 N).filter
              (fun n => ¬ |nativePNTError (N / n)| ≤
                beta * ((N : ℝ) / (n : ℝ))),
              nativeLambdaTwo n / (n : ℝ))) +
            D * (∑ n ∈ (Finset.Icc 1 N).filter
              (fun n => ¬ |nativePNTError (N / n)| ≤
                beta * ((N : ℝ) / (n : ℝ))), nativeLambdaTwo n)) := hbound
    _ = alpha * (N : ℝ) * nativeLambdaTwoRecipMass N -
        (alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta +
        D * nativeLambdaTwoSummatory N := by
      rw [← hrecSplit, ← hmassSplit]
      ring


/-! ## Reciprocal quotient geometry for good fibres -/

/-- The integer reciprocal interval

`N / (t + H + 1) < n <= N / t`

is exactly a block of divisor coordinates whose quotient `N / n` lies in the
forward interval `[t, t + H]`.  This is the finite floor geometry needed to
transport a PNT2 good interval into the `Lambda_2` compensation sum. -/
theorem nativePNT_quotient_mem_of_reciprocal_interval
    (N t H n : ℕ) (ht : 1 ≤ t)
    (hn : n ∈ Finset.Icc (N / (t + H + 1) + 1) (N / t)) :
    t ≤ N / n ∧ N / n ≤ t + H := by
  have hnI := Finset.mem_Icc.mp hn
  have hnpos : 0 < n :=
    lt_of_lt_of_le (Nat.zero_lt_succ (N / (t + H + 1))) hnI.1
  have hdenpos : 0 < t + H + 1 := by omega
  have hlower : N / (t + H + 1) < n := by omega
  have hNlt : N < n * (t + H + 1) :=
    (Nat.div_lt_iff_lt_mul hdenpos).1 hlower
  have hquotUpper : N / n < t + H + 1 := by
    apply (Nat.div_lt_iff_lt_mul hnpos).2
    simpa [Nat.mul_comm] using hNlt
  have htpos : 0 < t := by omega
  have htn : t * n ≤ N := by
    have h := (Nat.le_div_iff_mul_le htpos).1 hnI.2
    simpa [Nat.mul_comm] using h
  have hquotLower : t ≤ N / n :=
    (Nat.le_div_iff_mul_le hnpos).2 htn
  exact ⟨hquotLower, Nat.lt_succ_iff.mp hquotUpper⟩

/-- A good forward interval in the quotient variable becomes a whole reciprocal
block of good fibres for the second-Selberg compensation sum. -/
theorem nativePNT_reciprocal_interval_subset_good
    (N t H : ℕ) (beta : ℝ)
    (ht : 1 ≤ t) (hbeta : 0 ≤ beta)
    (hgood : ∀ q ∈ Finset.Icc t (t + H),
      |nativePNTError q| ≤ beta * (q : ℝ)) :
    Finset.Icc (N / (t + H + 1) + 1) (N / t) ⊆
      nativePNTGoodFiberSet N beta := by
  intro n hn
  have hq := nativePNT_quotient_mem_of_reciprocal_interval N t H n ht hn
  have hqmem : N / n ∈ Finset.Icc t (t + H) :=
    Finset.mem_Icc.mpr hq
  have herr := hgood (N / n) hqmem
  have hnI := Finset.mem_Icc.mp hn
  have hnpos : 0 < n :=
    lt_of_lt_of_le (Nat.zero_lt_succ (N / (t + H + 1))) hnI.1
  have hn1 : 1 ≤ n := Nat.succ_le_iff.mpr hnpos
  have hnN : n ≤ N :=
    hnI.2.trans (Nat.div_le_self N t)
  have hnposR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnpos
  have hfloor : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / (n : ℝ) := by
    rw [le_div_iff₀ hnposR]
    exact_mod_cast Nat.div_mul_le_self N n
  have hscale :
      beta * ((N / n : ℕ) : ℝ) ≤ beta * ((N : ℝ) / (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hfloor hbeta
  unfold nativePNTGoodFiberSet
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, herr.trans hscale⟩

/-- **One PNT2 interval contributes a positive block of good reciprocal
`Lambda_2` mass.**  The lower bound is the already-proved Selberg main term on
the reciprocal interval.  This is the local building block for the geometric
packing that yields the cubic gain. -/
theorem nativeLambdaTwoGoodRecipMass_of_good_quotient_interval
    (N t H : ℕ) (beta : ℝ)
    (ht : 1 ≤ t) (hbeta : 0 ≤ beta)
    (hA : 3 ≤ N / (t + H + 1))
    (hAB : N / (t + H + 1) ≤ N / t)
    (hgood : ∀ q ∈ Finset.Icc t (t + H),
      |nativePNTError q| ≤ beta * (q : ℝ)) :
    (2 * ((N / t : ℕ) : ℝ) * Real.log ((N / t : ℕ) : ℝ) -
        2 * ((N / (t + H + 1) : ℕ) : ℝ) *
          Real.log ((N / (t + H + 1) : ℕ) : ℝ) -
        (2 * (Real.log 4 + 2) + 172) *
          (((N / (t + H + 1) : ℕ) : ℝ) + ((N / t : ℕ) : ℝ))) /
        ((N / t : ℕ) : ℝ) ≤
      nativeLambdaTwoGoodRecipMass N beta := by
  have hmain := nativeLambdaTwoRecipIntervalMass_main_lower
    (N / (t + H + 1)) (N / t) hA hAB
  have hsubset := nativePNT_reciprocal_interval_subset_good
    N t H beta ht hbeta hgood
  have hmass :
      nativeLambdaTwoRecipIntervalMass (N / (t + H + 1)) (N / t) ≤
        nativeLambdaTwoGoodRecipMass N beta := by
    unfold nativeLambdaTwoRecipIntervalMass nativeLambdaTwoGoodRecipMass
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro n hn _hnold
    have hnI := nativePNTGoodFiberSet_subset N beta hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    exact div_nonneg (nativeLambdaTwo_nonneg n hn1) (by positivity)
  exact hmain.trans hmass


/-! ## Disjoint good-fibre packing -/

/-- The reciprocal `Lambda_2` mass of a quotient-good interval is itself
bounded by the total good-fibre mass. -/
theorem nativeLambdaTwoRecipIntervalMass_le_good_of_good_quotient_interval
    (N t H : ℕ) (beta : ℝ)
    (ht : 1 ≤ t) (hbeta : 0 ≤ beta)
    (hgood : ∀ q ∈ Finset.Icc t (t + H),
      |nativePNTError q| ≤ beta * (q : ℝ)) :
    nativeLambdaTwoRecipIntervalMass (N / (t + H + 1)) (N / t) ≤
      nativeLambdaTwoGoodRecipMass N beta := by
  have hsubset := nativePNT_reciprocal_interval_subset_good
    N t H beta ht hbeta hgood
  unfold nativeLambdaTwoRecipIntervalMass nativeLambdaTwoGoodRecipMass
  refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
  intro n hn _hnold
  have hnI := nativePNTGoodFiberSet_subset N beta hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
  exact div_nonneg (nativeLambdaTwo_nonneg n hn1) (by positivity)

/-- Separated quotient intervals produce disjoint reciprocal divisor blocks.
The reversal of order under `n ↦ N / n` is handled exactly at the integer
floor level. -/
theorem nativePNT_reciprocal_blocks_disjoint
    (N t₁ H₁ t₂ H₂ : ℕ)
    (hsep : t₁ + H₁ < t₂) :
    Disjoint
      (Finset.Icc (N / (t₁ + H₁ + 1) + 1) (N / t₁))
      (Finset.Icc (N / (t₂ + H₂ + 1) + 1) (N / t₂)) := by
  rw [Finset.disjoint_left]
  intro n hn₁ hn₂
  have hI₁ := Finset.mem_Icc.mp hn₁
  have hI₂ := Finset.mem_Icc.mp hn₂
  have hden : t₁ + H₁ + 1 ≤ t₂ := by omega
  have hmono : N / t₂ ≤ N / (t₁ + H₁ + 1) :=
    Nat.div_le_div_left hden (by omega)
  omega

/-- Pairwise disjoint blocks contained in the good-fibre set contribute their
masses additively.  This theorem isolates all finite-union bookkeeping from the
number-theoretic construction of the blocks. -/
theorem nativeLambdaTwoGoodRecipMass_packed_blocks
    (N J : ℕ) (beta : ℝ) (block : ℕ → Finset ℕ)
    (hsub : ∀ j < J, block j ⊆ nativePNTGoodFiberSet N beta)
    (hdisj : ∀ i < J, ∀ j < J, i ≠ j → Disjoint (block i) (block j)) :
    (∑ j ∈ Finset.range J,
      ∑ n ∈ block j, nativeLambdaTwo n / (n : ℝ)) ≤
      nativeLambdaTwoGoodRecipMass N beta := by
  have hUnionSubset :
      (Finset.range J).biUnion block ⊆ nativePNTGoodFiberSet N beta := by
    intro n hn
    rcases Finset.mem_biUnion.mp hn with ⟨j, hj, hnj⟩
    exact hsub j (Finset.mem_range.mp hj) hnj
  have hsumUnion :
      (∑ n ∈ (Finset.range J).biUnion block,
        nativeLambdaTwo n / (n : ℝ)) =
        ∑ j ∈ Finset.range J,
          ∑ n ∈ block j, nativeLambdaTwo n / (n : ℝ) := by
    rw [Finset.sum_biUnion]
    intro i hi j hj hij
    exact hdisj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
  unfold nativeLambdaTwoGoodRecipMass
  rw [← hsumUnion]
  refine Finset.sum_le_sum_of_subset_of_nonneg hUnionSubset ?_
  intro n hn _hnold
  have hnI := nativePNTGoodFiberSet_subset N beta hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
  exact div_nonneg (nativeLambdaTwo_nonneg n hn1) (by positivity)

/-- A relative gap between `A` and `B` turns the Selberg main term into a clean
positive reciprocal-mass lower bound.  The logarithmic size hypothesis absorbs
all linear-error constants:

`A ≤ (1-eta) B` and `2 C ≤ eta log B` imply
`eta log B ≤ sum_{A<n≤B} Lambda_2(n)/n`. -/
theorem nativeLambdaTwoRecipIntervalMass_gap_lower
    (A B : ℕ) (eta : ℝ)
    (hA : 3 ≤ A) (hAB : A ≤ B)
    (hgap : (A : ℝ) ≤ (1 - eta) * (B : ℝ))
    (hlog :
      2 * (2 * (Real.log 4 + 2) + 172) ≤
        eta * Real.log (B : ℝ)) :
    eta * Real.log (B : ℝ) ≤
      nativeLambdaTwoRecipIntervalMass A B := by
  have hmain := nativeLambdaTwoRecipIntervalMass_main_lower A B hA hAB
  have hApos : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast (show 0 < A by omega)
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (show 0 < B by omega)
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := by positivity
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := by positivity
  have hABR : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
  have hlogAB : Real.log (A : ℝ) ≤ Real.log (B : ℝ) := by
    exact Real.log_le_log hApos hABR
  have hAlog :
      (A : ℝ) * Real.log (A : ℝ) ≤
        (A : ℝ) * Real.log (B : ℝ) :=
    mul_le_mul_of_nonneg_left hlogAB hA0
  have hsum : (A : ℝ) + (B : ℝ) ≤ 2 * (B : ℝ) := by
    linarith
  have hgapdiff :
      eta * (B : ℝ) ≤ (B : ℝ) - (A : ℝ) := by
    nlinarith [hgap]
  have hlogB0 : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have hgaplog := mul_le_mul_of_nonneg_right hgapdiff hlogB0
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hC0 : 0 ≤ 2 * (Real.log 4 + 2) + 172 := by nlinarith
  have hCsum := mul_le_mul_of_nonneg_left hsum hC0
  have hCmul := mul_le_mul_of_nonneg_right hlog hB0
  have hnum :
      eta * Real.log (B : ℝ) * (B : ℝ) ≤
        2 * (B : ℝ) * Real.log (B : ℝ) -
          2 * (A : ℝ) * Real.log (A : ℝ) -
          (2 * (Real.log 4 + 2) + 172) *
            ((A : ℝ) + (B : ℝ)) := by
    nlinarith [hAlog, hgaplog, hCsum, hCmul]
  have hfrac :
      eta * Real.log (B : ℝ) ≤
        (2 * (B : ℝ) * Real.log (B : ℝ) -
          2 * (A : ℝ) * Real.log (A : ℝ) -
          (2 * (Real.log 4 + 2) + 172) *
            ((A : ℝ) + (B : ℝ))) / (B : ℝ) := by
    rw [le_div_iff₀ hBpos]
    exact hnum
  exact hfrac.trans hmain


/-! ## Integer good radii and quotient-block packing -/

/-- Integer radius corresponding to the PNT2 forward interval `h <= eps*t/8`. -/
def nativePNTGoodForwardRadius (t : ℕ) (eps : ℝ) : ℕ :=
  ⌊eps * (t : ℝ) / 8⌋₊

/-- The integer radius stays below the real PNT2 radius. -/
theorem nativePNTGoodForwardRadius_cast_le
    (t : ℕ) (eps : ℝ) (heps : 0 ≤ eps) :
    ((nativePNTGoodForwardRadius t eps : ℕ) : ℝ) ≤
      eps * (t : ℝ) / 8 := by
  unfold nativePNTGoodForwardRadius
  exact Nat.floor_le (by positivity)

/-- For `eps <= 1`, the good radius is at most the base point.  This is the
coarse separation estimate used between consecutive geometric search blocks. -/
theorem nativePNTGoodForwardRadius_le_self
    (t : ℕ) (eps : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1) :
    nativePNTGoodForwardRadius t eps ≤ t := by
  have hr := nativePNTGoodForwardRadius_cast_le t eps heps
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := by positivity
  have hreal : eps * (t : ℝ) / 8 ≤ (t : ℝ) := by
    nlinarith
  have hcast : ((nativePNTGoodForwardRadius t eps : ℕ) : ℝ) ≤ (t : ℝ) :=
    hr.trans hreal
  exact_mod_cast hcast

/-- PNT2 expressed as an ordinary integer interval rather than a displacement
bound. -/
theorem nativePNTError_good_on_forward_radius
    (t : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (hforward : ∀ h : ℕ, (h : ℝ) ≤ eps * (t : ℝ) / 8 →
      |nativePNTError (t + h)| ≤ eps * ((t + h : ℕ) : ℝ)) :
    ∀ q ∈ Finset.Icc t (t + nativePNTGoodForwardRadius t eps),
      |nativePNTError q| ≤ eps * (q : ℝ) := by
  intro q hq
  have hqI := Finset.mem_Icc.mp hq
  let h := q - t
  have hhR : h ≤ nativePNTGoodForwardRadius t eps := by
    dsimp [h]
    omega
  have hhCast : (h : ℝ) ≤
      ((nativePNTGoodForwardRadius t eps : ℕ) : ℝ) := by
    exact_mod_cast hhR
  have hh : (h : ℝ) ≤ eps * (t : ℝ) / 8 :=
    hhCast.trans (nativePNTGoodForwardRadius_cast_le t eps heps)
  have heq : t + h = q := by
    dsimp [h]
    omega
  simpa [heq] using hforward h hh

/-- The combined PNT1/PNT2 theorem with its forward radius discretized. -/
theorem nativePNT_exists_good_radius_dyadic
    (A K : ℕ) (eps : ℝ)
    (hA : 3 ≤ A) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hlogA : 1 ≤ Real.log (A : ℝ))
    (htailA : 2200 ≤ eps * Real.log (A : ℝ))
    (hdownA : 1 < (eps / 4) * (2 * (A : ℝ) + 1))
    (hupA :
      Real.log ((A * 2 ^ K : ℕ) : ℝ) - 1 <
        (eps / 4) * (2 * (A : ℝ) + 1))
    (hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        (eps / 4) * ((K : ℝ) * Real.log 2 - 1)) :
    ∃ t ∈ Finset.Icc A (A * 2 ^ K),
      |nativePNTError t| ≤ eps * (t : ℝ) / 4 ∧
        ∀ q ∈ Finset.Icc t (t + nativePNTGoodForwardRadius t eps),
          |nativePNTError q| ≤ eps * (q : ℝ) := by
  rcases nativePNT_exists_good_forward_dyadic
      A K eps hA heps heps1 hlogA htailA hdownA hupA hdepth with
    ⟨t, ht, hsmall, hforward⟩
  refine ⟨t, ht, hsmall, ?_⟩
  exact nativePNTError_good_on_forward_radius t eps heps.le hforward

/-- A separated family of good quotient intervals contributes the sum of all
its reciprocal `Lambda_2` block masses to the good-fibre compensation term. -/
theorem nativeLambdaTwoGoodRecipMass_packed_quotient_intervals
    (N J : ℕ) (beta : ℝ) (t H : ℕ → ℕ)
    (hbeta : 0 ≤ beta)
    (ht : ∀ j < J, 1 ≤ t j)
    (hgood : ∀ j < J, ∀ q ∈ Finset.Icc (t j) (t j + H j),
      |nativePNTError q| ≤ beta * (q : ℝ))
    (hsep : ∀ i j, i < j → j < J → t i + H i < t j) :
    (∑ j ∈ Finset.range J,
      nativeLambdaTwoRecipIntervalMass
        (N / (t j + H j + 1)) (N / t j)) ≤
      nativeLambdaTwoGoodRecipMass N beta := by
  let block : ℕ → Finset ℕ := fun j =>
    Finset.Icc (N / (t j + H j + 1) + 1) (N / t j)
  have hsub : ∀ j < J, block j ⊆ nativePNTGoodFiberSet N beta := by
    intro j hj
    dsimp [block]
    exact nativePNT_reciprocal_interval_subset_good
      N (t j) (H j) beta (ht j hj) hbeta (hgood j hj)
  have hdisj : ∀ i < J, ∀ j < J, i ≠ j → Disjoint (block i) (block j) := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · dsimp [block]
      exact nativePNT_reciprocal_blocks_disjoint
        N (t i) (H i) (t j) (H j) (hsep i j hijlt hj)
    · dsimp [block]
      exact (nativePNT_reciprocal_blocks_disjoint
        N (t j) (H j) (t i) (H i) (hsep j i hjilt hi)).symm
  have hpacked := nativeLambdaTwoGoodRecipMass_packed_blocks
    N J beta block hsub hdisj
  simpa [block, nativeLambdaTwoRecipIntervalMass] using hpacked


/-! ## Affine envelopes and the compensated squared recurrence -/

/-- An affine global envelope for the Chebyshev error.  The additive constant
is allowed to depend on the coefficient; this is exactly what is needed when
the cubic improvement is iterated and then read at infinity. -/
def nativePNTHasAffineEnvelope (alpha : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ,
    |nativePNTError N| ≤ alpha * (N : ℝ) + D

/-- The elementary Chebyshev bound supplies the starting affine coefficient
`6`. -/
theorem nativePNTHasAffineEnvelope_six :
    nativePNTHasAffineEnvelope 6 := by
  refine ⟨0, le_rfl, ?_⟩
  intro N
  have herr := nativePNTError_abs_le_const_mul N
  have hlog4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  have hC : Real.log 4 + 3 ≤ (6 : ℝ) := by
    norm_num at hlog4 ⊢
    linarith
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hC hN0
  simpa using herr.trans hmul

/-- An affine endpoint envelope automatically controls every reciprocal fibre
in the real `N/n` normalization used by the compensation identity. -/
theorem nativePNTAffineEnvelope_on_fiber
    (alpha D : ℝ) (halpha : 0 ≤ alpha)
    (henv : ∀ q : ℕ, |nativePNTError q| ≤ alpha * (q : ℝ) + D)
    (N n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    |nativePNTError (N / n)| ≤
      alpha * ((N : ℝ) / (n : ℝ)) + D := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hfloor : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / (n : ℝ) := by
    rw [le_div_iff₀ hnpos]
    exact_mod_cast Nat.div_mul_le_self N n
  have hscale := mul_le_mul_of_nonneg_left hfloor halpha
  exact (henv (N / n)).trans (add_le_add_right hscale D)

/-- **Compensated squared Selberg recurrence.**  This is the quantitative
interface between an affine error envelope and the good-fibre packing.  The
leading reciprocal `Lambda_2` coefficient is exactly `1`; all lower-order
terms are displayed explicitly. -/
theorem nativePNTError_abs_log_sq_le_affine_compensated
    (N : ℕ) (hN : 3 ≤ N)
    (alpha beta D : ℝ)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hba : beta ≤ alpha)
    (hD : 0 ≤ D)
    (henv : ∀ q : ℕ,
      |nativePNTError q| ≤ alpha * (q : ℝ) + D) :
    |nativePNTError N| * (Real.log N) ^ 2 ≤
      alpha * (N : ℝ) *
          ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) -
        (alpha - beta) * (N : ℝ) *
          nativeLambdaTwoGoodRecipMass N beta +
        D * (2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600) +
        3000 * (N : ℝ) * Real.log N := by
  have hall : ∀ n ∈ Finset.Icc 1 N,
      |nativePNTError (N / n)| ≤
        alpha * ((N : ℝ) / (n : ℝ)) + D := by
    intro n hn
    exact nativePNTAffineEnvelope_on_fiber alpha D halpha henv N n hn
  have hsq := nativePNTError_abs_log_sq_le_lambdaTwo N hN
  have hcomp := nativeLambdaTwoErrorMass_compensation
    N alpha beta D halpha hbeta hba hD hall
  have hrec := nativeLambdaTwoRecipMass_upper N hN
  have hrho := nativeLambdaTwoSummatory_upper_all N
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hrecMul :
      alpha * (N : ℝ) * nativeLambdaTwoRecipMass N ≤
        alpha * (N : ℝ) *
          ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) := by
    exact mul_le_mul_of_nonneg_left hrec (mul_nonneg halpha hN0)
  have hrhoMul :
      D * nativeLambdaTwoSummatory N ≤
        D * (2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600) :=
    mul_le_mul_of_nonneg_left hrho hD
  have hmass :
      nativeLambdaTwoErrorMass N ≤
        alpha * (N : ℝ) *
            ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) -
          (alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodRecipMass N beta +
          D * (2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600) := by
    exact hcomp.trans
      (add_le_add
        (sub_le_sub_right hrecMul
          ((alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta))
        hrhoMul)
  calc
    |nativePNTError N| * (Real.log N) ^ 2 ≤
        nativeLambdaTwoErrorMass N +
          3000 * (N : ℝ) * Real.log N := hsq
    _ ≤
        (alpha * (N : ℝ) *
            ((Real.log N) ^ 2 + 1000 * Real.log N + 2000) -
          (alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodRecipMass N beta +
          D * (2 * (N : ℝ) * Real.log N + 182 * (N : ℝ) + 600)) +
          3000 * (N : ℝ) * Real.log N :=
      add_le_add_right hmass _
    _ = _ := by ring


/-- **Strict affine-envelope improvement from positive good-fibre density.**
For a fixed `beta < alpha`, any positive quadratic-in-`log N` lower density of
good reciprocal `Lambda_2` fibres subtracts a fixed amount from the admissible
linear slope.  No uniform cubic constant is required: the lower-order terms in
the compensated squared recurrence are absorbed once `log N` is large, and
the finite prefix is absorbed into the additive constant. -/
theorem nativePNTHasAffineEnvelope_improve_of_goodMass
    (alpha beta c : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 ≤ beta) (hba : beta < alpha)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hgood : ∀ᶠ N : ℕ in atTop,
      c * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N beta)
    (henv : nativePNTHasAffineEnvelope alpha) :
    nativePNTHasAffineEnvelope
      (alpha - (alpha - beta) * c / 4) := by
  rcases henv with ⟨D, hD, henv⟩
  let delta : ℝ := (alpha - beta) * c / 4
  have habpos : 0 < alpha - beta := sub_pos.mpr hba
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hable : alpha - beta ≤ alpha := by linarith
  have hmul : (alpha - beta) * c ≤ alpha := by
    have := mul_le_mul hable hc1 hc.le halpha.le
    simpa using this
  have hdeltale : delta ≤ alpha / 4 := by
    dsimp [delta]
    nlinarith
  have hnewnonneg : 0 ≤ alpha - delta := by
    nlinarith
  let C0 : ℝ := 3000 * alpha + 784 * D + 3000
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hlogTop :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog1 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    hlogTop.eventually_ge_atTop 1
  have hlogC : ∀ᶠ N : ℕ in atTop,
      C0 / (3 * delta) ≤ Real.log (N : ℝ) :=
    hlogTop.eventually_ge_atTop (C0 / (3 * delta))
  have hlarge : ∀ᶠ N : ℕ in atTop,
      |nativePNTError N| ≤ (alpha - delta) * (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 3, hgood, hlog1, hlogC]
      with N hN hgoodN hL1 hLC
    have hN1 : 1 ≤ N := by omega
    have hNR0 : 0 ≤ (N : ℝ) := by positivity
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    let L : ℝ := Real.log (N : ℝ)
    have hL1' : (1 : ℝ) ≤ L := by simpa [L] using hL1
    have hL0 : 0 ≤ L := le_trans (by norm_num) hL1'
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1'
    have hden : 0 < 3 * delta := by positivity
    have hCLe0 : C0 ≤ L * (3 * delta) := by
      apply (div_le_iff₀ hden).mp
      simpa [L] using hLC
    have hCLe : C0 ≤ 3 * delta * L := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hCLe0
    have hB0 : 0 ≤ 2000 * alpha + 782 * D := by positivity
    have hBLe :
        2000 * alpha + 782 * D ≤
          (2000 * alpha + 782 * D) * L := by
      have h := mul_le_mul_of_nonneg_left hL1' hB0
      simpa using h
    have hleft :
        alpha * (1000 * L + 2000) +
            D * (2 * L + 782) + 3000 * L ≤ C0 * L := by
      dsimp [C0]
      nlinarith [hBLe]
    have hCLmul : C0 * L ≤ (3 * delta * L) * L :=
      mul_le_mul_of_nonneg_right hCLe hL0
    have hinner :
        alpha * (1000 * L + 2000) +
            D * (2 * L + 782) + 3000 * L ≤
          3 * delta * L ^ 2 := by
      calc
        alpha * (1000 * L + 2000) +
              D * (2 * L + 782) + 3000 * L ≤ C0 * L := hleft
        _ ≤ (3 * delta * L) * L := hCLmul
        _ = 3 * delta * L ^ 2 := by ring
    have hD600 : D * 600 ≤ D * 600 * (N : ℝ) := by
      have h600D : 0 ≤ D * 600 := by positivity
      have h := mul_le_mul_of_nonneg_left hN1R h600D
      simpa [mul_assoc] using h
    have hinnerN := mul_le_mul_of_nonneg_left hinner hNR0
    have hoverhead :
        alpha * (N : ℝ) * (1000 * L + 2000) +
            D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
            3000 * (N : ℝ) * L ≤
          3 * delta * (N : ℝ) * L ^ 2 := by
      have hreshape :
          alpha * (N : ℝ) * (1000 * L + 2000) +
              D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
              3000 * (N : ℝ) * L ≤
            (N : ℝ) *
              (alpha * (1000 * L + 2000) +
                D * (2 * L + 782) + 3000 * L) := by
        nlinarith [hD600]
      calc
        alpha * (N : ℝ) * (1000 * L + 2000) +
              D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
              3000 * (N : ℝ) * L ≤
            (N : ℝ) *
              (alpha * (1000 * L + 2000) +
                D * (2 * L + 782) + 3000 * L) := hreshape
        _ ≤ (N : ℝ) * (3 * delta * L ^ 2) := hinnerN
        _ = 3 * delta * (N : ℝ) * L ^ 2 := by ring
    have hcoef0 : 0 ≤ (alpha - beta) * (N : ℝ) :=
      mul_nonneg habpos.le hNR0
    have hgoodN' : c * L ^ 2 ≤ nativeLambdaTwoGoodRecipMass N beta := by
      simpa [L] using hgoodN
    have hgoodMul := mul_le_mul_of_nonneg_left hgoodN' hcoef0
    have hdeficit :
        -(alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta ≤
          -4 * delta * (N : ℝ) * L ^ 2 := by
      calc
        -(alpha - beta) * (N : ℝ) * nativeLambdaTwoGoodRecipMass N beta =
            -((alpha - beta) * (N : ℝ) *
              nativeLambdaTwoGoodRecipMass N beta) := by ring
        _ ≤ -((alpha - beta) * (N : ℝ) * (c * L ^ 2)) :=
          neg_le_neg hgoodMul
        _ = -4 * delta * (N : ℝ) * L ^ 2 := by
          dsimp [delta]
          ring
    have htail :
        (alpha * (N : ℝ) * (1000 * L + 2000) +
            D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
            3000 * (N : ℝ) * L) +
          (-(alpha - beta) * (N : ℝ) *
            nativeLambdaTwoGoodRecipMass N beta) ≤
          -delta * (N : ℝ) * L ^ 2 := by
      nlinarith [hoverhead, hdeficit]
    have hrec := nativePNTError_abs_log_sq_le_affine_compensated
      N hN alpha beta D halpha.le hbeta hba.le hD henv
    have hrearrange :
        alpha * (N : ℝ) *
              (L ^ 2 + 1000 * L + 2000) -
            (alpha - beta) * (N : ℝ) *
              nativeLambdaTwoGoodRecipMass N beta +
            D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
            3000 * (N : ℝ) * L =
          alpha * (N : ℝ) * L ^ 2 +
            ((alpha * (N : ℝ) * (1000 * L + 2000) +
                D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                3000 * (N : ℝ) * L) +
              (-(alpha - beta) * (N : ℝ) *
                nativeLambdaTwoGoodRecipMass N beta)) := by
      ring
    have hsq :
        |nativePNTError N| * L ^ 2 ≤
          (alpha - delta) * (N : ℝ) * L ^ 2 := by
      have hrec' :
          |nativePNTError N| * L ^ 2 ≤
            alpha * (N : ℝ) * L ^ 2 +
              ((alpha * (N : ℝ) * (1000 * L + 2000) +
                  D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                  3000 * (N : ℝ) * L) +
                (-(alpha - beta) * (N : ℝ) *
                  nativeLambdaTwoGoodRecipMass N beta)) := by
        simpa [L, hrearrange] using hrec
      calc
        |nativePNTError N| * L ^ 2 ≤
            alpha * (N : ℝ) * L ^ 2 +
              ((alpha * (N : ℝ) * (1000 * L + 2000) +
                  D * (2 * (N : ℝ) * L + 182 * (N : ℝ) + 600) +
                  3000 * (N : ℝ) * L) +
                (-(alpha - beta) * (N : ℝ) *
                  nativeLambdaTwoGoodRecipMass N beta)) := hrec'
        _ ≤ alpha * (N : ℝ) * L ^ 2 - delta * (N : ℝ) * L ^ 2 := by
          simpa [sub_eq_add_neg] using
            (add_le_add_left htail (alpha * (N : ℝ) * L ^ 2))
        _ = (alpha - delta) * (N : ℝ) * L ^ 2 := by ring
    have hLsq : 0 < L ^ 2 := sq_pos_of_pos hLpos
    have hsq' :
        |nativePNTError N| * L ^ 2 ≤
          ((alpha - delta) * (N : ℝ)) * L ^ 2 := by
      simpa [mul_assoc] using hsq
    exact (mul_le_mul_iff_left₀ hLsq).mp hsq'
  rcases (eventually_atTop.1 hlarge) with ⟨M, hM⟩
  refine ⟨D + delta * (M : ℝ), ?_, ?_⟩
  · positivity
  · intro N
    by_cases hMN : M ≤ N
    · exact (hM N hMN).trans
        (le_add_of_nonneg_right (by positivity))
    · have hNM : N ≤ M := Nat.le_of_lt (lt_of_not_ge hMN)
      have hNMR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
      have hdeltaNM := mul_le_mul_of_nonneg_left hNMR hdelta.le
      have hold := henv N
      have htarget :
          alpha * (N : ℝ) + D ≤
            (alpha - delta) * (N : ℝ) +
              (D + delta * (M : ℝ)) := by
        nlinarith
      exact hold.trans htarget


/-! ## Quantitative mass from one good PNT2 radius -/

/-- A PNT2 radius produces a fixed relative gap after reciprocal-floor
reindexing.  The hypothesis `32 ≤ eps * floor(N/t)` absorbs the two integer
floor errors. -/
theorem nativePNT_reciprocal_radius_gap
    (N t : ℕ) (eps : ℝ)
    (ht : 1 ≤ t) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hB : 32 ≤ eps * ((N / t : ℕ) : ℝ)) :
    ((N / (t + nativePNTGoodForwardRadius t eps + 1) : ℕ) : ℝ) ≤
      (1 - eps / 32) * ((N / t : ℕ) : ℝ) := by
  let H : ℕ := nativePNTGoodForwardRadius t eps
  let B : ℝ := ((N / t : ℕ) : ℝ)
  let d : ℕ := t + H + 1
  have htpos : 0 < t := by omega
  have htRpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
  have hB' : 32 ≤ eps * B := by simpa [B] using hB
  have hrad : eps * (t : ℝ) / 8 < (H : ℝ) + 1 := by
    dsimp [H, nativePNTGoodForwardRadius]
    simpa using (Nat.lt_floor_add_one (eps * (t : ℝ) / 8))
  have hdR : (1 + eps / 8) * (t : ℝ) < (d : ℝ) := by
    dsimp [d]
    push_cast
    nlinarith [hrad]
  have hmod := Nat.mod_lt N htpos
  have hNupperNat : N < (N / t + 1) * t := by
    calc
      N = N / t * t + N % t := (Nat.div_add_mod N t).symm
      _ < N / t * t + t := Nat.add_lt_add_left hmod _
      _ = (N / t + 1) * t := by ring
  have hNupper : (N : ℝ) < (B + 1) * (t : ℝ) := by
    dsimp [B]
    exact_mod_cast hNupperNat
  have hBpos : 0 < B := by
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    nlinarith
  have heps0 : 0 ≤ eps := heps.le
  have hepssq : eps ^ 2 ≤ eps := by nlinarith
  have hsquareB : eps ^ 2 * B ≤ eps * B :=
    mul_le_mul_of_nonneg_right hepssq hBpos.le
  have hratio :
      B + 1 ≤ (1 - eps / 32) * B * (1 + eps / 8) := by
    nlinarith [hB', hsquareB]
  have hratio_t := mul_le_mul_of_nonneg_right hratio htRpos.le
  have hfactor : 0 < 1 - eps / 32 := by nlinarith
  have htargetpos : 0 < (1 - eps / 32) * B :=
    mul_pos hfactor hBpos
  have hdenScaled := mul_lt_mul_of_pos_left hdR htargetpos
  have hNtarget :
      (N : ℝ) < ((1 - eps / 32) * B) * (d : ℝ) := by
    calc
      (N : ℝ) < (B + 1) * (t : ℝ) := hNupper
      _ ≤ ((1 - eps / 32) * B * (1 + eps / 8)) * (t : ℝ) := hratio_t
      _ = ((1 - eps / 32) * B) * ((1 + eps / 8) * (t : ℝ)) := by ring
      _ < ((1 - eps / 32) * B) * (d : ℝ) := hdenScaled
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdRpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hquot :
      (N : ℝ) / (d : ℝ) < (1 - eps / 32) * B := by
    rw [div_lt_iff₀ hdRpos]
    simpa [mul_comm] using hNtarget
  have hfloor : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdRpos]
    exact_mod_cast Nat.div_mul_le_self N d
  simpa [d, H, B] using hfloor.trans hquot.le

/-- The reciprocal interval attached to one sufficiently deep PNT2 radius has
a positive `Lambda_2/n` mass of size `eps * log(N/t)`. -/
theorem nativeLambdaTwoRecipIntervalMass_good_radius_lower
    (N t : ℕ) (eps : ℝ)
    (ht : 1 ≤ t) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hA : 3 ≤ N / (t + nativePNTGoodForwardRadius t eps + 1))
    (hB : 32 ≤ eps * ((N / t : ℕ) : ℝ))
    (hlog :
      64 * (2 * (Real.log 4 + 2) + 172) ≤
        eps * Real.log ((N / t : ℕ) : ℝ)) :
    (eps / 32) * Real.log ((N / t : ℕ) : ℝ) ≤
      nativeLambdaTwoRecipIntervalMass
        (N / (t + nativePNTGoodForwardRadius t eps + 1))
        (N / t) := by
  have hden : t ≤ t + nativePNTGoodForwardRadius t eps + 1 := by omega
  have hAB :
      N / (t + nativePNTGoodForwardRadius t eps + 1) ≤ N / t :=
    Nat.div_le_div_left hden (by omega)
  have hgap := nativePNT_reciprocal_radius_gap N t eps ht heps heps1 hB
  have hlog' :
      2 * (2 * (Real.log 4 + 2) + 172) ≤
        (eps / 32) * Real.log ((N / t : ℕ) : ℝ) := by
    nlinarith [hlog]
  exact nativeLambdaTwoRecipIntervalMass_gap_lower
    (N / (t + nativePNTGoodForwardRadius t eps + 1))
    (N / t) (eps / 32) hA hAB hgap hlog'

/-- One sufficiently deep PNT2 interval therefore contributes the same
quantitative lower bound directly to the global good-fibre compensation mass. -/
theorem nativeLambdaTwoGoodRecipMass_good_radius_lower
    (N t : ℕ) (eps : ℝ)
    (ht : 1 ≤ t) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hA : 3 ≤ N / (t + nativePNTGoodForwardRadius t eps + 1))
    (hB : 32 ≤ eps * ((N / t : ℕ) : ℝ))
    (hlog :
      64 * (2 * (Real.log 4 + 2) + 172) ≤
        eps * Real.log ((N / t : ℕ) : ℝ))
    (hgood : ∀ q ∈ Finset.Icc t
      (t + nativePNTGoodForwardRadius t eps),
      |nativePNTError q| ≤ eps * (q : ℝ)) :
    (eps / 32) * Real.log ((N / t : ℕ) : ℝ) ≤
      nativeLambdaTwoGoodRecipMass N eps := by
  have hlocal := nativeLambdaTwoRecipIntervalMass_good_radius_lower
    N t eps ht heps heps1 hA hB hlog
  have htoGood :=
    nativeLambdaTwoRecipIntervalMass_le_good_of_good_quotient_interval
      N t (nativePNTGoodForwardRadius t eps) eps ht heps.le hgood
  exact hlocal.trans htoGood

end RHLean.Analysis
