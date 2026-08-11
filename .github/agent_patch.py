from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_exists_small_error_dyadic' not in s
marker = '\nend RHLean.Analysis\n'
assert marker in s
block = r'''

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
'''
s = s.replace(marker, block + marker, 1)
p.write_text(s)