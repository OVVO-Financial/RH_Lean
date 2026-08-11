from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativeLambdaTwoRecipMass_upper' not in s
marker = '\nend RHLean.Analysis\n'
assert marker in s
block = r'''

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
    have hrho3 : nativeLambdaTwoSummatory 3 ≤ 600 := by
      norm_num at hlog3
      nlinarith [h3.2]
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
      ring
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
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
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
      positivity
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
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
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
'''
s = s.replace(marker, block + marker, 1)
p.write_text(s)
