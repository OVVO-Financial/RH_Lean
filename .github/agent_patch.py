from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativeLambdaTwoRecipMass' not in s
marker = '\nend RHLean.Analysis\n'
assert marker in s
block = r'''

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
  rw [← Finset.sum_div]
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
'''
s = s.replace(marker, block + marker, 1)
p.write_text(s)
