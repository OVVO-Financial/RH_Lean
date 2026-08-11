from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_reciprocal_interval_subset_good' in s
assert 'nativeLambdaTwoGoodRecipMass_packed_blocks' not in s
marker = '\nend RHLean.Analysis\n'
assert s.count(marker) == 1
block = r'''

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
'''
s = s.replace(marker, block + marker)
p.write_text(s)
