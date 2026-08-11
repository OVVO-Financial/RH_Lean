from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_reciprocal_interval_subset_good' not in s
marker = '\nend RHLean.Analysis\n'
assert s.count(marker) == 1
block = r'''

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
  have hnpos : 0 < n := by omega
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
  exact ⟨hquotLower, by omega⟩

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
  have hn1 : 1 ≤ n := by omega
  have hnN : n ≤ N :=
    hnI.2.trans (Nat.div_le_self N t)
  have hnposR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
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
'''
s = s.replace(marker, block + marker)
p.write_text(s)
