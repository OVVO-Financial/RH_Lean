from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativeLambdaTwoGoodRecipMass_packed_good_radii_lower' not in s
marker = '\nend RHLean.Analysis\n'
assert s.count(marker) == 1
block = r'''

/-- A separated family of sufficiently deep PNT2 radii contributes the sum of
all its local Selberg lower bounds to the global good-fibre compensation mass. -/
theorem nativeLambdaTwoGoodRecipMass_packed_good_radii_lower
    (N J : ℕ) (eps : ℝ) (t : ℕ → ℕ)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (ht : ∀ j < J, 1 ≤ t j)
    (hgood : ∀ j < J,
      ∀ q ∈ Finset.Icc (t j)
        (t j + nativePNTGoodForwardRadius (t j) eps),
        |nativePNTError q| ≤ eps * (q : ℝ))
    (hsep : ∀ i j, i < j → j < J →
      t i + nativePNTGoodForwardRadius (t i) eps < t j)
    (hA : ∀ j < J,
      3 ≤ N / (t j + nativePNTGoodForwardRadius (t j) eps + 1))
    (hB : ∀ j < J,
      32 ≤ eps * ((N / t j : ℕ) : ℝ))
    (hlog : ∀ j < J,
      64 * (2 * (Real.log 4 + 2) + 172) ≤
        eps * Real.log ((N / t j : ℕ) : ℝ)) :
    (∑ j ∈ Finset.range J,
      (eps / 32) * Real.log ((N / t j : ℕ) : ℝ)) ≤
      nativeLambdaTwoGoodRecipMass N eps := by
  have hlocal :
      (∑ j ∈ Finset.range J,
        (eps / 32) * Real.log ((N / t j : ℕ) : ℝ)) ≤
        ∑ j ∈ Finset.range J,
          nativeLambdaTwoRecipIntervalMass
            (N / (t j + nativePNTGoodForwardRadius (t j) eps + 1))
            (N / t j) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    exact nativeLambdaTwoRecipIntervalMass_good_radius_lower
      N (t j) eps (ht j hjlt) heps heps1
      (hA j hjlt) (hB j hjlt) (hlog j hjlt)
  have hpacked := nativeLambdaTwoGoodRecipMass_packed_quotient_intervals
    N J eps t (fun j => nativePNTGoodForwardRadius (t j) eps)
    heps.le ht hgood hsep
  exact hlocal.trans hpacked
'''
s = s.replace(marker, block + marker)
p.write_text(s)
