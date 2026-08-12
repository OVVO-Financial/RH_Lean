from pathlib import Path

p = Path('RHLean/Analysis/NativePNTAxer.lean')
s = p.read_text()
old = '''    _ = -∑ n ∈ Finset.Icc 1 N,
        ((μ : ArithmeticFunction ℝ) * Λ) n := by
      simp
'''
new = '''    _ = -∑ n ∈ Finset.Icc 1 N,
        ((μ : ArithmeticFunction ℝ) * Λ) n := by
      change (∑ n ∈ Finset.Icc 1 N,
        -(((μ : ArithmeticFunction ℝ) * Λ) n)) =
        -(∑ n ∈ Finset.Icc 1 N,
          ((μ : ArithmeticFunction ℝ) * Λ) n)
      rw [Finset.sum_neg_distrib]
'''
assert old in s
s = s.replace(old, new, 1)
p.write_text(s)
