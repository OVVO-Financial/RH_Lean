from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_exists_dyadic_depth_quantitative' in s
assert 'nativeLambdaTwoGoodRecipMass_eventually_quadratic_with_rate' in s
assert 'nativeLambdaTwoGoodRecipMass_eventually_quadratic_rate' in s
assert '6500000' in s
assert 'tendsto_zero_of_cubic_recurrence' in s
p.write_text(s)
