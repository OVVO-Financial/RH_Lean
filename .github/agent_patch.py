from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_exists_dyadic_depth_quantitative' in s
assert 'have hhalf := (mul_lt_mul_right' in s
assert 'nativeLambdaTwoGoodRecipMass_eventually_quadratic_with_rate' in s
assert 'nativeLambdaTwoGoodRecipMass_eventually_quadratic_rate' in s
assert '6500000' in s
p.write_text(s)
