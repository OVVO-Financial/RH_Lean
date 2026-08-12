from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativeLambdaTwoGoodRecipMass_eventually_quadratic' in s
assert 'nativePNTHasAffineEnvelope_arbitrarily_small' in s
assert 'nativePNTError_abs_div_atTop_zero' in s
assert 'nativePNTError_div_atTop_zero' in s
assert 'nativePsi_div_atTop_one' in s
p.write_text(s)
