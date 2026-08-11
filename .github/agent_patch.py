from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNTHasAffineEnvelope_improve_of_goodMass' in s
assert 'mul_le_mul_iff_right₀ hLsq' in s
p.write_text(s)
