from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_exists_dyadic_depth' in s
assert 'nativePNT_exists_good_radius_dyadic_eventually' in s
assert 'nativePNT_reciprocal_radius_gap' in s
assert 'nativePNTHasAffineEnvelope_improve_of_goodMass' in s
p.write_text(s)
