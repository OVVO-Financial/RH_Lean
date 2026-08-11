from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_reciprocal_radius_gap' in s
assert 'nativeLambdaTwoRecipIntervalMass_good_radius_lower' in s
assert 'nativeLambdaTwoGoodRecipMass_good_radius_lower' in s
assert 'nativePNTHasAffineEnvelope_improve_of_goodMass' in s
p.write_text(s)
