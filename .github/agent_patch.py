from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativeLambdaTwoGoodRecipMass_packed_blocks' in s
assert 'nativePNTGoodForwardRadius' in s
assert 'nativePNT_exists_good_radius_dyadic' in s
assert 'nativeLambdaTwoGoodRecipMass_packed_quotient_intervals' in s
p.write_text(s)
