from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_quotient_mem_of_reciprocal_interval' in s
assert 'nativePNT_reciprocal_interval_subset_good' in s
assert 'nativeLambdaTwoGoodRecipMass_of_good_quotient_interval' in s
p.write_text(s)
