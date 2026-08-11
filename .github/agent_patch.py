from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativeLambdaTwoRecipIntervalMass_le_good_of_good_quotient_interval' in s
assert 'nativePNT_reciprocal_blocks_disjoint' in s
assert 'nativeLambdaTwoGoodRecipMass_packed_blocks' in s
assert 'nativeLambdaTwoRecipIntervalMass_gap_lower' in s
p.write_text(s)
