from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'theorem cubic_recurrence_rate_sub' in s
assert 'theorem nativePNTHasAffineEnvelope_mono' in s
assert 'def nativePNTCubicConstant : ℝ := 1 / 1123200000' in s
assert 'theorem nativePNTHasAffineEnvelope_cubic_step' in s
assert 'def nativePNTCubicSlope' in s
assert 'theorem nativePNTCubicSlope_tendsto_zero' in s
assert 'theorem nativePNTCubicSlope_rate' in s
assert 'theorem nativePNTHasAffineEnvelope_of_cubic_budget' in s
p.write_text(s)
