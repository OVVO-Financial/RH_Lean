from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNTHasAffineEnvelope' in s
assert 'nativePNTHasAffineEnvelope_six' in s
assert 'nativePNTAffineEnvelope_on_fiber' in s
assert 'nativePNTError_abs_log_sq_le_affine_compensated' in s
p.write_text(s)
