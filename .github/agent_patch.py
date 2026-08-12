from pathlib import Path

p = Path('RHLean/Analysis/NativePNTAxer.lean')
s = p.read_text()
assert 'theorem arithmeticLogWeight_moebius' in s
assert 'theorem nativeMobiusLogSum_eq_neg_one_sub_error' in s
assert 'theorem nativePNTAxerErrorMass_le_of_affineEnvelope' in s
assert 'theorem nativeMertens_abs_mul_log_le_of_affineEnvelope' in s
assert 'theorem nativeMertens_div_atTop_zero' in s
assert 'abs_add_le' in s
p.write_text(s)
