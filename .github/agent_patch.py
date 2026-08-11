from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_exists_good_power_shell_selector' in s
assert 'nativeLambdaTwoGoodRecipMass_eventually_quadratic' in s
assert 'nativePNTHasAffineEnvelope_improve_of_goodMass' in s
assert 'nativePNTError_abs_log_sq_le_affine_compensated' in s
p.write_text(s)
