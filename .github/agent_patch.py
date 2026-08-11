from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
old = 'theorem nativeLambda_mul_log_le_lambdaTwo (n : ℕ) (hn : 1 ≤ n) :\n'
new = 'theorem nativeLambda_mul_log_le_lambdaTwo (n : ℕ) (_hn : 1 ≤ n) :\n'
assert old in s, 'unused hn declaration not found'
s = s.replace(old, new, 1)
old = '    (hA : 1 ≤ A) (hAB : A ≤ B) (hε : 0 < ε)\n'
new = '    (hA : 1 ≤ A) (_hAB : A ≤ B) (_hε : 0 < ε)\n'
assert old in s, 'unused sign theorem arguments not found'
s = s.replace(old, new, 1)
p.write_text(s)
