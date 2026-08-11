from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErrorMass.lean')
s = p.read_text()
old = '''    rw [hend, hmain]\n    ring\n'''
new = '''    rw [hend]\n    linarith [hmain]\n'''
assert old in s, 'expected hdecomp rewrite block not found'
s = s.replace(old, new, 1)
p.write_text(s)
