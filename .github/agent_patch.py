from pathlib import Path

p = Path('RHLean/Analysis/NativePNTSummatorySelberg.lean')
s = p.read_text()
old = "  intro d _hd\n  ring\n\nprivate theorem nativeMobiusLogSquareMainMass_eq\n"
new = "  intro d _hd\n  ring_nf\n\nprivate theorem nativeMobiusLogSquareMainMass_eq\n"
assert old in s, 'target not found'
p.write_text(s.replace(old, new, 1))
