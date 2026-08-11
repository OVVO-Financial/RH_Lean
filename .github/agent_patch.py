from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
old = '''  have hNupperNat : N < (N / t + 1) * t := by
    calc
      N = N / t * t + N % t := (Nat.div_add_mod N t).symm
      _ < N / t * t + t := Nat.add_lt_add_left hmod _
      _ = (N / t + 1) * t := by ring
'''
new = '''  have hNupperNat : N < (N / t + 1) * t := by
    calc
      N = t * (N / t) + N % t := (Nat.div_add_mod N t).symm
      _ < t * (N / t) + t := Nat.add_lt_add_left hmod _
      _ = (N / t + 1) * t := by ring
'''
assert s.count(old) == 1
s = s.replace(old, new, 1)
p.write_text(s)
