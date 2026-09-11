from pathlib import Path

p = Path("RHLean/Proof/ExceptionalContactFrameEnergyNoGo.lean")
s = p.read_text()

old = '''  have hhi_le : hi ≤ lo + 1 := by
    dsimp [lo, hi]
    rw [show 4 * (k + 1) = 4 * k + 4 by omega]
    calc
      (4 * k + 4) / Q ≤ 4 * k / Q + 4 / Q + 1 :=
        Nat.add_div_le_div_add_div_add_one _ _ _
      _ = 4 * k / Q + 1 := by
        rw [Nat.div_eq_of_lt hQgt4]
        omega
'''
new = '''  have hhi_le : hi ≤ lo + 1 := by
    have hxlt : 4 * k < Q * (lo + 1) := by
      have hdiv : 4 * k / Q < lo + 1 := by
        dsimp [lo]
        omega
      have h := (Nat.div_lt_iff_lt_mul hQpos).1 hdiv
      simpa [Nat.mul_comm] using h
    have hsumlt : 4 * (k + 1) < Q * (lo + 2) := by
      calc
        4 * (k + 1) = 4 * k + 4 := by omega
        _ < Q * (lo + 1) + Q := Nat.add_lt_add hxlt hQgt4
        _ = Q * (lo + 2) := by ring
    have hdivHi : hi < lo + 2 := by
      dsimp [hi]
      have hsumlt' : 4 * (k + 1) < (lo + 2) * Q := by
        rw [Nat.mul_comm (lo + 2) Q]
        exact hsumlt
      exact (Nat.div_lt_iff_lt_mul hQpos).2 hsumlt'
    omega
'''
if old not in s:
    raise SystemExit("hhi_le block not found")
s = s.replace(old, new, 1)

old = '''  rw [hstep, moebiusPositivePrefix_succ_sub_self] at hD'
  have hsf : Squarefree hi :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hD'
'''
new = '''  rw [hstep, moebiusPositivePrefix_succ_sub_self] at hD'
  have hsfStep : Squarefree (lo + 1) :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hD'
  have hsf : Squarefree hi := by
    rw [hstep]
    exact hsfStep
'''
if old not in s:
    raise SystemExit("squarefree block not found")
s = s.replace(old, new, 1)

old = '''  refine ⟨hi, ?_⟩
  rw [← hsum]
  dsimp [Q]
  ring
'''
new = '''  refine ⟨hi, ?_⟩
  calc
    4 * k + a = hi * Q := hsum
    _ = q * q * hi := by
      dsimp [Q]
      ring
'''
if old not in s:
    raise SystemExit("final witness block not found")
s = s.replace(old, new, 1)

p.write_text(s)
