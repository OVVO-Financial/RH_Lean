from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()


def repl(old: str, new: str) -> None:
    global s
    count = s.count(old)
    assert count == 1, (count, old[:140])
    s = s.replace(old, new, 1)

repl(
'''  have hcancel : (eps / 4) * (4 * C / eps) = C := by
    field_simp [ne_of_gt heps]
    ring
''',
'''  have hcancel : (eps / 4) * (4 * C / eps) = C := by
    field_simp [ne_of_gt heps]
''')

repl(
'''  have hnum1 : eps * Real.log 2 ≤ 1 := by
    have hnonneg : 0 ≤ Real.log (2 : ℝ) := hlog2pos.le
    have := mul_le_mul heps1 hlog2le hnonneg heps.le
    simpa using this
''',
'''  have hnum1 : eps * Real.log 2 ≤ 1 := by
    have hnonneg : 0 ≤ Real.log (2 : ℝ) := hlog2pos.le
    have h := mul_le_mul heps1 hlog2le hnonneg
      (show (0 : ℝ) ≤ 1 by norm_num)
    simpa using h
''')

repl(
'''    have hexp : E + i * L + K + 1 < E + j * L := by
      have hji : i + 1 ≤ j := by omega
      have hmul : (i + 1) * L ≤ j * L := Nat.mul_le_mul_right L hji
      dsimp [L] at hmul ⊢
      omega
''',
'''    have hexp : E + i * L + K + 1 < E + j * L := by
      have hji : i + 1 ≤ j := by omega
      have hmul : (i + 1) * L ≤ j * L := Nat.mul_le_mul_right L hji
      have hstep : E + i * L + K + 1 < E + (i + 1) * L := by
        dsimp [L]
        omega
      exact hstep.trans_le (Nat.add_le_add_left hmul E)
''')

repl(
'''    have hexpQ : E + j * L + K + 2 ≤ q / 4 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
      have hEpart : 8 * (E + K + 2) ≤ q := hqE
      dsimp [L] at hjstep ⊢
      omega
''',
'''    have hexpQ : E + j * L + K + 2 ≤ q / 4 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
      have hEpart : 8 * (E + K + 2) ≤ q := hqE
      have hjpart : 8 * (j * L) ≤ q := by
        calc
          8 * (j * L) ≤ 8 * ((j + 1) * L) :=
            Nat.mul_le_mul_left 8 (Nat.mul_le_mul_right L (Nat.le_succ j))
          _ = (j + 1) * (8 * L) := by ring
          _ ≤ q := hjstep
      have hsum : 4 * (E + K + 2 + j * L) ≤ q := by
        omega
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum
''')

repl(
'''        _ = 2 ^ (E + j * L + K + 2) := by
          rw [show E + j * L + K + 2 = (E + j * L + K) + 2 by omega, pow_add]
          norm_num
''',
'''        _ = 2 ^ (E + j * L + K + 2) := by
          calc
            4 * 2 ^ (E + j * L + K) =
                2 ^ 2 * 2 ^ (E + j * L + K) := by norm_num
            _ = 2 ^ (2 + (E + j * L + K)) := by rw [← pow_add]
            _ = 2 ^ (E + j * L + K + 2) := by
              congr 1
              omega
''')

repl(
'''    exact (Nat.le_div_iff_mul_le hdpos).2 hdM
''',
'''    exact (Nat.le_div_iff_mul_le hdpos).2 (by
      simpa [Nat.mul_comm] using hdM)
''')

repl(
'''  have hA : ∀ j < J,
      3 ≤ N / (t j + nativePNTGoodForwardRadius (t j) eps + 1) := by
    intro j hj
    exact (by omega : 3 ≤ M).trans (hLocalQuot j hj)
''',
'''  have hA : ∀ j < J,
      3 ≤ N / (t j + nativePNTGoodForwardRadius (t j) eps + 1) := by
    intro j hj
    exact hMfour.trans (hLocalQuot j hj)
''')

repl(
'''  have hJlowerNat : q ≤ 16 * L * J := by
    omega
''',
'''  have hJtwo : 2 ≤ J := by
    dsimp [J]
    apply (Nat.le_div_iff_mul_le hdpos).2
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hqJL
  have hJone : 1 ≤ J := by omega
  have hdJ : 8 * L ≤ (8 * L) * J := by
    simpa using Nat.mul_le_mul_left (8 * L) hJone
  have hremJ : q % (8 * L) ≤ (8 * L) * J :=
    (Nat.le_of_lt hmod).trans hdJ
  have hJlowerNat : q ≤ 16 * L * J := by
    calc
      q = (8 * L) * J + q % (8 * L) := hqDecomp.symm
      _ ≤ (8 * L) * J + (8 * L) * J := Nat.add_le_add_left hremJ _
      _ = 16 * L * J := by ring
''')

repl(
'''  have hqdiv4 : (q : ℝ) / 8 ≤ ((q / 4 : ℕ) : ℝ) := by
    have hdiv : q ≤ 2 * (q / 4) + 6 := by omega
    have hq8R : (8 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq8
    have : (6 : ℝ) ≤ (3 / 4 : ℝ) * (q : ℝ) := by nlinarith
    exact_mod_cast (show (0 : ℕ) ≤ q / 4 by omega) at *
    nlinarith
''',
'''  have hqdiv4 : (q : ℝ) / 8 ≤ ((q / 4 : ℕ) : ℝ) := by
    have hdec4 : 4 * (q / 4) + q % 4 = q := Nat.div_add_mod q 4
    have hmod4 : q % 4 < 4 := Nat.mod_lt q (by norm_num)
    have hnat : q ≤ 8 * (q / 4) := by
      omega
    have hcast : (q : ℝ) ≤ 8 * ((q / 4 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    nlinarith
''')

p.write_text(s)
