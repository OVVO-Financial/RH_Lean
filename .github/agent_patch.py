from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()


def repl(old: str, new: str) -> None:
    global s
    count = s.count(old)
    assert count == 1, (count, old[:120])
    s = s.replace(old, new, 1)

repl(
'''    have hrho3 : nativeLambdaTwoSummatory 3 ≤ 600 := by
      nlinarith [h3.2, hC3, hlogpart]
''',
'''    have hrho3 : nativeLambdaTwoSummatory 3 ≤ 600 := by
      calc
        nativeLambdaTwoSummatory 3 ≤
            2 * (3 : ℝ) * Real.log 3 +
              (2 * (Real.log 4 + 2) + 172) * (3 : ℝ) := by
          linarith [h3.2]
        _ ≤ 12 + 546 := add_le_add hlogpart hC3
        _ ≤ 600 := by norm_num
''')

repl(
'''    (N : ℕ) (alpha beta D : ℝ)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hba : beta ≤ alpha)
    (hD : 0 ≤ D)
''',
'''    (N : ℕ) (alpha beta D : ℝ)
    (_halpha : 0 ≤ alpha) (_hbeta : 0 ≤ beta) (_hba : beta ≤ alpha)
    (hD : 0 ≤ D)
''')

repl(
'''  have hnI := Finset.mem_Icc.mp hn
  have hnpos : 0 < n := by omega
''',
'''  have hnI := Finset.mem_Icc.mp hn
  have hnpos : 0 < n :=
    lt_of_lt_of_le (Nat.zero_lt_succ (N / (t + H + 1))) hnI.1
''')

repl(
'''  exact ⟨hquotLower, by omega⟩
''',
'''  exact ⟨hquotLower, Nat.lt_succ_iff.mp hquotUpper⟩
''')

repl(
'''  have hnI := Finset.mem_Icc.mp hn
  have hn1 : 1 ≤ n := by omega
  have hnN : n ≤ N :=
''',
'''  have hnI := Finset.mem_Icc.mp hn
  have hnpos : 0 < n :=
    lt_of_lt_of_le (Nat.zero_lt_succ (N / (t + H + 1))) hnI.1
  have hn1 : 1 ≤ n := Nat.succ_le_iff.mpr hnpos
  have hnN : n ≤ N :=
''')

repl(
'''  have hnposR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
''',
'''  have hnposR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnpos
''')

p.write_text(s)
