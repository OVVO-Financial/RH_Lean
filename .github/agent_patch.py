from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_exists_good_power_shell_selector' not in s
marker = '\nend RHLean.Analysis\n'
assert s.count(marker) == 1
block = r'''

/-- For every `0 < eps <= 1` there is one globally chosen PNT2-good interval
in each member of a fixed, separated power-of-two shell sequence. -/
theorem nativePNT_exists_good_power_shell_selector
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ K E : ℕ, ∃ t : ℕ → ℕ,
      (∀ j : ℕ, 2 ^ (E + j * (K + 2)) ≤ t j) ∧
      (∀ j : ℕ, t j ≤ 2 ^ (E + j * (K + 2) + K)) ∧
      (∀ j : ℕ,
        ∀ q ∈ Finset.Icc (t j)
          (t j + nativePNTGoodForwardRadius (t j) eps),
          |nativePNTError q| ≤ eps * (q : ℝ)) := by
  classical
  rcases nativePNT_exists_dyadic_depth eps heps with ⟨K, hdepth⟩
  have hshell :=
    nativePNT_exists_good_radius_dyadic_eventually K eps heps heps1 hdepth
  rcases eventually_atTop.1 hshell with ⟨A₀, hA₀⟩
  let shell : ℕ → ℕ := fun j => 2 ^ (A₀ + j * (K + 2))
  have hA₀pow : A₀ ≤ 2 ^ A₀ := by
    exact (Nat.lt_pow_self Nat.one_lt_two).le
  have hbase : ∀ j : ℕ, A₀ ≤ shell j := by
    intro j
    have hexp : A₀ ≤ A₀ + j * (K + 2) := by omega
    have hp : 2 ^ A₀ ≤ 2 ^ (A₀ + j * (K + 2)) :=
      (Nat.pow_le_pow_iff_right Nat.one_lt_two).2 hexp
    exact hA₀pow.trans hp
  have hExists : ∀ j : ℕ,
      ∃ u ∈ Finset.Icc (shell j) (shell j * 2 ^ K),
        |nativePNTError u| ≤ eps * (u : ℝ) / 4 ∧
          ∀ q ∈ Finset.Icc u (u + nativePNTGoodForwardRadius u eps),
            |nativePNTError q| ≤ eps * (q : ℝ) := by
    intro j
    exact hA₀ (shell j) (hbase j)
  let t : ℕ → ℕ := fun j => Classical.choose (hExists j)
  have hspec : ∀ j : ℕ,
      t j ∈ Finset.Icc (shell j) (shell j * 2 ^ K) ∧
        |nativePNTError (t j)| ≤ eps * (t j : ℝ) / 4 ∧
          ∀ q ∈ Finset.Icc (t j)
            (t j + nativePNTGoodForwardRadius (t j) eps),
            |nativePNTError q| ≤ eps * (q : ℝ) := by
    intro j
    exact Classical.choose_spec (hExists j)
  refine ⟨K, A₀, t, ?_, ?_, ?_⟩
  · intro j
    exact (Finset.mem_Icc.mp (hspec j).1).1
  · intro j
    have hu := (Finset.mem_Icc.mp (hspec j).1).2
    dsimp [shell] at hu
    simpa [pow_add] using hu
  · intro j q hq
    exact (hspec j).2.2 q hq
'''
s = s.replace(marker, block + marker)
p.write_text(s)
