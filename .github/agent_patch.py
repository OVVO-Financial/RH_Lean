from pathlib import Path


def replace_once(text: str, old: str, new: str, label: str) -> str:
    if new in text:
        return text
    count = text.count(old)
    assert count == 1, f'{label}: expected one old block, found {count}'
    return text.replace(old, new, 1)


# Keep the completed Axer bridge untouched, but retain the handoff validation.
p = Path('RHLean/Analysis/NativePNTAxer.lean')
s = p.read_text()
assert 'theorem arithmeticLogWeight_moebius' in s
assert 'change (∑ n ∈ Finset.Icc 1 N' in s
assert 'theorem nativeMobiusLogSum_eq_neg_one_sub_error' in s
assert 'theorem nativePNTAxerErrorMass_le_of_affineEnvelope' in s
assert 'theorem nativeMertens_abs_mul_log_le_of_affineEnvelope' in s
assert 'theorem nativeMertens_div_atTop_zero' in s
p.write_text(s)


# Repair only the three local NativePNTTransfer compiler clusters from the
# quantitative native-PNT handoff.  These replacements are intentionally
# idempotent because this helper may be triggered more than once.
p = Path('RHLean/Analysis/NativePNTTransfer.lean')
s = p.read_text()

old = '''      have hcardNat :
          ((nativePrimeSet N).filter
            (fun p => (p : ℝ) ≤ Real.sqrt (N : ℝ))).card ≤
            ⌊Real.sqrt (N : ℝ)⌋₊ := by
        rw [show ⌊Real.sqrt (N : ℝ)⌋₊ =
          #(Finset.Icc 1 ⌊Real.sqrt (N : ℝ)⌋₊) by simp]
        apply Finset.card_le_card
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpSet, hpSqrt⟩
        have hpPrime : p.Prime := (Finset.mem_filter.mp hpSet).2
        exact Finset.mem_Icc.mpr ⟨hpPrime.one_le, Nat.le_floor hpSqrt⟩
'''
new = '''      have hcardNat :
          ((nativePrimeSet N).filter
            (fun p : ℕ => (p : ℝ) ≤ Real.sqrt (N : ℝ))).card ≤
            ⌊Real.sqrt (N : ℝ)⌋₊ := by
        have hsubset :
            (nativePrimeSet N).filter
                (fun p : ℕ => (p : ℝ) ≤ Real.sqrt (N : ℝ)) ⊆
              Finset.Icc 1 ⌊Real.sqrt (N : ℝ)⌋₊ := by
          intro p hp
          rcases Finset.mem_filter.mp hp with ⟨hpSet, hpSqrt⟩
          have hpPrime : p.Prime := (Finset.mem_filter.mp hpSet).2
          exact Finset.mem_Icc.mpr ⟨hpPrime.one_le, Nat.le_floor hpSqrt⟩
        calc
          ((nativePrimeSet N).filter
              (fun p : ℕ => (p : ℝ) ≤ Real.sqrt (N : ℝ))).card ≤
              (Finset.Icc 1 ⌊Real.sqrt (N : ℝ)⌋₊).card :=
            Finset.card_le_card hsubset
          _ = ⌊Real.sqrt (N : ℝ)⌋₊ := by simp
'''
s = replace_once(s, old, new, 'prime-set square-root cardinality')

old = '''  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := lt_trans (by omega : 0 < K * M) hNlt
    exact_mod_cast this
'''
new = '''  have hKMle : K * M ≤ N := by
    dsimp [M]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self N K
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hKMpos : 0 < K * M := Nat.mul_pos hKpos hMpos
    have hNposNat : 0 < N := lt_of_lt_of_le hKMpos hKMle
    exact_mod_cast hNposNat
'''
s = replace_once(s, old, new, 'nativeLog_le_two_log_natDiv positivity')

old = '''    have hnorm :
        nativeTheta N / (N : ℝ) ≤
          ((Nat.primeCounting N : ℝ) * Real.log (N : ℝ)) / (N : ℝ) :=
      (div_le_div_iff₀ hNpos).2 hthetaPi
'''
new = '''    have hnorm :
        nativeTheta N / (N : ℝ) ≤
          ((Nat.primeCounting N : ℝ) * Real.log (N : ℝ)) / (N : ℝ) :=
      div_le_div_of_nonneg_right hthetaPi hNpos.le
'''
s = replace_once(s, old, new, 'normalized lower squeeze')

assert 'theorem nativePrimeNumberTheorem' in s
assert 'nativePrimeSet_card_eq_primeCounting' in s
p.write_text(s)
