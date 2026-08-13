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


# Guard the calibrated contraction interface against accidental weakening.
p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'theorem nativeLambdaTwoGoodRecipMass_eventually_quadratic_rate' in s
assert 'def nativePNTCubicConstant' in s
assert 'theorem nativePNTHasAffineEnvelope_cubic_step' in s
assert 'def nativePNTCubicSlope' in s
assert 'theorem nativePNTCubicSlope_rate' in s
assert 'theorem nativePNTHasAffineEnvelope_of_cubic_budget' in s
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

old = '''      have hcardReal :
          (((nativePrimeSet N).filter
            (fun p => (p : ℝ) ≤ Real.sqrt (N : ℝ))).card : ℕ) ≤
            Real.sqrt (N : ℝ) := by
        exact_mod_cast hcardNat.trans (Nat.floor_le (Real.sqrt_nonneg _))
'''
new = '''      have hcardReal :
          (((nativePrimeSet N).filter
            (fun p : ℕ => (p : ℝ) ≤ Real.sqrt (N : ℝ))).card : ℝ) ≤
            Real.sqrt (N : ℝ) := by
        have hcardFloorReal :
            (((nativePrimeSet N).filter
              (fun p : ℕ => (p : ℝ) ≤ Real.sqrt (N : ℝ))).card : ℝ) ≤
              (⌊Real.sqrt (N : ℝ)⌋₊ : ℝ) := by
          exact_mod_cast hcardNat
        have hfloorReal :
            (⌊Real.sqrt (N : ℝ)⌋₊ : ℝ) ≤ Real.sqrt (N : ℝ) :=
          Nat.floor_le (Real.sqrt_nonneg _)
        exact hcardFloorReal.trans hfloorReal
'''
s = replace_once(s, old, new, 'prime-set cardinality real cast')

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


# The post-PNT target file is intentionally declarative: it exposes the
# half-plus-epsilon targets and bridges the two Mertens presentations without
# claiming that qualitative PNT proves either target.
p = Path('RHLean/Analysis/NativePNTQuantitativeStatements.lean')
s = p.read_text()
assert 'def NativePNTChebyshevRHScaleStatement' in s
assert 'def MertensRHScaleStatement' in s
assert 'def NativeMertensRHScaleStatement' in s
assert 'def NativePNTQuantitativeTarget' in s
assert 'theorem mertensPowerBound_iff_nativeMertensPowerBound' in s
assert 'theorem mertensRHScale_of_energy' in s
p.write_text(s)


# Keep the generated root manifest synchronized with the new statement layer.
p = Path('RHLean.lean')
s = p.read_text()
needle = 'import RHLean.Analysis.NativePNTMobiusSecondMoment\n'
addition = needle + 'import RHLean.Analysis.NativePNTQuantitativeStatements\n'
if 'import RHLean.Analysis.NativePNTQuantitativeStatements\n' not in s:
    assert needle in s
    s = s.replace(needle, addition, 1)
p.write_text(s)
