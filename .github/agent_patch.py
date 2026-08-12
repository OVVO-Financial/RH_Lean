from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()

marker = '''/-- **Quadratic logarithmic density of good reciprocal fibres.**  For every
fixed `0 < eps <= 1`, the PNT2 good intervals supplied on separated dyadic
shells contribute a positive fixed multiple of `log^2 N` to the reciprocal
`Lambda_2` compensation mass.  This is the quantitative packing step that
closes the Selberg--Erdos contraction. -/
'''
helpers = r'''private lemma nativePNT_shell_step_lt (E K i : ℕ) :
    E + i * (K + 2) + K + 1 < E + (i + 1) * (K + 2) := by
  omega

private lemma nativePNT_four_mul_sum_le
    {a b q : ℕ} (ha : 8 * a ≤ q) (hb : 8 * b ≤ q) :
    4 * (a + b) ≤ q := by
  omega

private lemma nativePNT_quarter_cast_lower (q : ℕ) (hq : 8 ≤ q) :
    (q : ℝ) / 8 ≤ ((q / 4 : ℕ) : ℝ) := by
  have hdec4 : 4 * (q / 4) + q % 4 = q := Nat.div_add_mod q 4
  have hmod4 : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  have hnat : q ≤ 8 * (q / 4) := by
    omega
  have hcast : (q : ℝ) ≤ 8 * ((q / 4 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  nlinarith

private lemma nativePNT_quadratic_product_lower
    (eps logTwo L q J q4 : ℝ)
    (heps : 0 ≤ eps) (hlogTwo : 0 ≤ logTwo)
    (hL : 0 < L) (hq : 0 ≤ q) (hJnonneg : 0 ≤ J)
    (hJ : q / (16 * L) ≤ J) (hq4 : q / 8 ≤ q4) :
    eps * logTwo / (4096 * L) * q ^ 2 ≤
      J * ((eps / 32) * (q4 * logTwo)) := by
  have heps32 : 0 ≤ eps / 32 := div_nonneg heps (by norm_num)
  have hq8 : 0 ≤ q / 8 := div_nonneg hq (by norm_num)
  have hterm0 : 0 ≤ (eps / 32) * ((q / 8) * logTwo) :=
    mul_nonneg heps32 (mul_nonneg hq8 hlogTwo)
  have hterm :
      (eps / 32) * ((q / 8) * logTwo) ≤
        (eps / 32) * (q4 * logTwo) := by
    have hmul : (q / 8) * logTwo ≤ q4 * logTwo :=
      mul_le_mul_of_nonneg_right hq4 hlogTwo
    exact mul_le_mul_of_nonneg_left hmul heps32
  have hleft :
      (q / (16 * L)) * ((eps / 32) * ((q / 8) * logTwo)) ≤
        J * ((eps / 32) * ((q / 8) * logTwo)) :=
    mul_le_mul_of_nonneg_right hJ hterm0
  have hright :
      J * ((eps / 32) * ((q / 8) * logTwo)) ≤
        J * ((eps / 32) * (q4 * logTwo)) :=
    mul_le_mul_of_nonneg_left hterm hJnonneg
  have hprod := hleft.trans hright
  have halg :
      eps * logTwo / (4096 * L) * q ^ 2 =
        (q / (16 * L)) * ((eps / 32) * ((q / 8) * logTwo)) := by
    field_simp [ne_of_gt hL]
    <;> ring
  rw [halg]
  exact hprod

'''
assert marker in s
assert 'private lemma nativePNT_shell_step_lt' not in s
s = s.replace(marker, helpers + marker, 1)

repls = [
('''  let c : ℝ := eps * Real.log 2 / (8192 * (L : ℝ))\n''',
 '''  let c : ℝ := eps * Real.log 2 / (16384 * (L : ℝ))\n'''),
('''  have hden1 : (1 : ℝ) ≤ 8192 * (L : ℝ) := by\n''',
 '''  have hden1 : (1 : ℝ) ≤ 16384 * (L : ℝ) := by\n'''),
('''    have hdenpos : (0 : ℝ) < 8192 * (L : ℝ) := lt_of_lt_of_le (by norm_num) hden1\n''',
 '''    have hdenpos : (0 : ℝ) < 16384 * (L : ℝ) := lt_of_lt_of_le (by norm_num) hden1\n'''),
('''      have hstep : E + i * L + K + 1 < E + (i + 1) * L := by\n        dsimp [L]\n        omega\n''',
 '''      have hstep : E + i * L + K + 1 < E + (i + 1) * L := by\n        simpa [L] using nativePNT_shell_step_lt E K i\n'''),
('''      have hsum : 4 * (E + K + 2 + j * L) ≤ q := by\n        omega\n      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum\n''',
 '''      have hsum0 : 4 * ((E + K + 2) + j * L) ≤ q :=\n        nativePNT_four_mul_sum_le hEpart hjpart\n      have hsum : (E + j * L + K + 2) * 4 ≤ q := by\n        convert hsum0 using 1 <;> ring\n      exact hsum\n'''),
('''    have hden : t j ≤ t j + nativePNTGoodForwardRadius (t j) eps + 1 := by omega\n    exact hd.trans (Nat.div_le_div_left hden (by omega))\n''',
 '''    have hden : t j ≤ t j + nativePNTGoodForwardRadius (t j) eps + 1 := by omega\n    have htj0 : t j ≠ 0 := Nat.one_le_iff_ne_zero.mp (htOne j hjJ)\n    have htjpos : 0 < t j := Nat.pos_of_ne_zero htj0\n    exact hd.trans (Nat.div_le_div_left hden htjpos)\n'''),
('''    exact hMfour.trans (hLocalQuot j hj)\n''',
 '''    exact (show 3 ≤ 4 by norm_num).trans (hMfour.trans (hLocalQuot j hj))\n'''),
('''  have hJtwo : 2 ≤ J := by\n    dsimp [J]\n    apply (Nat.le_div_iff_mul_le hdpos).2\n    simpa using hqJL\n''',
 '''  have hJtwo : 2 ≤ J := by\n    dsimp [J]\n    apply (Nat.le_div_iff_mul_le hdpos).2\n    convert hqJL using 1 <;> ring\n'''),
('''  have hqdiv4 : (q : ℝ) / 8 ≤ ((q / 4 : ℕ) : ℝ) := by\n    have hdec4 : 4 * (q / 4) + q % 4 = q := Nat.div_add_mod q 4\n    have hmod4 : q % 4 < 4 := Nat.mod_lt q (by norm_num)\n    have hnat : q ≤ 8 * (q / 4) := by\n      omega\n    have hcast : (q : ℝ) ≤ 8 * ((q / 4 : ℕ) : ℝ) := by\n      exact_mod_cast hnat\n    nlinarith\n''',
 '''  have hqdiv4 : (q : ℝ) / 8 ≤ ((q / 4 : ℕ) : ℝ) :=\n    nativePNT_quarter_cast_lower q hq8\n'''),
('''    have hJreal : (q : ℝ) / (16 * (L : ℝ)) ≤ (J : ℝ) := by\n      have hLr : 0 < (L : ℝ) := by exact_mod_cast hLpos\n      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (L : ℝ))]\n      nlinarith [hJlower]\n    have htermQ :\n        (eps / 32) * (((q : ℝ) / 8) * Real.log 2) ≤\n          (eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2) := by\n      have hmul := mul_le_mul_of_nonneg_right hqdiv4 hlog2pos.le\n      exact mul_le_mul_of_nonneg_left hmul (by positivity)\n    have hprod := mul_le_mul hJreal htermQ\n      (by positivity)\n      (by positivity)\n    calc\n      eps * Real.log 2 / (4096 * (L : ℝ)) * (q : ℝ) ^ 2 ≤\n          ((J : ℕ) : ℝ) *\n            ((eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2)) := by\n        convert hprod using 1 <;> field_simp [show (L : ℝ) ≠ 0 by exact_mod_cast hLpos.ne'] <;> ring\n      _ ≤ ∑ j ∈ Finset.range J,\n''',
 '''    have hJreal : (q : ℝ) / (16 * (L : ℝ)) ≤ (J : ℝ) := by\n      have hden : (0 : ℝ) < 16 * (L : ℝ) := by positivity\n      apply (div_le_iff₀ hden).2\n      simpa [mul_assoc, mul_left_comm, mul_comm] using hJlower\n    have hprod :\n        eps * Real.log 2 / (4096 * (L : ℝ)) * (q : ℝ) ^ 2 ≤\n          ((J : ℕ) : ℝ) *\n            ((eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2)) := by\n      exact nativePNT_quadratic_product_lower\n        eps (Real.log 2) (L : ℝ) (q : ℝ) (J : ℝ) ((q / 4 : ℕ) : ℝ)\n        heps.le hlog2pos.le (by exact_mod_cast hLpos) (by positivity)\n        (by positivity) hJreal hqdiv4\n    calc\n      eps * Real.log 2 / (4096 * (L : ℝ)) * (q : ℝ) ^ 2 ≤\n          ((J : ℕ) : ℝ) *\n            ((eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2)) := hprod\n      _ ≤ ∑ j ∈ Finset.range J,\n'''),
('''    have hcoef : 0 ≤ eps * Real.log 2 / (8192 * (L : ℝ)) := hc.le\n''',
 '''    have hcoef : 0 ≤ eps * Real.log 2 / (16384 * (L : ℝ)) := hc.le\n'''),
]
for old, new in repls:
    assert old in s, old
    s = s.replace(old, new, 1)

p.write_text(s)
