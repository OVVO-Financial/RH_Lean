from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()

anchor = '''/-- For every positive error tolerance one can choose a fixed dyadic search
depth large enough for the PNT1/PNT2 pigeonhole inequality. -/
theorem nativePNT_exists_dyadic_depth
'''
insert = r'''private lemma nativePNT_log_two_ge_half :
    (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

private lemma nativePNT_dyadic_depth_constant_le_24 :
    2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) ≤ (24 : ℝ) := by
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog4eq : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = (2 : ℕ) * Real.log (2 : ℝ) := by rw [Real.log_pow]
      _ = 2 * Real.log (2 : ℝ) := by norm_num
  rw [hlog4eq]
  nlinarith

/-- A quantitatively calibrated dyadic depth.  The crude constants are chosen
for robust elaboration: `K + 2 <= 197 / eps`, while the PNT1/PNT2 depth
inequality still holds. -/
theorem nativePNT_exists_dyadic_depth_quantitative
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ K : ℕ,
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
          (eps / 4) * ((K : ℝ) * Real.log 2 - 1) ∧
      (((K + 2 : ℕ) : ℝ) ≤ 197 / eps) := by
  let x : ℝ := 192 / eps + 2
  let K : ℕ := ⌊x⌋₊ + 1
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxK : x < (K : ℝ) := by
    dsimp [K]
    push_cast
    simpa using (Nat.lt_floor_add_one x)
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hKupper0 : (K : ℝ) ≤ x + 1 := by
    dsimp [K]
    push_cast
    linarith
  have hloglow := nativePNT_log_two_ge_half
  have hKhalf : 96 / eps + 1 < (K : ℝ) / 2 := by
    dsimp [x] at hxK
    nlinarith
  have hKlog : 96 / eps < (K : ℝ) * Real.log 2 - 1 := by
    have hmul := mul_le_mul_of_nonneg_left hloglow
      (show (0 : ℝ) ≤ (K : ℝ) by positivity)
    nlinarith
  have hscaled := mul_lt_mul_of_pos_left hKlog
    (show (0 : ℝ) < eps / 4 by positivity)
  have hcancel : (eps / 4) * (96 / eps) = (24 : ℝ) := by
    field_simp [ne_of_gt heps]
    <;> ring
  rw [hcancel] at hscaled
  have hdepth :
      2 * (2 * (Real.log 4 + 2) + Real.log 2 + 3) <
        (eps / 4) * ((K : ℝ) * Real.log 2 - 1) :=
    nativePNT_dyadic_depth_constant_le_24.trans_lt hscaled
  have hKupper : (K : ℝ) ≤ 192 / eps + 3 := by
    dsimp [x] at hKupper0
    linarith
  have htail : 192 / eps + 5 ≤ 197 / eps := by
    rw [le_div_iff₀ heps]
    field_simp [ne_of_gt heps]
    nlinarith
  have hLupper : (((K + 2 : ℕ) : ℝ) ≤ 197 / eps) := by
    push_cast
    exact (by nlinarith [hKupper, htail])
  exact ⟨K, hdepth, hLupper⟩

/-- For every positive error tolerance one can choose a fixed dyadic search
depth large enough for the PNT1/PNT2 pigeonhole inequality. -/
theorem nativePNT_exists_dyadic_depth
'''
assert anchor in s
s = s.replace(anchor, insert, 1)

old_selector = r'''theorem nativePNT_exists_good_power_shell_selector
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
'''
new_selector = r'''theorem nativePNT_exists_good_power_shell_selector
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ K E : ℕ, ∃ t : ℕ → ℕ,
      (((K + 2 : ℕ) : ℝ) ≤ 197 / eps) ∧
      (∀ j : ℕ, 2 ^ (E + j * (K + 2)) ≤ t j) ∧
      (∀ j : ℕ, t j ≤ 2 ^ (E + j * (K + 2) + K)) ∧
      (∀ j : ℕ,
        ∀ q ∈ Finset.Icc (t j)
          (t j + nativePNTGoodForwardRadius (t j) eps),
          |nativePNTError q| ≤ eps * (q : ℝ)) := by
  classical
  rcases nativePNT_exists_dyadic_depth_quantitative eps heps heps1 with
    ⟨K, hdepth, hKupper⟩
'''
assert old_selector in s
s = s.replace(old_selector, new_selector, 1)

old_refine = '''  refine ⟨K, A₀, t, ?_, ?_, ?_⟩
  · intro j
'''
new_refine = '''  refine ⟨K, A₀, t, hKupper, ?_, ?_, ?_⟩
  · intro j
'''
assert old_refine in s
s = s.replace(old_refine, new_refine, 1)

old_head = r'''theorem nativeLambdaTwoGoodRecipMass_eventually_quadratic
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        c * (Real.log (N : ℝ)) ^ 2 ≤
          nativeLambdaTwoGoodRecipMass N eps := by
  classical
  rcases nativePNT_exists_good_power_shell_selector eps heps heps1 with
    ⟨K, E, t, htLower, htUpper, htGood⟩
'''
new_head = r'''theorem nativeLambdaTwoGoodRecipMass_eventually_quadratic_with_rate
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ c : ℝ, eps ^ 2 / 6500000 ≤ c ∧ c ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        c * (Real.log (N : ℝ)) ^ 2 ≤
          nativeLambdaTwoGoodRecipMass N eps := by
  classical
  rcases nativePNT_exists_good_power_shell_selector eps heps heps1 with
    ⟨K, E, t, hKupper, htLower, htUpper, htGood⟩
'''
assert old_head in s
s = s.replace(old_head, new_head, 1)

old_before_refine = '''  have hc1 : c ≤ 1 := by
    dsimp [c]
    have hdenpos : (0 : ℝ) < 16384 * (L : ℝ) := lt_of_lt_of_le (by norm_num) hden1
    rw [div_le_one hdenpos]
    exact hnum1.trans hden1
  refine ⟨c, hc, hc1, ?_⟩
'''
new_before_refine = r'''  have hc1 : c ≤ 1 := by
    dsimp [c]
    have hdenpos : (0 : ℝ) < 16384 * (L : ℝ) := lt_of_lt_of_le (by norm_num) hden1
    rw [div_le_one hdenpos]
    exact hnum1.trans hden1
  have hLupper : (L : ℝ) ≤ 197 / eps := by
    simpa [L] using hKupper
  have hepsL : eps * (L : ℝ) ≤ 197 := by
    have h := (le_div_iff₀ heps).mp hLupper
    simpa [mul_comm] using h
  have hepsSqL : eps ^ 2 * (L : ℝ) ≤ 197 * eps := by
    have h := mul_le_mul_of_nonneg_left hepsL heps.le
    nlinarith
  have hlogscaled : eps / 2 ≤ eps * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_left nativePNT_log_two_ge_half heps.le
    nlinarith
  have hconst : (16384 : ℝ) * 197 ≤ 6500000 / 2 := by norm_num
  have hleft :
      16384 * (eps ^ 2 * (L : ℝ)) ≤ 16384 * (197 * eps) :=
    mul_le_mul_of_nonneg_left hepsSqL (by norm_num)
  have hmid : 16384 * (197 * eps) ≤ 6500000 * (eps / 2) := by
    have h := mul_le_mul_of_nonneg_right hconst heps.le
    nlinarith
  have hright : 6500000 * (eps / 2) ≤ 6500000 * (eps * Real.log 2) :=
    mul_le_mul_of_nonneg_left hlogscaled (by norm_num)
  have hcross :
      16384 * (eps ^ 2 * (L : ℝ)) ≤
        6500000 * (eps * Real.log 2) :=
    hleft.trans (hmid.trans hright)
  have hcrate : eps ^ 2 / 6500000 ≤ c := by
    dsimp [c]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6500000)
      (by positivity : (0 : ℝ) < 16384 * (L : ℝ))]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross
  refine ⟨c, hcrate, hc1, ?_⟩
'''
assert old_before_refine in s
s = s.replace(old_before_refine, new_before_refine, 1)

end_anchor = '''  exact hcSq.trans hmassQ


/-! ## Closing the affine-envelope contraction -/
'''
end_insert = r'''  exact hcSq.trans hmassQ

/-- Qualitative wrapper for callers that only need positivity of the quadratic
mass coefficient. -/
theorem nativeLambdaTwoGoodRecipMass_eventually_quadratic
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        c * (Real.log (N : ℝ)) ^ 2 ≤
          nativeLambdaTwoGoodRecipMass N eps := by
  rcases nativeLambdaTwoGoodRecipMass_eventually_quadratic_with_rate
      eps heps heps1 with ⟨c, hcrate, hc1, hgood⟩
  have hc : 0 < c :=
    (show 0 < eps ^ 2 / 6500000 by positivity).trans_le hcrate
  exact ⟨c, hc, hc1, hgood⟩

/-- Explicit quadratic good-mass density.  This is the calibrated interface
used by the cubic slope recurrence. -/
theorem nativeLambdaTwoGoodRecipMass_eventually_quadratic_rate
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      (eps ^ 2 / 6500000) * (Real.log (N : ℝ)) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N eps := by
  rcases nativeLambdaTwoGoodRecipMass_eventually_quadratic_with_rate
      eps heps heps1 with ⟨c, hcrate, _hc1, hgood⟩
  filter_upwards [hgood] with N hN
  exact (mul_le_mul_of_nonneg_right hcrate (sq_nonneg _)).trans hN


/-! ## Closing the affine-envelope contraction -/
'''
assert end_anchor in s
s = s.replace(end_anchor, end_insert, 1)

p.write_text(s)
