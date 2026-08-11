from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativeLambdaTwoGoodRecipMass_eventually_quadratic' not in s
marker = '\nend RHLean.Analysis\n'
assert s.count(marker) == 1
block = r'''

/-- **Quadratic logarithmic density of good reciprocal fibres.**  For every
fixed `0 < eps <= 1`, the PNT2 good intervals supplied on separated dyadic
shells contribute a positive fixed multiple of `log^2 N` to the reciprocal
`Lambda_2` compensation mass.  This is the quantitative packing step that
closes the Selberg--Erdos contraction. -/
theorem nativeLambdaTwoGoodRecipMass_eventually_quadratic
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        c * (Real.log (N : ℝ)) ^ 2 ≤
          nativeLambdaTwoGoodRecipMass N eps := by
  classical
  rcases nativePNT_exists_good_power_shell_selector eps heps heps1 with
    ⟨K, E, t, htLower, htUpper, htGood⟩
  let L : ℕ := K + 2
  have hLpos : 0 < L := by dsimp [L]; omega
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  let C : ℝ := 2 * (Real.log 4 + 2) + 172
  obtain ⟨M_B : ℕ, hM_Bnat⟩ := exists_nat_gt (32 / eps)
  have hM_B : 32 / eps < (M_B : ℝ) := by exact_mod_cast hM_Bnat
  obtain ⟨M_log : ℕ, hM_lognat⟩ :=
    exists_nat_gt (64 * C / (eps * Real.log 2))
  have hM_log : 64 * C / (eps * Real.log 2) < (M_log : ℝ) := by
    exact_mod_cast hM_lognat
  let c : ℝ := eps * Real.log 2 / (8192 * (L : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hden1 : (1 : ℝ) ≤ 8192 * (L : ℝ) := by
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.2 hLpos.ne')
    nlinarith
  have hnum1 : eps * Real.log 2 ≤ 1 := by
    have hnonneg : 0 ≤ Real.log (2 : ℝ) := hlog2pos.le
    have := mul_le_mul heps1 hlog2le hnonneg heps.le
    simpa using this
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have hdenpos : (0 : ℝ) < 8192 * (L : ℝ) := lt_of_lt_of_le (by norm_num) hden1
    rw [div_le_one hdenpos]
    exact hnum1.trans hden1
  refine ⟨c, hc, hc1, ?_⟩
  have hqTop : Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop (2 ^ b)] with N hN
    exact Nat.le_log_of_pow_le Nat.one_lt_two hN
  let Q : ℕ := max
    (8 * (E + K + 2))
    (max (16 * L) (max 8 (max (4 * M_B) (4 * M_log))))
  have hqLarge : ∀ᶠ N : ℕ in atTop, Q ≤ Nat.log 2 N :=
    hqTop.eventually_ge_atTop Q
  filter_upwards [eventually_ge_atTop 1, hqLarge] with N hN1 hqQ
  let q : ℕ := Nat.log 2 N
  let J : ℕ := q / (8 * L)
  let M : ℕ := 2 ^ (q / 4)
  have hNne : N ≠ 0 := by omega
  have hqE : 8 * (E + K + 2) ≤ q := by
    dsimp [Q, q] at hqQ ⊢
    exact le_trans (le_max_left _ _) hqQ
  have hqJL : 16 * L ≤ q := by
    dsimp [Q, q] at hqQ ⊢
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hqQ)
  have hq8 : 8 ≤ q := by
    dsimp [Q, q] at hqQ ⊢
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) hqQ))
  have hqMB : 4 * M_B ≤ q := by
    dsimp [Q, q] at hqQ ⊢
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hqQ)))
  have hqMlog : 4 * M_log ≤ q := by
    dsimp [Q, q] at hqQ ⊢
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hqQ)))
  have hq4two : 2 ≤ q / 4 := by omega
  have hMBq : M_B ≤ q / 4 := by
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2 (by simpa [Nat.mul_comm] using hqMB)
  have hMlogq : M_log ≤ q / 4 := by
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2 (by simpa [Nat.mul_comm] using hqMlog)
  have hMfour : 4 ≤ M := by
    dsimp [M]
    have := (Nat.pow_le_pow_iff_right Nat.one_lt_two).2 hq4two
    norm_num at this ⊢
    exact this
  have hpowq : 2 ^ q ≤ N := by
    dsimp [q]
    exact Nat.pow_log_le_self 2 hNne
  have htOne : ∀ j < J, 1 ≤ t j := by
    intro j _hj
    have hpowpos : 0 < 2 ^ (E + j * L) := by positivity
    have hlow : 2 ^ (E + j * L) ≤ t j := by
      simpa [L] using htLower j
    omega
  have hsep : ∀ i j, i < j → j < J →
      t i + nativePNTGoodForwardRadius (t i) eps < t j := by
    intro i j hij _hjJ
    have hrad := nativePNTGoodForwardRadius_le_self (t i) eps heps.le heps1
    have hui : t i ≤ 2 ^ (E + i * L + K) := by
      simpa [L] using htUpper i
    have hlj : 2 ^ (E + j * L) ≤ t j := by
      simpa [L] using htLower j
    have hexp : E + i * L + K + 1 < E + j * L := by
      have hji : i + 1 ≤ j := by omega
      have hmul : (i + 1) * L ≤ j * L := Nat.mul_le_mul_right L hji
      dsimp [L] at hmul ⊢
      omega
    have hp : 2 ^ (E + i * L + K + 1) < 2 ^ (E + j * L) :=
      Nat.pow_lt_pow_right Nat.one_lt_two hexp
    have htwo : 2 * t i ≤ 2 ^ (E + i * L + K + 1) := by
      calc
        2 * t i ≤ 2 * 2 ^ (E + i * L + K) := Nat.mul_le_mul_left 2 hui
        _ = 2 ^ (E + i * L + K + 1) := by rw [pow_succ]; ring
    have hsum : t i + nativePNTGoodForwardRadius (t i) eps ≤ 2 * t i := by omega
    exact hsum.trans_lt (htwo.trans_lt (hp.trans_le hlj))
  have hJmul : J * (8 * L) ≤ q := by
    dsimp [J]
    exact Nat.div_mul_le_self q (8 * L)
  have hLocalQuot : ∀ j < J,
      M ≤ N / (t j + nativePNTGoodForwardRadius (t j) eps + 1) := by
    intro j hjJ
    have hjstep : (j + 1) * (8 * L) ≤ q := by
      have hj1 : j + 1 ≤ J := by omega
      exact (Nat.mul_le_mul_right (8 * L) hj1).trans hJmul
    have hexpQ : E + j * L + K + 2 ≤ q / 4 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
      have hEpart : 8 * (E + K + 2) ≤ q := hqE
      dsimp [L] at hjstep ⊢
      omega
    have hrad := nativePNTGoodForwardRadius_le_self (t j) eps heps.le heps1
    have htj1 : 1 ≤ t j := htOne j hjJ
    have hud : t j + nativePNTGoodForwardRadius (t j) eps + 1 ≤ 4 * t j := by
      omega
    have hut : t j ≤ 2 ^ (E + j * L + K) := by
      simpa [L] using htUpper j
    have hdPow :
        t j + nativePNTGoodForwardRadius (t j) eps + 1 ≤
          2 ^ (E + j * L + K + 2) := by
      calc
        t j + nativePNTGoodForwardRadius (t j) eps + 1 ≤ 4 * t j := hud
        _ ≤ 4 * 2 ^ (E + j * L + K) := Nat.mul_le_mul_left 4 hut
        _ = 2 ^ (E + j * L + K + 2) := by
          rw [show E + j * L + K + 2 = (E + j * L + K) + 2 by omega, pow_add]
          norm_num
    have hsumExp : E + j * L + K + 2 + q / 4 ≤ q := by
      have hqq : q / 4 + q / 4 ≤ q := by omega
      omega
    have hpowExp :
        2 ^ (E + j * L + K + 2 + q / 4) ≤ 2 ^ q :=
      (Nat.pow_le_pow_iff_right Nat.one_lt_two).2 hsumExp
    have hdM :
        (t j + nativePNTGoodForwardRadius (t j) eps + 1) * M ≤ N := by
      calc
        (t j + nativePNTGoodForwardRadius (t j) eps + 1) * M ≤
            2 ^ (E + j * L + K + 2) * 2 ^ (q / 4) :=
          Nat.mul_le_mul hdPow le_rfl
        _ = 2 ^ (E + j * L + K + 2 + q / 4) := by rw [← pow_add]
        _ ≤ 2 ^ q := hpowExp
        _ ≤ N := hpowq
    have hdpos : 0 < t j + nativePNTGoodForwardRadius (t j) eps + 1 := by omega
    exact (Nat.le_div_iff_mul_le hdpos).2 hdM
  have hLocalB : ∀ j < J, M ≤ N / t j := by
    intro j hjJ
    have hd := hLocalQuot j hjJ
    have hden : t j ≤ t j + nativePNTGoodForwardRadius (t j) eps + 1 := by omega
    exact hd.trans (Nat.div_le_div_left hden (by omega))
  have hA : ∀ j < J,
      3 ≤ N / (t j + nativePNTGoodForwardRadius (t j) eps + 1) := by
    intro j hj
    exact (by omega : 3 ≤ M).trans (hLocalQuot j hj)
  have hMBpow : M_B ≤ M := by
    have hself : M_B ≤ 2 ^ M_B := (Nat.lt_pow_self Nat.one_lt_two).le
    have hp : 2 ^ M_B ≤ 2 ^ (q / 4) :=
      (Nat.pow_le_pow_iff_right Nat.one_lt_two).2 hMBq
    exact hself.trans hp
  have hBbase : 32 ≤ eps * (M : ℝ) := by
    have hMBreal : (M_B : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMBpow
    have h32MB : 32 < eps * (M_B : ℝ) := by
      have h := (div_lt_iff₀ heps).mp hM_B
      simpa [mul_comm] using h
    have hmul := mul_le_mul_of_nonneg_left hMBreal heps.le
    linarith
  have hB : ∀ j < J, 32 ≤ eps * ((N / t j : ℕ) : ℝ) := by
    intro j hj
    have hcast : (M : ℝ) ≤ ((N / t j : ℕ) : ℝ) := by exact_mod_cast hLocalB j hj
    exact hBbase.trans (mul_le_mul_of_nonneg_left hcast heps.le)
  have hMlogpow : M_log ≤ q / 4 := hMlogq
  have hlogM :
      ((q / 4 : ℕ) : ℝ) * Real.log 2 = Real.log (M : ℝ) := by
    dsimp [M]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hlogBase : 64 * C ≤ eps * Real.log (M : ℝ) := by
    have hdenpos : 0 < eps * Real.log 2 := mul_pos heps hlog2pos
    have hCML : 64 * C < (M_log : ℝ) * (eps * Real.log 2) := by
      have h := (div_lt_iff₀ hdenpos).mp hM_log
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hMLq : (M_log : ℝ) ≤ ((q / 4 : ℕ) : ℝ) := by exact_mod_cast hMlogpow
    have hmul := mul_le_mul_of_nonneg_right hMLq hdenpos.le
    rw [← hlogM]
    nlinarith
  have hlog : ∀ j < J,
      64 * (2 * (Real.log 4 + 2) + 172) ≤
        eps * Real.log ((N / t j : ℕ) : ℝ) := by
    intro j hj
    have hBpos : 0 < M := by positivity
    have hcast := hLocalB j hj
    have hlogle : Real.log (M : ℝ) ≤ Real.log ((N / t j : ℕ) : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast hBpos
      · exact_mod_cast hcast
    have hmul := mul_le_mul_of_nonneg_left hlogle heps.le
    dsimp [C] at hlogBase ⊢
    exact hlogBase.trans hmul
  have hpacked := nativeLambdaTwoGoodRecipMass_packed_good_radii_lower
    N J eps t heps heps1 htOne
    (fun j _hj => htGood j) hsep hA hB hlog
  have hterm : ∀ j < J,
      (eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2) ≤
        (eps / 32) * Real.log ((N / t j : ℕ) : ℝ) := by
    intro j hj
    have hlogle : Real.log (M : ℝ) ≤ Real.log ((N / t j : ℕ) : ℝ) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast hLocalB j hj
    rw [hlogM]
    exact mul_le_mul_of_nonneg_left hlogle (by positivity)
  have hsumTerm :
      ((J : ℕ) : ℝ) *
          ((eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2)) ≤
        ∑ j ∈ Finset.range J,
          (eps / 32) * Real.log ((N / t j : ℕ) : ℝ) := by
    have hcard := Finset.card_nsmul_le_sum (Finset.range J)
      (fun j => (eps / 32) * Real.log ((N / t j : ℕ) : ℝ))
      ((eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2))
      (by
        intro j hj
        exact hterm j (Finset.mem_range.mp hj))
    rw [Finset.card_range, nsmul_eq_mul] at hcard
    exact hcard
  have hdpos : 0 < 8 * L := by positivity
  have hqDecomp : 8 * L * J + q % (8 * L) = q := by
    dsimp [J]
    exact Nat.div_add_mod q (8 * L)
  have hmod : q % (8 * L) < 8 * L := Nat.mod_lt q hdpos
  have hJlowerNat : q ≤ 16 * L * J := by
    omega
  have hJlower : (q : ℝ) ≤ 16 * (L : ℝ) * (J : ℝ) := by
    exact_mod_cast hJlowerNat
  have hqdiv4 : (q : ℝ) / 8 ≤ ((q / 4 : ℕ) : ℝ) := by
    have hdiv : q ≤ 2 * (q / 4) + 6 := by omega
    have hq8R : (8 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq8
    have : (6 : ℝ) ≤ (3 / 4 : ℝ) * (q : ℝ) := by nlinarith
    exact_mod_cast (show (0 : ℕ) ≤ q / 4 by omega) at *
    nlinarith
  have hmassQ :
      eps * Real.log 2 / (4096 * (L : ℝ)) * (q : ℝ) ^ 2 ≤
        nativeLambdaTwoGoodRecipMass N eps := by
    have hJreal : (q : ℝ) / (16 * (L : ℝ)) ≤ (J : ℝ) := by
      have hLr : 0 < (L : ℝ) := by exact_mod_cast hLpos
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (L : ℝ))]
      nlinarith [hJlower]
    have htermQ :
        (eps / 32) * (((q : ℝ) / 8) * Real.log 2) ≤
          (eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2) := by
      have hmul := mul_le_mul_of_nonneg_right hqdiv4 hlog2pos.le
      exact mul_le_mul_of_nonneg_left hmul (by positivity)
    have hprod := mul_le_mul hJreal htermQ
      (by positivity)
      (by positivity)
    calc
      eps * Real.log 2 / (4096 * (L : ℝ)) * (q : ℝ) ^ 2 ≤
          ((J : ℕ) : ℝ) *
            ((eps / 32) * (((q / 4 : ℕ) : ℝ) * Real.log 2)) := by
        convert hprod using 1 <;> field_simp [show (L : ℝ) ≠ 0 by exact_mod_cast hLpos.ne'] <;> ring
      _ ≤ ∑ j ∈ Finset.range J,
          (eps / 32) * Real.log ((N / t j : ℕ) : ℝ) := hsumTerm
      _ ≤ nativeLambdaTwoGoodRecipMass N eps := hpacked
  have hNpow : N < 2 ^ (q + 1) := by
    dsimp [q]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self Nat.one_lt_two N
  have hlogNnonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  have hlogNupper : Real.log (N : ℝ) ≤ 2 * (q : ℝ) := by
    have hpowpos : (0 : ℝ) < ((2 ^ (q + 1) : ℕ) : ℝ) := by positivity
    have hcast : (N : ℝ) ≤ ((2 ^ (q + 1) : ℕ) : ℝ) := by exact_mod_cast hNpow.le
    have hlogle := Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hcast
    have hlogpow : Real.log ((2 ^ (q + 1) : ℕ) : ℝ) =
        ((q + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [Nat.cast_pow, Real.log_pow]
    rw [hlogpow] at hlogle
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    have hmul := mul_le_mul_of_nonneg_left hlog2le (by positivity : (0 : ℝ) ≤ ((q + 1 : ℕ) : ℝ))
    push_cast at hmul
    nlinarith
  have hsq : (Real.log (N : ℝ)) ^ 2 ≤ 4 * (q : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (N : ℝ) - 2 * (q : ℝ))]
  have hcSq : c * (Real.log (N : ℝ)) ^ 2 ≤
      eps * Real.log 2 / (4096 * (L : ℝ)) * (q : ℝ) ^ 2 := by
    dsimp [c]
    have hcoef : 0 ≤ eps * Real.log 2 / (8192 * (L : ℝ)) := hc.le
    have h := mul_le_mul_of_nonneg_left hsq hcoef
    nlinarith
  exact hcSq.trans hmassQ
'''
s = s.replace(marker, block + marker)
p.write_text(s)
