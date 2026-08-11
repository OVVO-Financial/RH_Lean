from pathlib import Path

p = Path('RHLean/Analysis/NativePNTErdosContraction.lean')
s = p.read_text()
assert 'nativePNT_reciprocal_radius_gap' not in s
marker = '\nend RHLean.Analysis\n'
assert s.count(marker) == 1
block = r'''

/-! ## Quantitative mass from one good PNT2 radius -/

/-- A PNT2 radius produces a fixed relative gap after reciprocal-floor
reindexing.  The hypothesis `32 ≤ eps * floor(N/t)` absorbs the two integer
floor errors. -/
theorem nativePNT_reciprocal_radius_gap
    (N t : ℕ) (eps : ℝ)
    (ht : 1 ≤ t) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hB : 32 ≤ eps * ((N / t : ℕ) : ℝ)) :
    ((N / (t + nativePNTGoodForwardRadius t eps + 1) : ℕ) : ℝ) ≤
      (1 - eps / 32) * ((N / t : ℕ) : ℝ) := by
  let H : ℕ := nativePNTGoodForwardRadius t eps
  let B : ℝ := ((N / t : ℕ) : ℝ)
  let d : ℕ := t + H + 1
  have htpos : 0 < t := by omega
  have htRpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
  have hB' : 32 ≤ eps * B := by simpa [B] using hB
  have hrad : eps * (t : ℝ) / 8 < (H : ℝ) + 1 := by
    dsimp [H, nativePNTGoodForwardRadius]
    simpa using (Nat.lt_floor_add_one (eps * (t : ℝ) / 8))
  have hdR : (1 + eps / 8) * (t : ℝ) < (d : ℝ) := by
    dsimp [d]
    push_cast
    nlinarith [hrad]
  have hmod := Nat.mod_lt N htpos
  have hNupperNat : N < (N / t + 1) * t := by
    calc
      N = N / t * t + N % t := (Nat.div_add_mod N t).symm
      _ < N / t * t + t := Nat.add_lt_add_left hmod _
      _ = (N / t + 1) * t := by ring
  have hNupper : (N : ℝ) < (B + 1) * (t : ℝ) := by
    dsimp [B]
    exact_mod_cast hNupperNat
  have hBpos : 0 < B := by
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    nlinarith
  have heps0 : 0 ≤ eps := heps.le
  have hepssq : eps ^ 2 ≤ eps := by nlinarith
  have hsquareB : eps ^ 2 * B ≤ eps * B :=
    mul_le_mul_of_nonneg_right hepssq hBpos.le
  have hratio :
      B + 1 ≤ (1 - eps / 32) * B * (1 + eps / 8) := by
    nlinarith [hB', hsquareB]
  have hratio_t := mul_le_mul_of_nonneg_right hratio htRpos.le
  have hfactor : 0 < 1 - eps / 32 := by nlinarith
  have htargetpos : 0 < (1 - eps / 32) * B :=
    mul_pos hfactor hBpos
  have hdenScaled := mul_lt_mul_of_pos_left hdR htargetpos
  have hNtarget :
      (N : ℝ) < ((1 - eps / 32) * B) * (d : ℝ) := by
    calc
      (N : ℝ) < (B + 1) * (t : ℝ) := hNupper
      _ ≤ ((1 - eps / 32) * B * (1 + eps / 8)) * (t : ℝ) := hratio_t
      _ = ((1 - eps / 32) * B) * ((1 + eps / 8) * (t : ℝ)) := by ring
      _ < ((1 - eps / 32) * B) * (d : ℝ) := hdenScaled
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdRpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hquot :
      (N : ℝ) / (d : ℝ) < (1 - eps / 32) * B := by
    rw [div_lt_iff₀ hdRpos]
    simpa [mul_comm] using hNtarget
  have hfloor : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdRpos]
    exact_mod_cast Nat.div_mul_le_self N d
  simpa [d, H, B] using hfloor.trans hquot.le

/-- The reciprocal interval attached to one sufficiently deep PNT2 radius has
a positive `Lambda_2/n` mass of size `eps * log(N/t)`. -/
theorem nativeLambdaTwoRecipIntervalMass_good_radius_lower
    (N t : ℕ) (eps : ℝ)
    (ht : 1 ≤ t) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hA : 3 ≤ N / (t + nativePNTGoodForwardRadius t eps + 1))
    (hB : 32 ≤ eps * ((N / t : ℕ) : ℝ))
    (hlog :
      64 * (2 * (Real.log 4 + 2) + 172) ≤
        eps * Real.log ((N / t : ℕ) : ℝ)) :
    (eps / 32) * Real.log ((N / t : ℕ) : ℝ) ≤
      nativeLambdaTwoRecipIntervalMass
        (N / (t + nativePNTGoodForwardRadius t eps + 1))
        (N / t) := by
  have hden : t ≤ t + nativePNTGoodForwardRadius t eps + 1 := by omega
  have hAB :
      N / (t + nativePNTGoodForwardRadius t eps + 1) ≤ N / t :=
    Nat.div_le_div_left hden (by omega)
  have hgap := nativePNT_reciprocal_radius_gap N t eps ht heps heps1 hB
  have hlog' :
      2 * (2 * (Real.log 4 + 2) + 172) ≤
        (eps / 32) * Real.log ((N / t : ℕ) : ℝ) := by
    nlinarith [hlog]
  exact nativeLambdaTwoRecipIntervalMass_gap_lower
    (N / (t + nativePNTGoodForwardRadius t eps + 1))
    (N / t) (eps / 32) hA hAB hgap hlog'

/-- One sufficiently deep PNT2 interval therefore contributes the same
quantitative lower bound directly to the global good-fibre compensation mass. -/
theorem nativeLambdaTwoGoodRecipMass_good_radius_lower
    (N t : ℕ) (eps : ℝ)
    (ht : 1 ≤ t) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hA : 3 ≤ N / (t + nativePNTGoodForwardRadius t eps + 1))
    (hB : 32 ≤ eps * ((N / t : ℕ) : ℝ))
    (hlog :
      64 * (2 * (Real.log 4 + 2) + 172) ≤
        eps * Real.log ((N / t : ℕ) : ℝ))
    (hgood : ∀ q ∈ Finset.Icc t
      (t + nativePNTGoodForwardRadius t eps),
      |nativePNTError q| ≤ eps * (q : ℝ)) :
    (eps / 32) * Real.log ((N / t : ℕ) : ℝ) ≤
      nativeLambdaTwoGoodRecipMass N eps := by
  have hlocal := nativeLambdaTwoRecipIntervalMass_good_radius_lower
    N t eps ht heps heps1 hA hB hlog
  have htoGood :=
    nativeLambdaTwoRecipIntervalMass_le_good_of_good_quotient_interval
      N t (nativePNTGoodForwardRadius t eps) eps ht heps.le hgood
  exact hlocal.trans htoGood
'''
s = s.replace(marker, block + marker)
p.write_text(s)
