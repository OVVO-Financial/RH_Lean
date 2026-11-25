import Mathlib

/-!
# Single-prime physical weighted recovery

Native scalar and finite-cofactor suppliers for the research PR. The physical
carrier is not replaced by an assumed rank, and no RH-scale signed estimate is
a premise or conclusion here. The accompanying paper gives the actual wheel
specialization, the paid deep-power tail, and the remaining signed comparison.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Research.SinglePrimePhysicalRecovery

def baseWeight (N x : ℝ) : ℝ := N / x - 1

def logWeight (N x : ℝ) : ℝ := Real.log x * baseWeight N x

theorem baseWeight_nonneg (N x : ℝ) (hx : 0 < x) (hxN : x ≤ N) :
    0 ≤ baseWeight N x := by
  unfold baseWeight
  exact sub_nonneg.mpr ((le_div_iff₀ hx).2 (by simpa using hxN))

theorem logWeight_nonneg (N x : ℝ) (hx : 1 ≤ x) (hxN : x ≤ N) :
    0 ≤ logWeight N x :=
  mul_nonneg (Real.log_nonneg hx)
    (baseWeight_nonneg N x (lt_of_lt_of_le zero_lt_one hx) hxN)

/-- Exact scale law, including the nonhomogeneous endpoint cost. -/
theorem scaled_base (N d x : ℝ) (hd : 0 < d) (hx : 0 < x) :
    d * baseWeight N (d * x) = baseWeight N x - (d - 1) := by
  unfold baseWeight
  field_simp [ne_of_gt hd, ne_of_gt hx]
  ring

theorem scaled_log (N d x : ℝ) (hd : 0 < d) (hx : 0 < x) :
    d * logWeight N (d * x) =
      logWeight N x + Real.log d * baseWeight N x -
        (d - 1) * Real.log (d * x) := by
  calc
    _ = Real.log (d * x) * (d * baseWeight N (d * x)) := by
      unfold logWeight
      ring
    _ = _ := by
      rw [scaled_base N d x hd hx]
      unfold logWeight
      rw [Real.log_mul (ne_of_gt hd) (ne_of_gt hx)]
      ring

/-- The actual one-depth signed cost after introducing a scaled weight and
an attenuation change. No term of either sign is discarded. -/
theorem scaled_signed (N d x a b : ℝ) (hd : 0 < d) (hx : 0 < x) :
    d * (b * logWeight N (d * x)) - a * logWeight N x =
      b * Real.log d * baseWeight N x -
        (d - 1) * b * Real.log (d * x) -
        (a - b) * logWeight N x := by
  calc
    _ = b * (d * logWeight N (d * x)) - a * logWeight N x := by ring
    _ = _ := by rw [scaled_log N d x hd hx]; ring

/-- The unlogged measure contracts by the literal reciprocal dilation. -/
theorem baseWeight_scale_le (N d x : ℝ) (hd : 1 ≤ d) (hx : 0 < x) :
    baseWeight N (d * x) ≤ baseWeight N x / d := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  apply (le_div_iff₀ hd0).2
  rw [mul_comm (baseWeight N (d * x)) d, scaled_base N d x hd0 hx]
  linarith

/-- Logarithmic weight contracts on the ancestor carrier. The hypothesis
p <= x is supplied by the actual old-wheel rough cofactor, not a density. -/
theorem logWeight_scale_le (N p x : ℝ) (k : ℕ)
    (hp : 1 < p) (hx : p ≤ x) (hN : p ^ k * x ≤ N) :
    logWeight N (p ^ k * x) ≤
      (((k : ℝ) + 1) / p ^ k) * logWeight N x := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hx0 : 0 < x := lt_of_lt_of_le hp0 hx
  have hd0 : 0 < p ^ k := pow_pos hp0 k
  have hd1 : 1 ≤ p ^ k := one_le_pow₀ hp.le
  have hx1 : 1 ≤ x := le_trans hp.le hx
  have hxd : x ≤ p ^ k * x := by
    simpa using mul_le_mul_of_nonneg_right hd1 hx0.le
  have hxN : x ≤ N := hxd.trans hN
  have hbase : 0 ≤ baseWeight N x := baseWeight_nonneg N x hx0 hxN
  have hlog : Real.log (p ^ k) ≤ (k : ℝ) * Real.log x := by
    rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hp0 hx) (Nat.cast_nonneg k)
  have hg := mul_le_mul_of_nonneg_right hlog hbase
  have hc : 0 ≤ (p ^ k - 1) * Real.log (p ^ k * x) :=
    mul_nonneg (sub_nonneg.mpr hd1) (Real.log_nonneg (hx1.trans hxd))
  have hscaled : p ^ k * logWeight N (p ^ k * x) ≤
      ((k : ℝ) + 1) * logWeight N x := by
    rw [scaled_log N (p ^ k) x hd0 hx0]
    calc
      _ ≤ logWeight N x + Real.log (p ^ k) * baseWeight N x :=
        sub_le_self _ hc
      _ ≤ logWeight N x + ((k : ℝ) * Real.log x) * baseWeight N x :=
        add_le_add (le_refl (logWeight N x)) hg
      _ = _ := by unfold logWeight; ring
  calc
    _ = (p ^ k * logWeight N (p ^ k * x)) / p ^ k := by
      field_simp [ne_of_gt hd0]
    _ ≤ (((k : ℝ) + 1) * logWeight N x) / p ^ k :=
      div_le_div_of_nonneg_right hscaled hd0.le
    _ = _ := by ring

/-- The finite physical layer is pushed into its actual cofactor image.
Attenuation may decrease on moving from an ancestor to its descendant. -/
theorem weighted_cofactor_layer_le (J : Finset ℕ) (N p k : ℕ)
    (a : ℕ → ℝ) (hp : 2 ≤ p)
    (hdiv : ∀ n ∈ J, p ^ k ∣ n)
    (hphys : ∀ n ∈ J, p ≤ n / p ^ k ∧ n ≤ N)
    (ha : ∀ n ∈ J, 0 ≤ a n ∧ a n ≤ a (n / p ^ k)) :
    (∑ n ∈ J, a n * logWeight (N : ℝ) (n : ℝ)) ≤
      (((k : ℝ) + 1) / (p : ℝ) ^ k) *
        ∑ m ∈ J.image (fun n => n / p ^ k), a m * logWeight (N : ℝ) (m : ℝ) := by
  classical
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  calc
    _ ≤ ∑ n ∈ J, (((k : ℝ) + 1) / (p : ℝ) ^ k) *
        (a (n / p ^ k) * logWeight (N : ℝ) ((n / p ^ k : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hmul : p ^ k * (n / p ^ k) = n := Nat.mul_div_cancel' (hdiv n hn)
      have hmulR : (p : ℝ) ^ k * ((n / p ^ k : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast hmul
      have hpx : (p : ℝ) ≤ ((n / p ^ k : ℕ) : ℝ) := by
        exact_mod_cast (hphys n hn).1
      have hxN : (p : ℝ) ^ k * ((n / p ^ k : ℕ) : ℝ) ≤ (N : ℝ) := by
        rw [hmulR]
        exact_mod_cast (hphys n hn).2
      have hscale := logWeight_scale_le (N : ℝ) (p : ℝ)
        ((n / p ^ k : ℕ) : ℝ) k hpR hpx hxN
      rw [hmulR] at hscale
      have hn1 : 1 ≤ n := by
        have h1 := Nat.div_le_self n (p ^ k)
        have h2 := (hphys n hn).1
        omega
      have hw : 0 ≤ logWeight (N : ℝ) (n : ℝ) :=
        logWeight_nonneg _ _ (by exact_mod_cast hn1)
          (by exact_mod_cast (hphys n hn).2)
      calc
        _ ≤ a (n / p ^ k) * logWeight (N : ℝ) (n : ℝ) :=
          mul_le_mul_of_nonneg_right (ha n hn).2 hw
        _ ≤ a (n / p ^ k) *
            ((((k : ℝ) + 1) / (p : ℝ) ^ k) *
              logWeight (N : ℝ) ((n / p ^ k : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hscale ((ha n hn).1.trans (ha n hn).2)
        _ = _ := by ring
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_image]
      intro x hx y hy hxy
      change x / p ^ k = y / p ^ k at hxy
      calc
        x = p ^ k * (x / p ^ k) := (Nat.mul_div_cancel' (hdiv x hx)).symm
        _ = p ^ k * (y / p ^ k) := by rw [hxy]
        _ = y := Nat.mul_div_cancel' (hdiv y hy)

/-- Signed decomposition of an actual finite carrier into active cofactors
and excluded top-tail cofactors. No quantitative bound is hidden here. -/
theorem finite_signed_ledger (F : Finset ℕ) (N d : ℝ)
    (a b : ℕ → ℝ) (active : ℕ → Prop) [DecidablePred active]
    (hd : 0 < d) (hx : ∀ m ∈ F, 0 < (m : ℝ)) :
    d * (∑ m ∈ F.filter active, b m * logWeight N (d * (m : ℝ))) -
      (∑ m ∈ F, a m * logWeight N (m : ℝ)) =
      (∑ m ∈ F.filter active,
        (b m * Real.log d * baseWeight N (m : ℝ) -
          (d - 1) * b m * Real.log (d * (m : ℝ)) -
          (a m - b m) * logWeight N (m : ℝ))) -
      (∑ m ∈ F.filter (fun m => ¬ active m), a m * logWeight N (m : ℝ)) := by
  classical
  simp only [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases ha : active m
  · simpa [ha] using scaled_signed N d (m : ℝ) (a m) (b m) hd (hx m hm)
  · simp [ha]

/-- Positive physical weight admits the elementary harmonic majorant. -/
theorem logWeight_le_harmonic (N x : ℝ) (hx : 1 ≤ x) (hN : x ≤ N) :
    logWeight N x ≤ N * Real.log N / x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hN0 : 0 ≤ N := (zero_lt_one.le.trans hx).trans hN
  unfold logWeight baseWeight
  calc
    _ ≤ Real.log x * (N / x) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.log_nonneg hx)
    _ ≤ Real.log N * (N / x) :=
      mul_le_mul_of_nonneg_right (Real.log_le_log hx0 hN) (div_nonneg hN0 hx0.le)
    _ = _ := by ring

/-- Geometrically contracting exceptional *mass* has a summable cost. -/
theorem finite_geom_sum_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (L : ℕ) :
    (∑ j ∈ Finset.range L, r ^ j) ≤ 1 / (1 - r) := by
  have htel : (∑ j ∈ Finset.range L, r ^ j) * (1 - r) = 1 - r ^ L := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
      ring
  apply (le_div_iff₀ (sub_pos.mpr hr1)).2
  rw [htel]
  linarith [pow_nonneg hr0 L]

/-- At p^K >= R*p the whole finite depth tail is at most 1/(R*(p-1)). -/
theorem reciprocal_depth_tail_le (p R : ℝ) (hp : 1 < p) (hR : 0 < R)
    (K L : ℕ) (hcut : R * p ≤ p ^ K) :
    (∑ j ∈ Finset.range L, (1 / p) ^ (K + j)) ≤ 1 / (R * (p - 1)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hr0 : 0 ≤ 1 / p := div_nonneg zero_le_one hp0.le
  have hr1 : 1 / p < 1 := (div_lt_iff₀ hp0).2 (by simpa using hp)
  have hd : 0 < 1 - 1 / p := sub_pos.mpr hr1
  have hc : (1 / p) ^ K ≤ 1 / (R * p) := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (mul_pos hR hp0) hcut
  calc
    _ = (1 / p) ^ K * (∑ j ∈ Finset.range L, (1 / p) ^ j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add]
    _ ≤ (1 / p) ^ K * (1 / (1 - 1 / p)) :=
      mul_le_mul_of_nonneg_left (finite_geom_sum_le (1 / p) hr0 hr1 L)
        (pow_nonneg hr0 K)
    _ ≤ (1 / (R * p)) * (1 / (1 - 1 / p)) :=
      mul_le_mul_of_nonneg_right hc (div_nonneg zero_le_one hd.le)
    _ = _ := by
      field_simp [ne_of_gt hp0, ne_of_gt hR, ne_of_gt hd, ne_of_gt (sub_pos.mpr hp)]

/-- Coordinate-support counterexample on an actual square block.
There are no pure powers of 13 in this interval. -/
def witnessSites : Finset ℕ :=
  (Finset.Icc 2809 2915).filter (fun n => Nat.Coprime n 2310)

def witnessLayer (k : ℕ) : Finset ℕ :=
  witnessSites.filter (fun n => 13 ^ k ∣ n)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem nested_witness :
    witnessSites.card = 22 ∧ (witnessLayer 1).card = 2 ∧
    (witnessLayer 2).card = 1 ∧
    (witnessLayer 1 ∩ witnessLayer 2).card = 1 ∧
    ¬ witnessSites.card * (witnessLayer 1 ∩ witnessLayer 2).card ≤
      (witnessLayer 1).card * (witnessLayer 2).card := by
  decide

#print axioms scaled_log
#print axioms logWeight_scale_le
#print axioms weighted_cofactor_layer_le
#print axioms finite_signed_ledger
#print axioms reciprocal_depth_tail_le
#print axioms nested_witness

end RHLean.Research.SinglePrimePhysicalRecovery
