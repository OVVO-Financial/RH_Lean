import «research.VF_919_NATIVE_EXTERIOR_PARTIAL_MOMENT_20261020»
import «research.VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP»

/-!
# Exact multiplicative-antiderivative partition and period-three cofactor cutoff

These theorems are conditional ONLY on the explicitly displayed monotone,
smooth antiderivative profile properties. They do not construct the input
antiderivative from a particular η; that analytic construction must be
supplied separately before claiming a full concrete SourceData witness.

Every conclusion below is algebraic and uses genuine physical integer
Moebius sites (not a surrogate character or modeled source).

The period-three prefix difference is bounded by ONE independently of
interval width. Bounding the total low-norm mass still requires an ideal
counting estimate and |mu_F| <= 1; neither is assumed implicitly.

This file does not assert the missing 7/8 signed covariance bound.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace RHLean.Analysis

/-- The exact geometric requirements satisfied by the primitive of a
    nonnegative η(v)/v supported in [5/4,8/5], normalized to integral 1.
    The existence of such a smooth primitive is a separate analytic lemma. -/
structure VF919LogAntiderivativeData where
  F : ℝ → ℝ
  mono : Monotone F
  smooth : ContDiff ℝ ∞ F
  low : ∀ u : ℝ, u ≤ (5 : ℝ) / 4 → F u = 0
  high : ∀ u : ℝ, (8 : ℝ) / 5 ≤ u → F u = 1

/-- Single fixed nonnegative logarithmic slot profile. -/
def vf919LogWindow (d : VF919LogAntiderivativeData) (u : ℝ) : ℝ :=
  d.F u - d.F (((4 : ℝ) / 5) * u)

/-- Single smooth exterior taper, equal to one up to the sharp boundary. -/
def vf919LogTerminal (d : VF919LogAntiderivativeData) (u : ℝ) : ℝ :=
  1 - d.F (((5 : ℝ) / 4) * u)

theorem vf919LogWindow_smooth (d : VF919LogAntiderivativeData) :
    ContDiff ℝ ∞ (vf919LogWindow d) := by
  have hscale : ContDiff ℝ ∞ (fun u : ℝ => ((4 : ℝ) / 5) * u) :=
    contDiff_const.mul contDiff_id
  exact d.smooth.sub (d.smooth.comp hscale)

theorem vf919LogTerminal_smooth (d : VF919LogAntiderivativeData) :
    ContDiff ℝ ∞ (vf919LogTerminal d) := by
  have hscale : ContDiff ℝ ∞ (fun u : ℝ => ((5 : ℝ) / 4) * u) :=
    contDiff_const.mul contDiff_id
  exact contDiff_const.sub (d.smooth.comp hscale)

private theorem vf919LogF_nonneg (d : VF919LogAntiderivativeData)
    (u : ℝ) : 0 ≤ d.F u := by
  by_cases hu : u ≤ (5 : ℝ) / 4
  · rw [d.low u hu]
  · have hlo := d.low ((5 : ℝ) / 4) le_rfl
    have hmono := d.mono (le_of_not_ge hu)
    rw [hlo] at hmono
    exact hmono

private theorem vf919LogF_le_one (d : VF919LogAntiderivativeData)
    (u : ℝ) : d.F u ≤ 1 := by
  by_cases hu : (8 : ℝ) / 5 ≤ u
  · rw [d.high u hu]
  · have hhi := d.high ((8 : ℝ) / 5) le_rfl
    have hmono := d.mono (le_of_not_ge hu)
    rw [hhi] at hmono
    exact hmono

/-- No δ-dependent real derivatives: the fixed logarithmic slot lies
    between zero and one for every real argument. -/
theorem vf919LogWindow_bounds (d : VF919LogAntiderivativeData)
    (u : ℝ) : 0 ≤ vf919LogWindow d u ∧ vf919LogWindow d u ≤ 1 := by
  by_cases hu : 0 ≤ u
  · have hscale : ((4 : ℝ) / 5) * u ≤ u := by nlinarith
    have hmono := d.mono hscale
    have hupper := vf919LogF_le_one d u
    have hlower := vf919LogF_nonneg d (((4 : ℝ) / 5) * u)
    unfold vf919LogWindow
    constructor <;> linarith
  · have hu0 : u ≤ (5 : ℝ) / 4 := by linarith
    have hu1 : ((4 : ℝ) / 5) * u ≤ (5 : ℝ) / 4 := by nlinarith
    simp [vf919LogWindow, d.low u hu0, d.low _ hu1]

theorem vf919LogWindow_zero_below
    (d : VF919LogAntiderivativeData) (u : ℝ)
    (hu : u ≤ (5 : ℝ) / 4) : vf919LogWindow d u = 0 := by
  have hscaled : ((4 : ℝ) / 5) * u ≤ (5 : ℝ) / 4 := by
    by_cases hneg : u ≤ 0 <;> nlinarith
  simp [vf919LogWindow, d.low u hu, d.low _ hscaled]

theorem vf919LogWindow_zero_above
    (d : VF919LogAntiderivativeData) (u : ℝ)
    (hu : (2 : ℝ) ≤ u) : vf919LogWindow d u = 0 := by
  have hscaled : (8 : ℝ) / 5 ≤ ((4 : ℝ) / 5) * u := by nlinarith
  have huhi : (8 : ℝ) / 5 ≤ u := by linarith
  simp [vf919LogWindow, d.high u huhi, d.high _ hscaled]

/-- Precisely the strict support accepted by OpenAI's smooth SourceData
    window fields; actual SourceData also requires ideal-source data. -/
theorem vf919LogWindow_support
    (d : VF919LogAntiderivativeData) :
    Function.support (vf919LogWindow d) ⊆ Set.Ioo (1 : ℝ) 2 := by
  intro u hu
  have hlo : (5 : ℝ) / 4 < u := by
    by_contra h
    exact hu (vf919LogWindow_zero_below d u (le_of_not_gt h))
  have hhi : u < 2 := by
    by_contra h
    exact hu (vf919LogWindow_zero_above d u (le_of_not_gt h))
  exact ⟨by linarith, hhi⟩

/-- Abel terminal profile is antitone, and so all discrete weights
    H(n/X)-H((n+1)/X) are nonnegative. -/
theorem vf919LogTerminal_antitone
    (d : VF919LogAntiderivativeData) :
    Antitone (vf919LogTerminal d) := by
  intro u v huv
  have hscale : ((5 : ℝ) / 4) * u ≤ ((5 : ℝ) / 4) * v := by nlinarith
  have hmono := d.mono hscale
  unfold vf919LogTerminal
  linarith

theorem vf919LogTerminal_le_one
    (d : VF919LogAntiderivativeData) (u : ℝ) :
    vf919LogTerminal d u ≤ 1 := by
  unfold vf919LogTerminal
  linarith [vf919LogF_nonneg d (((5 : ℝ) / 4) * u)]

theorem vf919LogTerminal_nonneg
    (d : VF919LogAntiderivativeData) (u : ℝ) :
    0 ≤ vf919LogTerminal d u := by
  unfold vf919LogTerminal
  linarith [vf919LogF_le_one d (((5 : ℝ) / 4) * u)]

/-- Each adjacent logarithmic slot is literally the first difference
    in the primitive at consecutive powers of 5/4. -/
private theorem vf919LogWindow_succ
    (d : VF919LogAntiderivativeData) (u : ℝ) (j : ℕ) :
    vf919LogWindow d ((((5 : ℝ) / 4) ^ (j + 1)) * u) =
      d.F ((((5 : ℝ) / 4) ^ (j + 1)) * u) -
        d.F ((((5 : ℝ) / 4) ^ j) * u) := by
  unfold vf919LogWindow
  congr 1
  rw [pow_succ]
  ring

/-- Nat finite telescoping over the original 2..J slot index. -/
private theorem vf919LogSequence_telescope
    (g : ℕ → ℝ) (J : ℕ) (hJ : 2 ≤ J) :
    (∑ j ∈ Finset.Icc 2 J, (g j - g (j - 1))) = g J - g 1 := by
  induction J, hJ using Nat.le_induction with
  | base => simp
  | succ J hJ ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ J + 1), ih]
      have hj : J + 1 - 1 = J := by omega
      rw [hj]
      ring

/-- Exact multiplicative partition. No normalization denominators
    or narrow-window estimates appear in the identity. -/
theorem vf919LogWindow_finite_partition
    (d : VF919LogAntiderivativeData) (u : ℝ)
    (J : ℕ) (hJ : 2 ≤ J) :
    (∑ j ∈ Finset.Icc 2 J,
      vf919LogWindow d ((((5 : ℝ) / 4) ^ j) * u)) =
      d.F ((((5 : ℝ) / 4) ^ J) * u) -
        d.F (((5 : ℝ) / 4) * u) := by
  calc
    (∑ j ∈ Finset.Icc 2 J,
        vf919LogWindow d ((((5 : ℝ) / 4) ^ j) * u)) =
      ∑ j ∈ Finset.Icc 2 J,
        (d.F ((((5 : ℝ) / 4) ^ j) * u) -
          d.F ((((5 : ℝ) / 4) ^ (j - 1)) * u)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjlow : 2 ≤ j := (Finset.mem_Icc.mp hj).1
        cases j with
        | zero => omega
        | succ k =>
            simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right] using
              vf919LogWindow_succ d u k
    _ = _ := by
      simpa only [pow_one] using
        (vf919LogSequence_telescope
          (fun j => d.F ((((5 : ℝ) / 4) ^ j) * u)) J hJ)

theorem vf919LogWindow_partition_eq_terminal
    (d : VF919LogAntiderivativeData) (u : ℝ)
    (J : ℕ) (hJ : 2 ≤ J)
    (hTop : (8 : ℝ) / 5 ≤ (((5 : ℝ) / 4) ^ J) * u) :
    (∑ j ∈ Finset.Icc 2 J,
      vf919LogWindow d ((((5 : ℝ) / 4) ^ j) * u)) =
        vf919LogTerminal d u := by
  rw [vf919LogWindow_finite_partition d u J hJ,
      d.high _ hTop]
  simp [vf919LogTerminal]

/-- One finite J works uniformly for EVERY integer n >= 1,
    provided (5/4)^J >= (8/5)X. -/
theorem vf919LogWindow_partition_at_integer
    (d : VF919LogAntiderivativeData)
    (X n J : ℕ) (hX : 0 < X) (hn : 1 ≤ n) (hJ : 2 ≤ J)
    (hScale : ((8 : ℝ) / 5) * (X : ℝ) ≤ ((5 : ℝ) / 4) ^ J) :
    (∑ j ∈ Finset.Icc 2 J,
      vf919LogWindow d
        ((((5 : ℝ) / 4) ^ j) * ((n : ℝ) / (X : ℝ)))) =
      vf919LogTerminal d ((n : ℝ) / (X : ℝ)) := by
  apply vf919LogWindow_partition_eq_terminal d _ J hJ
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hPow : (0 : ℝ) ≤ ((5 : ℝ) / 4) ^ J := by positivity
  have hMul : ((8 : ℝ) / 5) * (X : ℝ) ≤
      ((5 : ℝ) / 4) ^ J * (n : ℝ) := by
    nlinarith
  have hDiv : ((8 : ℝ) / 5) ≤
      (((5 : ℝ) / 4) ^ J * (n : ℝ)) / (X : ℝ) :=
    (le_div_iff₀ hXr).mpr hMul
  simpa only [mul_div_assoc] using hDiv

/-- Exact interior plateau at physical integer n <= X. -/
theorem vf919LogTerminal_inside
    (d : VF919LogAntiderivativeData)
    (X n : ℕ) (hX : 0 < X) (hn : n ≤ X) :
    vf919LogTerminal d ((n : ℝ) / (X : ℝ)) = 1 := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hnr : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hn
  have hDiv : (n : ℝ) / (X : ℝ) ≤ 1 :=
    (div_le_iff₀ hXr).mpr (by nlinarith)
  have hArg : ((5 : ℝ) / 4) * ((n : ℝ) / (X : ℝ)) ≤
      (5 : ℝ) / 4 := by nlinarith
  unfold vf919LogTerminal
  rw [d.low _ hArg]
  ring

/-- Exact exterior vanishing at any integer bound B >= (32/25)X. -/
theorem vf919LogTerminal_at_upper
    (d : VF919LogAntiderivativeData)
    (X B : ℕ) (hX : 0 < X)
    (hB : ((32 : ℝ) / 25) * (X : ℝ) ≤ (B : ℝ)) :
    vf919LogTerminal d ((B : ℝ) / (X : ℝ)) = 0 := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hDiv : ((32 : ℝ) / 25) ≤ (B : ℝ) / (X : ℝ) :=
    (le_div_iff₀ hXr).mpr hB
  have hArg : ((8 : ℝ) / 5) ≤
      ((5 : ℝ) / 4) * ((B : ℝ) / (X : ℝ)) := by nlinarith
  unfold vf919LogTerminal
  rw [d.high _ hArg]
  ring

/-- The physical discrete Abel weights from a monotone primitive
    are nonnegative and have total mass at most one. -/
theorem vf919LogTerminal_discreteAbel_nonneg
    (d : VF919LogAntiderivativeData)
    (X n : ℕ) (hX : 0 < X) :
    0 ≤ vf919ExteriorAbelWeight
       (fun k : ℕ => vf919LogTerminal d ((k : ℝ) / (X : ℝ))) n := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  have hDiv : (n : ℝ) / (X : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) / (X : ℝ) :=
    div_le_div_of_nonneg_right hn hXr.le
  have hAnti := vf919LogTerminal_antitone d hDiv
  unfold vf919ExteriorAbelWeight
  exact sub_nonneg.mpr hAnti

/-- The existing #989 sharp-prefix theorem specialized to the
    ACTUAL physical mu_Z and an explicit finite logarithmic partition.
    No analytic saving is presumed here. -/
theorem vf919LogOriginalMertens_sharp_eq_smooth_sub_Abel
    (d : VF919LogAntiderivativeData)
    (X B J : ℕ) (hX : 0 < X) (hXB : X + 1 ≤ B)
    (hJ : 2 ≤ J)
    (hScale : ((8 : ℝ) / 5) * (X : ℝ) ≤ ((5 : ℝ) / 4) ^ J)
    (hB : ((32 : ℝ) / 25) * (X : ℝ) ≤ (B : ℝ)) :
    (∑ n ∈ Finset.Icc 1 X, realMoebiusStep n) =
      (∑ n ∈ Finset.Ico 1 B,
        realMoebiusStep n *
          (∑ j ∈ Finset.Icc 2 J,
            vf919LogWindow d
              ((((5 : ℝ) / 4) ^ j) * ((n : ℝ) / (X : ℝ))))) -
      (∑ n ∈ Finset.Ioo X B,
        vf919ExteriorSignedPrefix X n realMoebiusStep *
          vf919ExteriorAbelWeight
            (fun k : ℕ => vf919LogTerminal d ((k : ℝ) / (X : ℝ))) n) := by
  apply vf919SharpPrefix_eq_smooth_sub_discreteSpill X B hXB realMoebiusStep
    (fun n => ∑ j ∈ Finset.Icc 2 J,
      vf919LogWindow d
        ((((5 : ℝ) / 4) ^ j) * ((n : ℝ) / (X : ℝ))))
    (fun n => vf919LogTerminal d ((n : ℝ) / (X : ℝ)))
  · exact vf919LogTerminal_at_upper d X B hX hB
  · intro n hn
    have hmem := Finset.mem_Icc.mp hn
    rw [vf919LogWindow_partition_at_integer d X n J hX hmem.1 hJ hScale]
    exact vf919LogTerminal_inside d X n hX hmem.2
  · intro n hn
    have hmem := Finset.mem_Ioo.mp hn
    exact vf919LogWindow_partition_at_integer d X n J hX (by omega) hJ hScale

/-- Period-three character prefixes have EXACTLY two possible values:
    0 or 1. Their difference always has magnitude at most one. -/
theorem vf919PeriodThreePrefix_difference_abs_le_one (A B : ℕ) :
    |vf919IntegerCharacterPrefix A - vf919IntegerCharacterPrefix B| ≤
      (1 : ℤ) := by
  rw [vf919IntegerCharacterPrefix_eq_residue,
      vf919IntegerCharacterPrefix_eq_residue]
  split_ifs <;> norm_num

/-- Exact low-ideal-norm cofactor interval saving at EACH norm, prior
    to any sum over ideal labels. No statistical independence invoked. -/
theorem vf919PeriodThreeCofactor_interval_abs_le_one
    (X n m : ℕ) :
    |vf919IntegerCharacterPrefix (n / m) -
      vf919IntegerCharacterPrefix (X / m)| ≤ (1 : ℤ) :=
  vf919PeriodThreePrefix_difference_abs_le_one (n / m) (X / m)

#print axioms vf919LogWindow_finite_partition
#print axioms vf919LogWindow_partition_at_integer
#print axioms vf919LogOriginalMertens_sharp_eq_smooth_sub_Abel
#print axioms vf919PeriodThreePrefix_difference_abs_le_one
#print axioms vf919PeriodThreeCofactor_interval_abs_le_one

end RHLean.Analysis
