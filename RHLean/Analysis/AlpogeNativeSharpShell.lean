import Mathlib
import RHLean.Analysis.AlpogeNativeSharpASKBalance

/-!
# Genuine prime-power cutoff shell in Alpoge's sharp ASK

An unconditional finite estimate for the entire von Mangoldt prime-power
population. It localizes the positive convexity remainder after subtracting
the common affine tangent at width b to an ACTUAL arithmetic shell. This
does not supply the deep topExcess estimate or the theta-lift cost theorem.
-/

noncomputable section
open Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Sharp ASK residual after restoring the signed tangent at b. -/
def alpogeNativeASKCollar (z b w : ℝ) : ℝ :=
  max (z - w) 0 - max (z - b) 0 +
    (if b < z then w - b else 0)

theorem alpogeNativeASKCollar_eq_above (z b w : ℝ) (hb : b < z) :
    alpogeNativeASKCollar z b w = max (w - z) 0 := by
  unfold alpogeNativeASKCollar
  rw [ite_eq_left hb, max_eq_left (by linarith : 0 ≤ z - b)]
  by_cases hzw : z ≤ w
  · rw [max_eq_right (by linarith : z - w ≤ 0),
        max_eq_left (by linarith : 0 ≤ w - z)]
    ring
  · rw [max_eq_left (by linarith : 0 ≤ z - w),
        max_eq_right (by linarith : w - z ≤ 0)]
    ring

theorem alpogeNativeASKCollar_eq_below
    (z b w : ℝ) (hzb : z ≤ b) (hbw : b ≤ w) :
    alpogeNativeASKCollar z b w = 0 := by
  unfold alpogeNativeASKCollar
  rw [ite_eq_right (not_lt_of_ge hzb),
      max_eq_right (by linarith : z - w ≤ 0),
      max_eq_right (by linarith : z - b ≤ 0)]
  ring

/-- Source-exact positive collar, supported on b < z <= b+h. -/
theorem alpogeNativeASKCollar_nonneg_le_shell
    (z b w h : ℝ) (hbw : b ≤ w) (hwh : w ≤ b + h) (hh : 0 ≤ h) :
    0 ≤ alpogeNativeASKCollar z b w ∧
      alpogeNativeASKCollar z b w ≤
        (if b < z ∧ z ≤ b + h then h else 0) := by
  by_cases hbz : b < z
  · rw [alpogeNativeASKCollar_eq_above z b w hbz]
    constructor
    · exact le_max_right _ _
    · by_cases hz : z ≤ b + h
      · rw [ite_eq_left (And.intro hbz hz)]
        exact max_le (by linarith) hh
      · have hnot : ¬ (b < z ∧ z ≤ b + h) := by
          intro h
          exact hz h.2
        rw [ite_eq_right hnot]
        have hclosed : w - z ≤ 0 := by linarith
        rw [max_eq_right hclosed]
  · have hzb : z ≤ b := le_of_not_gt hbz
    rw [alpogeNativeASKCollar_eq_below z b w hzb hbw]
    have hnot : ¬ (b < z ∧ z ≤ b + h) := by
      intro h
      exact hbz h.1
    simp [hnot]

/-- The genuine weighted prime-power remainder at a single site. -/
def alpogeNativeASKPrimeCollarMass (N : ℕ) (a b w : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    Λ n * alpogeNativeASKCollar (a / (n : ℝ)) b w

/-- All real von Mangoldt mass in the actual cutoff-crossing shell. -/
def alpogeNativeASKPrimeShellMass (N : ℕ) (a b h : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter
      (fun n : ℕ => b < a / (n : ℝ) ∧ a / (n : ℝ) ≤ b + h), Λ n

/-- No lost prime powers or positive full-prefix charge. -/
theorem alpogeNativeASKPrimeCollar_le_shell
    (N : ℕ) (a b w h : ℝ)
    (hbw : b ≤ w) (hwh : w ≤ b + h) (hh : 0 ≤ h) :
    0 ≤ alpogeNativeASKPrimeCollarMass N a b w ∧
      alpogeNativeASKPrimeCollarMass N a b w ≤
        h * alpogeNativeASKPrimeShellMass N a b h := by
  constructor
  · unfold alpogeNativeASKPrimeCollarMass
    apply Finset.sum_nonneg
    intro n _hn
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (alpogeNativeASKCollar_nonneg_le_shell
        (a / (n : ℝ)) b w h hbw hwh hh).1
  · unfold alpogeNativeASKPrimeCollarMass
    calc
      (∑ n ∈ Finset.Icc 1 N,
          Λ n * alpogeNativeASKCollar (a / (n : ℝ)) b w) ≤
        ∑ n ∈ Finset.Icc 1 N,
          Λ n * (if b < a / (n : ℝ) ∧ a / (n : ℝ) ≤ b + h then h else 0) := by
            apply Finset.sum_le_sum
            intro n _hn
            exact mul_le_mul_of_nonneg_left
              (alpogeNativeASKCollar_nonneg_le_shell
                (a / (n : ℝ)) b w h hbw hwh hh).2
              ArithmeticFunction.vonMangoldt_nonneg
      _ = h * alpogeNativeASKPrimeShellMass N a b h := by
        unfold alpogeNativeASKPrimeShellMass
        rw [Finset.mul_sum, Finset.sum_filter]
        simp [mul_comm]

/-- Physical shell weight is at most shell population times log N. -/
theorem alpogeNativeASKPrimeShellMass_le_card_log
    (N : ℕ) (a b h : ℝ) :
    alpogeNativeASKPrimeShellMass N a b h ≤
      (((Finset.Icc 1 N).filter
        (fun n : ℕ => b < a / (n : ℝ) ∧ a / (n : ℝ) ≤ b + h)).card : ℝ) *
      Real.log (N : ℝ) := by
  unfold alpogeNativeASKPrimeShellMass
  calc
    (∑ n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => b < a / (n : ℝ) ∧ a / (n : ℝ) ≤ b + h), Λ n) ≤
      ∑ _n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => b < a / (n : ℝ) ∧ a / (n : ℝ) ≤ b + h),
        Real.log (N : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnIcc : n ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hn).1
          have hnhi : n ≤ N := (Finset.mem_Icc.mp hnIcc).2
          have hnpos : (0 : ℝ) < n := by
            exact_mod_cast (show 0 < n by
              have hlo := (Finset.mem_Icc.mp hnIcc).1
              omega)
          have hR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnhi
          exact ArithmeticFunction.vonMangoldt_le_log.trans
            (Real.log_le_log hnpos hR)
    _ = _ := by simp

/-- The complete shell-count bound; no analytic hypotheses are hidden. -/
theorem alpogeNativeASKPrimeCollar_le_card_log
    (N : ℕ) (a b w h : ℝ)
    (hbw : b ≤ w) (hwh : w ≤ b + h) (hh : 0 ≤ h) :
    alpogeNativeASKPrimeCollarMass N a b w ≤
      h * (((Finset.Icc 1 N).filter
        (fun n : ℕ => b < a / (n : ℝ) ∧ a / (n : ℝ) ≤ b + h)).card : ℝ) *
      Real.log (N : ℝ) := by
  calc
    _ ≤ h * alpogeNativeASKPrimeShellMass N a b h :=
      (alpogeNativeASKPrimeCollar_le_shell N a b w h hbw hwh hh).2
    _ ≤ h * (((Finset.Icc 1 N).filter
          (fun n : ℕ => b < a / (n : ℝ) ∧ a / (n : ℝ) ≤ b + h)).card : ℝ) *
        Real.log (N : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left
          (alpogeNativeASKPrimeShellMass_le_card_log N a b h) hh
        nlinarith only [hm]

end RHLean.Analysis
