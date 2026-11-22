import Mathlib
import RHLean.Analysis.AlpogeSharpASKCollar

/-!
# Alpoge ASK at the exact native square clock: a root-width prime-power collar

At X_R = R^2 - 1, take the physical ASK width parameters
  a_R = R * X_R,  b_R = R,  B_R = R + 1.
The two sharp cutoffs a_R/B_R and a_R/b_R are EXACTLY
  R*(R-1)  and  R^2 - 1.
Thus only R-2 integer sites lie in the principal character crossing
collar. The already proved midpoint Jensen bound therefore pays the
ENTIRE actual principal prime-power width movement by
  (R-2)*log(R^2-1)/4 = O(R log R).

This is a new source-faithful, unconditional finite estimate, NOT an
RH proof. A full lattice shortcut still needs the nonprincipal,
partner/width covariance and the actual geometric multiplicity/cost
witnesses. No external Alpoge theorem or RH hypothesis is used.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Square-root-scaled sharp ASK height, where X_R is the completed
square endpoint of RH_Lean's native arithmetic. -/
def alpogeSquareASKScale (R : ℕ) : ℝ :=
  (R : ℝ) * ((R : ℝ) ^ 2 - 1)

/-- The exact principal ASK midpoint width movement, using the
original von Mangoldt mass on every actual prime power. -/
def alpogeSquareASKPrincipalGap (R : ℕ) : ℝ :=
  alpogeASKPrimePowerMidpointGap (R ^ 2 - 1)
    (alpogeSquareASKScale R) (R : ℝ) ((R + 1 : ℕ) : ℝ)

/-- Exact square-clock cutoff at the narrow width. -/
theorem alpogeSquareASKScale_div_R (R : ℕ) (hR : 1 ≤ R) :
    alpogeSquareASKScale R / (R : ℝ) = (R : ℝ) ^ 2 - 1 := by
  have hr : (R : ℝ) ≠ 0 := by
    exact_mod_cast (show R ≠ 0 by omega)
  unfold alpogeSquareASKScale
  field_simp

/-- The second width makes the lower cutoff an *integer*:
R*(R^2-1)/(R+1) = R*(R-1). -/
theorem alpogeSquareASKScale_div_succ (R : ℕ) :
    alpogeSquareASKScale R / ((R : ℝ) + 1) =
      (R : ℝ) * ((R : ℝ) - 1) := by
  have hs : (R : ℝ) + 1 ≠ 0 := by positivity
  unfold alpogeSquareASKScale
  rw [show (R : ℝ) ^ 2 - 1 =
    ((R : ℝ) - 1) * ((R : ℝ) + 1) by ring]
  field_simp

theorem alpogeSquareASKScale_eq_natX (R : ℕ) (hR : 2 ≤ R) :
    alpogeSquareASKScale R =
      (R : ℝ) * ((R ^ 2 - 1 : ℕ) : ℝ) := by
  have hX : 1 ≤ R ^ 2 := by nlinarith
  unfold alpogeSquareASKScale
  rw [Nat.cast_sub hX]
  push_cast
  ring

theorem alpogeSquareASKScale_eq_natLower (R : ℕ) (hR : 2 ≤ R) :
    alpogeSquareASKScale R =
      (((R + 1 : ℕ) : ℝ)) * ((R * (R - 1) : ℕ) : ℝ) := by
  have hR1 : 1 ≤ R := by omega
  unfold alpogeSquareASKScale
  rw [Nat.cast_mul, Nat.cast_sub hR1]
  push_cast
  ring

/-- The exact interval contains R-2 physical integer sites. -/
theorem alpogeSquareASKCollar_card (R : ℕ) (hR : 2 ≤ R) :
    (Finset.Ico (R * (R - 1) + 1) (R ^ 2 - 1)).card = R - 2 := by
  have hr : R - 1 + 1 = R := by omega
  have hsq : R ^ 2 = R * (R - 1) + (R - 1) + 1 := by
    calc
      R ^ 2 = ((R - 1) + 1) ^ 2 := by rw [hr]
      _ = ((R - 1) + 1) * (R - 1) + (R - 1) + 1 := by ring
      _ = R * (R - 1) + (R - 1) + 1 := by rw [hr]
  have hX : R ^ 2 - 1 = R * (R - 1) + (R - 1) := by omega
  rw [Nat.card_Ico, hX]
  omega

/-- For every actual n≥1, the original sharp ASK crossing condition is
exactly the short upper part of the native square. -/
theorem alpogeSquareASKCollar_iff (R n : ℕ)
    (hR : 2 ≤ R) (hn : 1 ≤ n) :
    ((R : ℝ) < alpogeSquareASKScale R / (n : ℝ) ∧
      alpogeSquareASKScale R / (n : ℝ) < ((R + 1 : ℕ) : ℝ)) ↔
      R * (R - 1) < n ∧ n < R ^ 2 - 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hrpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
  have hspos : (0 : ℝ) < ((R + 1 : ℕ) : ℝ) := by positivity
  have haUpper := alpogeSquareASKScale_eq_natX R hR
  have haLower := alpogeSquareASKScale_eq_natLower R hR
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (R : ℝ) * (n : ℝ) < (R : ℝ) * ((R ^ 2 - 1 : ℕ) : ℝ) := by
      rw [← haUpper]
      exact (lt_div_iff₀ hnpos).mp h1
    have h2' : ((R + 1 : ℕ) : ℝ) * ((R * (R - 1) : ℕ) : ℝ) <
        ((R + 1 : ℕ) : ℝ) * (n : ℝ) := by
      rw [← haLower]
      exact (div_lt_iff₀ hnpos).mp h2
    have hlt : (n : ℝ) < ((R ^ 2 - 1 : ℕ) : ℝ) := by
      by_contra h
      have hle : ((R ^ 2 - 1 : ℕ) : ℝ) ≤ (n : ℝ) :=
        le_of_not_gt h
      have hm := mul_le_mul_of_nonneg_left hle hrpos.le
      linarith
    have hgt : ((R * (R - 1) : ℕ) : ℝ) < (n : ℝ) := by
      by_contra h
      have hle : (n : ℝ) ≤ ((R * (R - 1) : ℕ) : ℝ) :=
        le_of_not_gt h
      have hm := mul_le_mul_of_nonneg_left hle hspos.le
      linarith
    exact ⟨by exact_mod_cast hgt, by exact_mod_cast hlt⟩
  · rintro ⟨hgt, hlt⟩
    have hgt' : ((R * (R - 1) : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hgt
    have hlt' : (n : ℝ) < ((R ^ 2 - 1 : ℕ) : ℝ) := by exact_mod_cast hlt
    constructor
    · apply (lt_div_iff₀ hnpos).mpr
      rw [haUpper]
      have hdiff : 0 < (R : ℝ) * (((R ^ 2 - 1 : ℕ) : ℝ) - (n : ℝ)) :=
        mul_pos hrpos (sub_pos.mpr hlt')
      nlinarith only [hdiff]
    · apply (div_lt_iff₀ hnpos).mpr
      rw [haLower]
      have hdiff : 0 < (((R + 1 : ℕ) : ℝ)) * ((n : ℝ) - ((R * (R - 1) : ℕ) : ℝ)) :=
        mul_pos hspos (sub_pos.mpr hgt')
      nlinarith only [hdiff]

theorem alpogeSquareASKCollar_filter_eq (R : ℕ) (hR : 2 ≤ R) :
    (Finset.Icc 2 (R ^ 2 - 1)).filter
      (fun n : ℕ => (R : ℝ) < alpogeSquareASKScale R / (n : ℝ) ∧
        alpogeSquareASKScale R / (n : ℝ) < ((R + 1 : ℕ) : ℝ)) =
    Finset.Ico (R * (R - 1) + 1) (R ^ 2 - 1) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hn2, _⟩, h⟩
    have hx := (alpogeSquareASKCollar_iff R n hR (by omega)).mp h
    omega
  · intro hn
    have hR1 : 1 ≤ R - 1 := by omega
    have hmul : R ≤ R * (R - 1) := by
      simpa only [mul_one] using Nat.mul_le_mul_left R hR1
    have hn2 : 2 ≤ n := by omega
    have h : R * (R - 1) < n ∧ n < R ^ 2 - 1 := by omega
    exact ⟨⟨hn2, by omega⟩,
      (alpogeSquareASKCollar_iff R n hR (by omega)).mpr h⟩

/-- Entire genuine prime-power collar mass is at most (R-2) log(X_R).
No PNT, cancellation assumption, or geometric hypothesis. -/
theorem alpogeSquareASKCollarMass_le (R : ℕ) (hR : 2 ≤ R) :
    alpogeASKPrimePowerCollarMass (R ^ 2 - 1)
      (alpogeSquareASKScale R) (R : ℝ) ((R + 1 : ℕ) : ℝ) ≤
    ((R - 2 : ℕ) : ℝ) * Real.log ((R ^ 2 - 1 : ℕ) : ℝ) := by
  unfold alpogeASKPrimePowerCollarMass
  rw [alpogeSquareASKCollar_filter_eq R hR]
  calc
    (∑ n ∈ Finset.Ico (R * (R - 1) + 1) (R ^ 2 - 1), Λ n) ≤
      ∑ _n ∈ Finset.Ico (R * (R - 1) + 1) (R ^ 2 - 1),
        Real.log ((R ^ 2 - 1 : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hI := Finset.mem_Ico.mp hn
          have hn1 : 1 ≤ n := by omega
          have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
          have hnle : (n : ℝ) ≤ ((R ^ 2 - 1 : ℕ) : ℝ) := by exact_mod_cast hI.2.le
          exact ArithmeticFunction.vonMangoldt_le_log.trans
            (Real.log_le_log hnpos hnle)
    _ = ((R - 2 : ℕ) : ℝ) * Real.log ((R ^ 2 - 1 : ℕ) : ℝ) := by
      rw [Finset.sum_const, alpogeSquareASKCollar_card R hR]
      simp only [nsmul_eq_mul]

/-- A genuinely unconditional root-scale physical ASK movement cost.
Only the original Λ(n) prime powers are used, and all selected
sites lie in the exact R-2-site integer collar. -/
theorem alpogeSquareASKPrincipalGap_le_rootLog (R : ℕ) (hR : 2 ≤ R) :
    0 ≤ alpogeSquareASKPrincipalGap R ∧
      alpogeSquareASKPrincipalGap R ≤
        ((R - 2 : ℕ) : ℝ) * Real.log ((R ^ 2 - 1 : ℕ) : ℝ) / 4 := by
  have hb : (R : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have h := alpogeASKPrimePowerMidpointGap_le_collar
    (R ^ 2 - 1) (alpogeSquareASKScale R)
    (R : ℝ) ((R + 1 : ℕ) : ℝ) hb
  have hmass := alpogeSquareASKCollarMass_le R hR
  constructor
  · exact h.1
  · unfold alpogeSquareASKPrincipalGap
    calc
      alpogeASKPrimePowerMidpointGap (R ^ 2 - 1)
          (alpogeSquareASKScale R) (R : ℝ) ((R + 1 : ℕ) : ℝ) ≤
        ((((R + 1 : ℕ) : ℝ) - (R : ℝ)) / 4) *
          alpogeASKPrimePowerCollarMass (R ^ 2 - 1)
            (alpogeSquareASKScale R) (R : ℝ) ((R + 1 : ℕ) : ℝ) := h.2
      _ = (1 / 4 : ℝ) * alpogeASKPrimePowerCollarMass (R ^ 2 - 1)
          (alpogeSquareASKScale R) (R : ℝ) ((R + 1 : ℕ) : ℝ) := by
            push_cast
            ring
      _ ≤ (1 / 4 : ℝ) *
          (((R - 2 : ℕ) : ℝ) * Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) := by
            linarith
      _ = ((R - 2 : ℕ) : ℝ) *
          Real.log ((R ^ 2 - 1 : ℕ) : ℝ) / 4 := by ring

end RHLean.Analysis
