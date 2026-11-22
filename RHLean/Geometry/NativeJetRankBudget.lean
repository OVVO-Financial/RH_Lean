import Mathlib

/-!
# The constructed jet order and the actual rank-defect budget

This is the numerical supplier used by the original rank-saturation proof,
ported from `CocoSgt/riemann-hypothesis-lean` at
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`:

* `Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChooseAddLePowMulChooseAdd.lean`;
* the `exists_jet_order` proof in
  `Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankGrowthBoundSmallScale.lean`.

The order is actually constructed as `floor ((T + d + 4) / (1 - rho))`.
The result retains the binomial dimensions and the original quantitative
loss `7 * (d^2 / T + d * rho)`. A final theorem applies it to the same
component degree and share data, deriving the near-rank comparison instead
of taking that comparison as a premise.

The algebraic-geometric jet injection, degree comparison, and lower share
on the actual theta/cover instance remain explicit inputs to that final
application. This file does not claim to construct the theta/cover datum
or to prove the complete character-source estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Matrix
open Polynomial

namespace RHLean.Geometry.NativeJetRank

private theorem choose_succ_mul_succ_eq_mul_choose (c n : ℕ) :
    (((c + (n + 1)).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1)
      = ((c : ℝ) + n + 1) * (((c + n).choose n : ℕ) : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (c + n) n
  have h' : (c + (n + 1)).choose (n + 1) * (n + 1) = (c + n + 1) * (c + n).choose n := by
    rw [show c + (n + 1) = c + n + 1 by ring]
    linarith
  exact_mod_cast h'

theorem choose_add_le_pow_mul_choose_add (a b : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (h : (a : ℝ) ≤ b + y * (b + 1)) (n : ℕ) :
    (((a + n).choose n : ℕ) : ℝ) ≤ (1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hA := choose_succ_mul_succ_eq_mul_choose a n
    have hB := choose_succ_mul_succ_eq_mul_choose b n
    have hCa : (0 : ℝ) ≤ (((a + n).choose n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hlin : (a : ℝ) + n + 1 ≤ (1 + y) * ((b : ℝ) + n + 1) := by
      nlinarith [mul_nonneg hy hn]
    have hfac : (0 : ℝ) ≤ (1 + y) * ((b : ℝ) + n + 1) :=
      mul_nonneg (by linarith) (by positivity)
    rw [← mul_le_mul_iff_of_pos_right hpos]
    rw [hA, mul_assoc, hB]
    calc ((a : ℝ) + n + 1) * (((a + n).choose n : ℕ) : ℝ)
        ≤ ((1 + y) * ((b : ℝ) + n + 1)) * ((1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ)) :=
          mul_le_mul hlin ih hCa hfac
      _ = (1 + y) ^ (n + 1) * (((b : ℝ) + n + 1) * (((b + n).choose n : ℕ) : ℝ)) := by ring

theorem exp_le_one_add_of_le_tenth (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 10) :
    Real.exp x ≤ 1 + 53 / 50 * x := by
  have hx : |x| ≤ 1 := by rw [abs_of_nonneg h0]; linarith
  have hb := Real.exp_bound hx (n := 3) (by norm_num)
  have h2 := (abs_le.mp hb).2
  rw [abs_of_nonneg h0] at h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have hx2 : x ^ 2 ≤ x / 10 := by nlinarith
  have hx3 : x ^ 3 ≤ x / 100 := by nlinarith
  nlinarith

theorem choose_rank_ratio_le :
    ∀ (D T a : ℕ) (ρ : ℝ), 2 ≤ D → 20 * D ≤ T → 0 ≤ ρ → ρ ≤ 1 / 4 → (a : ℝ) ≤ ((T : ℝ) + D + 4) / (1 - ρ) → (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) ≤ 1 / 10 → (((a + D).choose D : ℕ) : ℝ) ≤ (1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)) * (((T - 1).choose D : ℕ) : ℝ) := by
  intro D T a ρ hD hT hρ0 hρ1 ha hε
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hT' : (20 : ℝ) * D ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hbD : (T - 1 - D) + D = T - 1 := by omega
  have hbR : ((T - 1 - D : ℕ) : ℝ) = T - 1 - D := by
    have h3 : (T - 1 - D) + D + 1 = T := by omega
    have h := congrArg (fun k : ℕ => (k : ℝ)) h3
    push_cast at h
    linarith
  have hρ' : 0 < 1 - ρ := by linarith
  have hTD : 0 < (T : ℝ) - D := by linarith
  have hden : 0 < (1 - ρ) * ((T : ℝ) - D) := mul_pos hρ' hTD
  have hnum0 : (0 : ℝ) ≤ 2 * D + 5 + ρ * T := by nlinarith [mul_nonneg hρ0 hTpos.le]
  have hy0 : (0 : ℝ) ≤ (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := div_nonneg hnum0 hden.le
  have hyb : (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1)
      = (2 * D + 5 + ρ * T) / (1 - ρ) := by
    rw [hbR]
    field_simp
    ring
  have hab : (a : ℝ) ≤ ((T - 1 - D : ℕ) : ℝ)
      + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1) := by
    rw [hyb, hbR]
    have key : ((T : ℝ) + D + 4) / (1 - ρ) ≤ (T - 1 - D) + (2 * D + 5 + ρ * T) / (1 - ρ) := by
      rw [div_le_iff₀ hρ', add_mul, div_mul_cancel₀ _ hρ'.ne']
      nlinarith [mul_nonneg hρ0 (by linarith : (0 : ℝ) ≤ D + 1)]
    linarith
  have h1 := choose_add_le_pow_mul_choose_add a (T - 1 - D) _ hy0 hab D
  rw [hbD] at h1
  have hC : (0 : ℝ) ≤ (((T - 1).choose D : ℕ) : ℝ) := Nat.cast_nonneg _
  have hDy : (D : ℝ) * ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))
      = (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := by ring
  have hε0 : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := by
    rw [← hDy]; exact mul_nonneg (Nat.cast_nonneg _) hy0
  have hpow : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D
      ≤ Real.exp ((D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) := by
    rw [← hDy, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith)
      (by linarith [Real.add_one_le_exp ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))]) D
  have hexp := exp_le_one_add_of_le_tenth _ hε0 hε
  have hu : (57 / 80 : ℝ) * T ≤ (1 - ρ) * (T - D) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - ρ) hTD.le]
  have hnum : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) := mul_nonneg (Nat.cast_nonneg _) hnum0
  have h2 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))
      ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T) :=
    div_le_div_of_nonneg_left hnum (by positivity) hu
  have e1 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T)
      = (80 / 57) * ((D : ℝ) * (2 * D + 5) / T) + (80 / 57) * ((D : ℝ) * ρ) := by
    field_simp
  have e2 : (D : ℝ) * (2 * D + 5) / T ≤ (9 / 2) * ((D : ℝ) ^ 2 / T) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hTpos.le
  have e3 : 7 * (D : ℝ) ^ 2 / T = 7 * ((D : ℝ) ^ 2 / T) := by ring
  have hq : (0 : ℝ) ≤ (D : ℝ) ^ 2 / T := by positivity
  have hdr : (0 : ℝ) ≤ (D : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ0
  have hfin : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D
      ≤ 1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ) := by
    rw [e3]
    nlinarith
  calc (((a + D).choose D : ℕ) : ℝ)
      ≤ (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D * (((T - 1).choose D : ℕ) : ℝ) := h1
    _ ≤ (1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)) * (((T - 1).choose D : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hfin hC


/-- Construct the actual jet order with the original multiplicity and
binomial dimension budgets. -/
theorem exists_jet_order (d T : ℕ) (ρ : ℝ) (hd : 2 ≤ d) (hT : 1000 * (d : ℝ) ^ 2 ≤ T) (h0 : 0 ≤ ρ)
    (hz : 7 * ((d : ℝ) ^ 2 / T + d * ρ) ≤ 1 / 2) :
    ∃ a : ℕ, ((T + d + 4 : ℕ) : ℝ) < (a + 1) * (1 - ρ) ∧
      (((a + d).choose d : ℕ) : ℝ) ≤ (1 + 7 * ((d : ℝ) ^ 2 / T + d * ρ)) * (((T - 1).choose d : ℕ) : ℝ) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hTd : 2000 * (d : ℝ) ≤ T := by nlinarith
  have hT0 : (0 : ℝ) < T := by linarith
  have h1 : 0 ≤ (d : ℝ) ^ 2 / T := by positivity
  have h2 : (d : ℝ) * ρ ≤ 1 / 14 := by linarith
  have h3 : ρ ≤ 1 / 28 := by nlinarith
  have h4 : 0 < 1 - ρ := by linarith
  refine ⟨⌊((T : ℝ) + d + 4) / (1 - ρ)⌋₊, ?_, ?_⟩
  · have := Nat.lt_floor_add_one (((T : ℝ) + d + 4) / (1 - ρ))
    rw [div_lt_iff₀ h4] at this
    push_cast
    exact this
  · refine (choose_rank_ratio_le d T _ ρ hd (by exact_mod_cast (by linarith : 20 * (d : ℝ) ≤ T)) h0 (by linarith)
      (Nat.floor_le (by positivity)) ?_).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    · rw [div_le_iff₀ (mul_pos h4 (by linarith))]
      have a1 : (d : ℝ) * ρ * T ≤ 1 / 14 * T := mul_le_mul_of_nonneg_right h2 hT0.le
      have a2 : 27 / 28 * (1999 / 2000 * (T : ℝ)) ≤ (1 - ρ) * (T - d) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) h4.le
      nlinarith
    · have : 0 ≤ (d : ℝ) * ρ := by positivity
      rw [mul_div_assoc]
      linarith


/-- Apply the constructed jet order to the same component degrees and lower
shares. This is the final finite summation in `HodgeSteps.rk_le_alt_alt`.
The loss is the derived jet budget, rather than an assumed near-rank bound. -/
theorem rank_growth_of_component_jets
    {Z : Type} [Fintype Z]
    (d T : ℕ) (ρ δ : ℝ)
    (rPlus rMinus : Z → ℕ) (degree : Z → ℝ)
    (hd : 2 ≤ d) (hT : 1000 * (d : ℝ) ^ 2 ≤ T) (hρ : 0 ≤ ρ)
    (hsmall : 7 * ((d : ℝ) ^ 2 / T + d * ρ) ≤ 1 / 2)
    (hpaid : 7 * ((d : ℝ) ^ 2 / T + d * ρ) ≤ δ)
    (hdegree : ∀ z, 0 ≤ degree z)
    (hjet : ∀ a : ℕ,
      ((T + d + 4 : ℕ) : ℝ) < (a + 1) * (1 - ρ) →
      ∀ z, (rPlus z : ℝ) ≤ (((a + d).choose d : ℕ) : ℝ) * degree z)
    (hshare : ∀ z,
      (((T - 1).choose d : ℕ) : ℝ) * degree z ≤ (rMinus z : ℝ)) :
    ((∑ z, rPlus z : ℕ) : ℝ) ≤ (1 + δ) * ((∑ z, rMinus z : ℕ) : ℝ) := by
  classical
  obtain ⟨a, ha, hrank⟩ := exists_jet_order d T ρ hd hT hρ hsmall
  have hδ : 0 ≤ δ := le_trans (by positivity) hpaid
  rw [Nat.cast_sum, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  calc
    (rPlus z : ℝ) ≤ (((a + d).choose d : ℕ) : ℝ) * degree z := hjet a ha z
    _ ≤ ((1 + 7 * ((d : ℝ) ^ 2 / T + d * ρ)) *
        (((T - 1).choose d : ℕ) : ℝ)) * degree z :=
      mul_le_mul_of_nonneg_right hrank (hdegree z)
    _ ≤ ((1 + δ) * (((T - 1).choose d : ℕ) : ℝ)) * degree z :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (add_le_add_left hpaid 1) (Nat.cast_nonneg _))
        (hdegree z)
    _ = (1 + δ) * ((((T - 1).choose d : ℕ) : ℝ) * degree z) := by ring
    _ ≤ (1 + δ) * (rMinus z : ℝ) :=
      mul_le_mul_of_nonneg_left (hshare z) (by linarith)

end RHLean.Geometry.NativeJetRank
