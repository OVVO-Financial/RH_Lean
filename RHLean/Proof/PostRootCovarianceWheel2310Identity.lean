import RHLean.Proof.PostRootCovariancePrimeWheel210Scratch

/-!
# Exact 2310 wheel with both opposite-sign overlaps cancelled

This module contains only the exact signed algebra.  It deliberately leaves the
finite counting estimate to a separate layer, so the wheel identity itself can
be kernel-checked without the large floor-arithmetic proof.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- Adjoining `11` to the exact `210` wheel and cancelling both opposite-sign
overlaps gives the fully reduced sixteen-piece `2310` staircase. -/
theorem roughMertens_one_eq_2310Wheel_twoOverlapsCancelled (B : ℕ) :
    roughMertens 1 B =
      roughInterval 2310 (B / 2) B
      - roughInterval 2310 (B / 15) (B / 11)
      - roughInterval 2310 (B / 14) (B / 7)
      + roughInterval 2310 (B / 105) (B / 77)
      - roughInterval 2310 (B / 10) (B / 5)
      + roughInterval 2310 (B / 110) (B / 55)
      + roughInterval 2310 (B / 70) (B / 35)
      - roughInterval 2310 (B / 770) (B / 385)
      - roughInterval 2310 (B / 6) (B / 3)
      + roughInterval 2310 (B / 66) (B / 33)
      + roughInterval 2310 (B / 42) (B / 21)
      - roughInterval 2310 (B / 462) (B / 231)
      + roughInterval 2310 (B / 30) (B / 22)
      - roughInterval 2310 (B / 330) (B / 165)
      - roughInterval 2310 (B / 210) (B / 154)
      + roughInterval 2310 (B / 2310) (B / 1155) := by
  have hs6 : Squarefree 6 := by
    simpa using (Nat.squarefree_mul (by norm_num : Nat.Coprime 2 3)).2
      ⟨Nat.prime_two.squarefree, (show Nat.Prime 3 by norm_num).squarefree⟩
  have hs30 : Squarefree 30 := by
    simpa using (Nat.squarefree_mul (by norm_num : Nat.Coprime 5 6)).2
      ⟨(show Nat.Prime 5 by norm_num).squarefree, hs6⟩
  have hs210 : Squarefree 210 := by
    simpa using (Nat.squarefree_mul (by norm_num : Nat.Coprime 7 30)).2
      ⟨(show Nat.Prime 7 by norm_num).squarefree, hs30⟩
  have hs2310 : Squarefree 2310 := by
    simpa using (Nat.squarefree_mul (by norm_num : Nat.Coprime 11 210)).2
      ⟨(show Nat.Prime 11 by norm_num).squarefree, hs210⟩
  have hr0 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 2) B
  have hr1 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 14) (B / 7)
  have hr2 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 10) (B / 5)
  have hr3 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 70) (B / 35)
  have hr4 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 6) (B / 3)
  have hr5 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 42) (B / 21)
  have hr6 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 30) (B / 15)
  have hr7 := roughInterval_wheel_recursion
    (W := 2310) (p := 11) (by norm_num) (by norm_num) hs2310 (B / 210) (B / 105)
  norm_num at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  have h0 : roughInterval 210 (B / 2) B =
      roughInterval 2310 (B / 2) B -
        roughInterval 2310 (B / 22) (B / 11) := by
    simpa [Nat.div_div_eq_div_mul] using hr0
  have h1 : roughInterval 210 (B / 14) (B / 7) =
      roughInterval 2310 (B / 14) (B / 7) -
        roughInterval 2310 (B / 154) (B / 77) := by
    simpa [Nat.div_div_eq_div_mul] using hr1
  have h2 : roughInterval 210 (B / 10) (B / 5) =
      roughInterval 2310 (B / 10) (B / 5) -
        roughInterval 2310 (B / 110) (B / 55) := by
    simpa [Nat.div_div_eq_div_mul] using hr2
  have h3 : roughInterval 210 (B / 70) (B / 35) =
      roughInterval 2310 (B / 70) (B / 35) -
        roughInterval 2310 (B / 770) (B / 385) := by
    simpa [Nat.div_div_eq_div_mul] using hr3
  have h4 : roughInterval 210 (B / 6) (B / 3) =
      roughInterval 2310 (B / 6) (B / 3) -
        roughInterval 2310 (B / 66) (B / 33) := by
    simpa [Nat.div_div_eq_div_mul] using hr4
  have h5 : roughInterval 210 (B / 42) (B / 21) =
      roughInterval 2310 (B / 42) (B / 21) -
        roughInterval 2310 (B / 462) (B / 231) := by
    simpa [Nat.div_div_eq_div_mul] using hr5
  have h6 : roughInterval 210 (B / 30) (B / 15) =
      roughInterval 2310 (B / 30) (B / 15) -
        roughInterval 2310 (B / 330) (B / 165) := by
    simpa [Nat.div_div_eq_div_mul] using hr6
  have h7 : roughInterval 210 (B / 210) (B / 105) =
      roughInterval 2310 (B / 210) (B / 105) -
        roughInterval 2310 (B / 2310) (B / 1155) := by
    simpa [Nat.div_div_eq_div_mul] using hr7
  rw [roughMertens_one_eq_twoTenWheel_eightBands, h0, h1, h2, h3, h4, h5, h6, h7]
  unfold roughInterval
  ring

end RHLean.Proof
