import RHLean.Proof.PostRootCovarianceUnconditionalDecayScratch

/-!
# Explicit 210-wheel continuation

The generic finite-wheel transport is already proved in
`PostRootCovarianceUnconditionalDecayScratch`.  This file pushes the concrete
staircase one prime farther: adjoining `7` to the compiled `30`-wheel refines
each surviving band by the same multiplicative finite difference.  No estimate
or restart occurs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- **The wheel keeps iterating.**  Adjoining `7` to the explicit `30`-wheel
four-band representation gives the corresponding eight-band `210`-rough
staircase.  Every old band survives as a parent term and gains exactly one
`1/7` child with the opposite sign. -/
theorem roughMertens_one_eq_twoTenWheel_eightBands (B : ℕ) :
    roughMertens 1 B =
      roughInterval 210 (B / 2) B -
        roughInterval 210 (B / 14) (B / 7) -
        roughInterval 210 (B / 10) (B / 5) +
        roughInterval 210 (B / 70) (B / 35) -
        roughInterval 210 (B / 6) (B / 3) +
        roughInterval 210 (B / 42) (B / 21) +
        roughInterval 210 (B / 30) (B / 15) -
        roughInterval 210 (B / 210) (B / 105) := by
  have hsq6 : Squarefree 6 := by
    simpa using
      (Nat.squarefree_mul (by norm_num : Nat.Coprime 2 3)).2
        ⟨Nat.prime_two.squarefree, (show Nat.Prime 3 by norm_num).squarefree⟩
  have hsq30 : Squarefree 30 := by
    simpa using
      (Nat.squarefree_mul (by norm_num : Nat.Coprime 5 6)).2
        ⟨(show Nat.Prime 5 by norm_num).squarefree, hsq6⟩
  have hsq210 : Squarefree 210 := by
    simpa using
      (Nat.squarefree_mul (by norm_num : Nat.Coprime 7 30)).2
        ⟨(show Nat.Prime 7 by norm_num).squarefree, hsq30⟩
  have htop :=
    roughInterval_wheel_recursion
      (W := 210) (p := 7) (by norm_num) (by norm_num) hsq210 (B / 2) B
  have hten :=
    roughInterval_wheel_recursion
      (W := 210) (p := 7) (by norm_num) (by norm_num) hsq210 (B / 10) (B / 5)
  have hsix :=
    roughInterval_wheel_recursion
      (W := 210) (p := 7) (by norm_num) (by norm_num) hsq210 (B / 6) (B / 3)
  have hthirty :=
    roughInterval_wheel_recursion
      (W := 210) (p := 7) (by norm_num) (by norm_num) hsq210 (B / 30) (B / 15)
  norm_num at htop hten hsix hthirty
  have htop' :
      roughInterval 30 (B / 2) B =
        roughInterval 210 (B / 2) B -
          roughInterval 210 (B / 14) (B / 7) := by
    simpa [Nat.div_div_eq_div_mul] using htop
  have hten' :
      roughInterval 30 (B / 10) (B / 5) =
        roughInterval 210 (B / 10) (B / 5) -
          roughInterval 210 (B / 70) (B / 35) := by
    simpa [Nat.div_div_eq_div_mul] using hten
  have hsix' :
      roughInterval 30 (B / 6) (B / 3) =
        roughInterval 210 (B / 6) (B / 3) -
          roughInterval 210 (B / 42) (B / 21) := by
    simpa [Nat.div_div_eq_div_mul] using hsix
  have hthirty' :
      roughInterval 30 (B / 30) (B / 15) =
        roughInterval 210 (B / 30) (B / 15) -
          roughInterval 210 (B / 210) (B / 105) := by
    simpa [Nat.div_div_eq_div_mul] using hthirty
  rw [roughMertens_one_eq_thirtyWheel_fourBands B,
    htop', hten', hsix', hthirty']
  ring

end RHLean.Proof
