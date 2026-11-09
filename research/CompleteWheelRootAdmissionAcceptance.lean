import «research.CompleteWheelRootAdmission»

/-! Exact public types and axiom checks for the complete-wheel component bound.
The final discrepancy estimate is deliberately not an assumption or conclusion.
-/

open Finset
open scoped BigOperators
open RHLean.Arithmetic RHLean.Proof RHLean.Analysis

noncomputable section

example (r : ℕ) (hr : 2 ≤ r) (L : ℝ) :
    finiteWheelCenteredAt r (squareRootEndpoint (r + 1)) L -
        finiteWheelCenteredAt (r - 1) (squareRootEndpoint (r + 1)) L =
      if r = 2 then 3 else
        if r.Prime then 1 + (if (r + 2).Prime then 1 else 0) else 0 :=
  finiteWheel_centered_next_root_step r hr L

example (A B : ℕ) (hA : 2 ≤ A) :
    0 ≤ ∑ r ∈ Finset.Ico A B, finiteWheelRootAdmission r ∧
      (∑ r ∈ Finset.Ico A B, finiteWheelRootAdmission r) ≤
        2 * (B - A : ℕ) + if A = 2 ∧ A < B then 1 else 0 :=
  finiteWheel_rootAdmission_sum_bounds A B hA

example (r : ℕ) (hr : 2 ≤ r) (L : ℝ) :
    finiteWheelCenteredAt r (squareRootEndpoint r) L =
      finiteWheelCenteredAt (r - 1) (squareRootEndpoint r) L :=
  finiteWheel_centered_old_root_step r hr L

example (r : ℕ) (L₀ L₁ : ℝ) :
    finiteWheelCenteredAt r (squareRootEndpoint (r + 1)) L₁ -
        finiteWheelCenteredAt (r - 1) (squareRootEndpoint r) L₀ =
      L₁ - L₀ -
        ((vfMidPrefixWheelCounting (r - 1) (squareRootEndpoint (r + 1)) : ℝ) -
          (vfMidPrefixWheelCounting (r - 1) (squareRootEndpoint r) : ℝ)) +
        finiteWheelRootAdmission r :=
  finiteWheel_centered_root_return r L₀ L₁

example (r : ℕ) (L : ℝ) :
    finiteWheelCenteredAt (r - 1) (squareRootEndpoint r) L =
      finiteWheelFract (r - 1) (squareRootEndpoint r) -
        finiteWheelSquareDeterministic r L :=
  finiteWheel_centeredAt_square_source r L

#check @finiteWheel_pred_count_prime_add_two
#check @finiteWheel_centered_next_root_step
#check @finiteWheel_centered_old_root_step
#check @finiteWheel_rootAdmission_bounds
#check @finiteWheel_rootAdmission_sum_bounds
#check @finiteWheel_centered_root_return
#check @finiteWheel_centeredAt_square_source

/-- info: 'RHLean.Analysis.finiteWheel_centered_next_root_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteWheel_centered_next_root_step

/-- info: 'RHLean.Analysis.finiteWheel_centered_old_root_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteWheel_centered_old_root_step

/-- info: 'RHLean.Analysis.finiteWheel_rootAdmission_sum_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteWheel_rootAdmission_sum_bounds

/-- info: 'RHLean.Analysis.finiteWheel_centered_root_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteWheel_centered_root_return

/-- info: 'RHLean.Analysis.finiteWheel_centeredAt_square_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finiteWheel_centeredAt_square_source

#print axioms finiteWheel_centered_next_root_step
#print axioms finiteWheel_rootAdmission_sum_bounds
#print axioms finiteWheel_centered_root_return
