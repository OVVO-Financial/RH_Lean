import Mathlib

/-!
# Grouped product-fiber multiplicity obstruction

This module formalizes the independently reviewed claims
`20261023-referee-1` and the abstract part of `20261023-wheel-1`.

A valuation cap controls the contribution of each tuple in a product fiber.
After tuples with the same product are grouped, the unavoidable extra factor is
the total mass of that fiber. The final theorem gives finite fibers of arbitrary
size with unit per-tuple valuation contribution, ruling out any deduction of a
uniform grouped-label cap from valuation alone.

These are finite combinatorial obstruction theorems. They do not assert that
the actual OAI source realizes the witness fibers, and they do not bound the
weighted physical coefficient, prove claim (A), or supply an analytic saving.
-/

open scoped BigOperators

namespace RHLean.Analysis

/-- A pointwise valuation cap survives grouping only after multiplication by
the cardinality of the product fiber. This is claim (1) in
`20261023-referee-1`. -/
theorem productFiber_unweighted_degree_le
    {α : Type*} [DecidableEq α]
    (T : Finset α) (contribution : α → ℕ) (valuation : ℕ)
    (hcap : ∀ x ∈ T, contribution x ≤ valuation) :
    ∑ x ∈ T, contribution x ≤ valuation * T.card := by
  calc
    ∑ x ∈ T, contribution x ≤ ∑ _x ∈ T, valuation := by
      exact Finset.sum_le_sum fun x hx => hcap x hx
    _ = valuation * T.card := by
      simp [Nat.mul_comm]

/-- Weighted product-fiber form of the valuation bound. Nonnegative physical
label weights retain the whole fiber mass rather than disappearing under
grouping. This is claim (2) in `20261023-referee-1`. -/
theorem productFiber_weighted_degree_le
    {α : Type*} [DecidableEq α]
    (T : Finset α) (contribution : α → ℕ) (weight : α → ℝ)
    (valuation : ℕ)
    (hweight : ∀ x ∈ T, 0 ≤ weight x)
    (hcap : ∀ x ∈ T, contribution x ≤ valuation) :
    ∑ x ∈ T, weight x * (contribution x : ℝ) ≤
      (valuation : ℝ) * ∑ x ∈ T, weight x := by
  calc
    ∑ x ∈ T, weight x * (contribution x : ℝ) ≤
        ∑ x ∈ T, weight x * (valuation : ℝ) := by
      exact Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcap x hx)) (hweight x hx)
    _ = (valuation : ℝ) * ∑ x ∈ T, weight x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring

/-- Unit per-label valuation contribution permits product fibers of arbitrary
finite size. Hence valuation alone cannot give a uniform bound for the grouped
label degree; a fiber-mass or phase-sensitive theorem is indispensable. -/
theorem productFiber_unit_cap_arbitrary_degree (K : ℕ) :
    let labels := Finset.univ : Finset (Fin (K + 1))
    let contribution : Fin (K + 1) → ℕ := fun _ => 1
    (∀ x ∈ labels, contribution x ≤ 1) ∧
      (∑ x ∈ labels, contribution x) = K + 1 := by
  dsimp
  constructor
  · intro x _hx
    rfl
  · simp

end RHLean.Analysis

#print axioms RHLean.Analysis.productFiber_unweighted_degree_le
#print axioms RHLean.Analysis.productFiber_weighted_degree_le
#print axioms RHLean.Analysis.productFiber_unit_cap_arbitrary_degree
