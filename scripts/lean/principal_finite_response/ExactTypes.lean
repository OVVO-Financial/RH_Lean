import «research.oai_434.VF919PrincipalFiniteResponse»

open scoped BigOperators
open OAI.SevenEighths.PrincipalSlotEstimate

#check principal_slot_response_exact
#check principal_slot_partial_tail
#check principal_slot_partial_error
#check principal_slot_partial_norms
#check weighted_principal_product_partial_error
#check exists_principal_truncation_order
#check weighted_principal_product_partial_power

example (K : ℕ) {Q : ℝ} {A eta s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1)
    (hs : 7 / 8 ≤ s.re) :
    ‖-principalSlot Q A eta s - principalSlotPartial K Q A eta s‖ ≤
      4 * (2 * Q ^ (-(7 / 8 : ℝ))) ^ (K + 1) :=
  principal_slot_partial_error K hQ hA heta hs

example {κ ι : Type*} (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A eta : κ → ι → ℂ) (s : ℂ) (P : ℝ) (K : ℕ)
    (hP : 480 ≤ P) (hs : 7 / 8 ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (heta : ∀ j ∈ S, ∀ i ∈ T j, ‖eta j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (eta j i) s) /
          principalScalar S (fun j => ∑ i ∈ T j, w j i) -
        ∏ j ∈ S, (∑ i ∈ T j, (w j i : ℂ) *
          principalSlotPartial K (Q j i) (A j i) (eta j i) s) /
            (∑ i ∈ T j, w j i : ℝ)‖ ≤
      S.card * (5 : ℝ) ^ S.card * (4 * (2 * P ^ (-(7 / 8 : ℝ))) ^ (K + 1)) :=
  weighted_principal_product_partial_error S T w Q A eta s P K hP hs hw hQ hA heta hM

#print axioms principal_slot_response_exact
#print axioms principal_slot_partial_tail
#print axioms principal_slot_partial_error
#print axioms weighted_principal_product_partial_error
#print axioms weighted_principal_product_partial_power
#print axioms exists_principal_truncation_order
