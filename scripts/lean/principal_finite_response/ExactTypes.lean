import «research.oai_434.VF919PrincipalResponseMass»

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

#check principal_response_terms_eval
#check principal_response_terms_mass_le
#check principal_response_terms_mass_uniform
#check principal_product_response_terms_eval
#check principal_product_response_terms_mass
#check principal_product_response_delays
#check principal_product_response_original_error

example (K : ℕ) (Q : ℝ) (hQ : 0 < Q) (A eta s : ℂ) :
    1 + FiniteResponse.eval s (principalResponseTerms K Q A eta) =
      principalSlotPartial K Q A eta s :=
  principal_response_terms_eval K Q hQ A eta s

example {κ ι : Type*} (K : ℕ) (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A eta : κ → ι → ℂ)
    (P theta : ℝ) (hP : 1 ≤ P) (htheta : 3 / 5 ≤ theta)
    (hr : P ^ (2 - 6 * theta) + P ^ (-theta) ≤ 1 / 2)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (heta : ∀ j ∈ S, ∀ i ∈ T j, ‖eta j i‖ ≤ 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    FiniteResponse.mass theta (principalProductResponseTerms K S T w Q A eta) ≤
      (1 + 2 * (P ^ (2 - 6 * theta) + P ^ (-theta) + P ^ (3 - 5 * theta))) ^ S.card - 1 :=
  principal_product_response_terms_mass K S T w Q A eta P theta hP htheta hr hw hQ hA heta hM

#print axioms principal_product_response_terms_eval
#print axioms principal_product_response_terms_mass
#print axioms principal_product_response_delays
#print axioms principal_product_response_original_error

