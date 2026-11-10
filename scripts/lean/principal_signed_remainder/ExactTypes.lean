import «research.oai_434.VF919PrincipalSignedRemainder»

open OAI.SevenEighths.PrincipalSlotEstimate

example : ∀ {Q : ℝ} {A eta s : ℂ}, 480 ≤ Q → ‖A‖ ≤ 1 → ‖eta‖ = 1 →
    7 / 8 ≤ s.re →
    ‖principalSlot Q A eta s + 1 + eta * (Q : ℂ) ^ (-s)‖ ≤
      12 * Q ^ (-(11 / 8 : ℝ)) := @principal_slot_signed_error

#check principal_K_signed
#check principal_slot_signed_error
#check actual_principal_slot_signed_error
#check weighted_principal_slot_signed_error
#check weighted_principal_slot_signed_relative_error
#print axioms principal_slot_signed_error
#print axioms actual_principal_slot_signed_error
#print axioms weighted_principal_slot_signed_error
#print axioms weighted_principal_slot_signed_relative_error
