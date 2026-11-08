import «research.TWOAB_RENEWAL_COMPLETE_BAND_20261108»
import «research.oai_434.VF919ExplicitSlotTotalMass»

/-!
# The established strict OAI exponent applies to complete 2ab renewal bands

No new cancellation hypothesis.  The finite, source-faithful complete-parent
band is EXACTLY a difference of ordinary historical Mertens values.  The
already-certified November 8 source growth theorem therefore bounds every
such completed band at the HISTORICAL endpoint scale.

This is a proper-subpopulation theorem, NOT a new global exponent and NOT a
bound on a parent diagonal or the discarded long-fibre complement.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open OAI.SevenEighths.Parameters

/-- Existing OAI cancellation, transported through exact 2ab parent+daughter
completion with all positive exponent losses and one scale-independent C.

The critical gain is in using the complete signed band BEFORE estimating;
the result does NOT claim the complementary z<a population is small. -/
theorem twoABCompleteReciprocalBand_native_oai_bound
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R a b : ℕ), 2 ≤ R → 1 ≤ a → a ≤ b → b < R →
        ‖twoABCompleteReciprocalBand R a b‖ ≤
          C * Real.rpow ((squareRootEndpoint R / a : ℕ) : ℝ)
            ((7 / 8 : ℝ) - 1 / (48 * (explicitSlotCount : ℝ)) + eps) +
          C * Real.rpow ((squareRootEndpoint R / (b + 1) : ℕ) : ℝ)
            ((7 / 8 : ℝ) - 1 / (48 * (explicitSlotCount : ℝ)) + eps) := by
  obtain ⟨C, hC, hbound⟩ :=
    RHLean.Analysis.native_mertens_explicit_slot_count_total_mass eps heps
  refine ⟨C, hC, ?_⟩
  intro R a b hR ha hab hbR
  have hsq : R + 1 ≤ R ^ 2 := by nlinarith
  have hRX : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have haX : a ≤ squareRootEndpoint R := by omega
  have hbX : b + 1 ≤ squareRootEndpoint R := by omega
  have haDiv : 1 ≤ squareRootEndpoint R / a :=
    (Nat.one_le_div_iff (by omega : 0 < a)).2 haX
  have hbDiv : 1 ≤ squareRootEndpoint R / (b + 1) :=
    (Nat.one_le_div_iff (by omega : 0 < b + 1)).2 hbX
  calc
    ‖twoABCompleteReciprocalBand R a b‖ ≤
        ‖mertensSummatory (squareRootEndpoint R / a)‖ +
          ‖mertensSummatory (squareRootEndpoint R / (b + 1))‖ :=
            twoABCompleteReciprocalBand_norm_le_endpoints
              R a b hR ha hab hbR
    _ ≤
        C * Real.rpow ((squareRootEndpoint R / a : ℕ) : ℝ)
          ((7 / 8 : ℝ) - 1 / (48 * (explicitSlotCount : ℝ)) + eps) +
        C * Real.rpow ((squareRootEndpoint R / (b + 1) : ℕ) : ℝ)
          ((7 / 8 : ℝ) - 1 / (48 * (explicitSlotCount : ℝ)) + eps) :=
            add_le_add (hbound _ haDiv) (hbound _ hbDiv)

#print axioms twoABCompleteReciprocalBand_native_oai_bound

end RHLean.Proof
