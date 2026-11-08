import «research.TWOAB_RENEWAL_COMPLETE_BAND_20261108»
import «research.MERTENS_EXPONENT_ENVELOPES»

/-!
# Reuse ANY established Mertens exponent on a complete 2ab band

The existing 1 -> 7/8 OAI cancellation, and the stronger November 8
total-slot-mass gain, enter through the separately proved
MertensGrowthAtMost input at their ACTUAL exponents.

This file is a source-faithful, independent consumer.  It does not import
the very large OAI pinned/GENERATED proof environment into every downstream
2ab user.  The original complete OAI source is proved separately; the
closed theorem native_mertens_explicit_slot_count_total_mass supplies this
consumer's hgrowth at b=7/8-1/(48*explicitSlotCount).

No new arithmetic cancellation premise is introduced; an arbitrary
unverified growth hypothesis does NOT prove any unconditional exponent.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Analysis.MertensExponent

/-- The exact 2ab parent-completed band is controlled by any already
certified global Mertens exponent, with a uniform constant independent of all
R,a,b, including every positive exponent loss.  This is a proper-subpopulation
bound, not a gain on the global endpoint itself. -/
theorem twoABCompleteReciprocalBand_of_mertensGrowth
    (beta eps : ℝ) (heps : 0 < eps)
    (hgrowth : MertensGrowthAtMost beta) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R a b : ℕ), 2 ≤ R → 1 ≤ a → a ≤ b → b < R →
        ‖twoABCompleteReciprocalBand R a b‖ ≤
          C * Real.rpow ((squareRootEndpoint R / a : ℕ) : ℝ)
            (beta + eps) +
          C * Real.rpow ((squareRootEndpoint R / (b + 1) : ℕ) : ℝ)
            (beta + eps) := by
  obtain ⟨C, hC, hbound⟩ := hgrowth eps heps
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
          (beta + eps) +
        C * Real.rpow ((squareRootEndpoint R / (b + 1) : ℕ) : ℝ)
          (beta + eps) :=
            add_le_add (hbound _ haDiv) (hbound _ hbDiv)

/-- Exact adapter to the already-certified strict OAI exponent, without
introducing a dependency on its generated source files into the 2ab kernel.

Instantiating N with the ACTUAL existing explicitSlotCount and hsource with
native_mertens_explicit_slot_count_total_mass is a separately-certified
application, not a new analytic input or an unconditional assertion here.
-/
theorem twoABCompleteReciprocalBand_of_strict_oai_input
    (N : ℕ) (_hN : 0 < N)
    (hsource : MertensGrowthAtMost
      ((7 / 8 : ℝ) - 1 / (48 * (N : ℝ))))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R a b : ℕ), 2 ≤ R → 1 ≤ a → a ≤ b → b < R →
        ‖twoABCompleteReciprocalBand R a b‖ ≤
          C * Real.rpow ((squareRootEndpoint R / a : ℕ) : ℝ)
            ((7 / 8 : ℝ) - 1 / (48 * (N : ℝ)) + eps) +
          C * Real.rpow ((squareRootEndpoint R / (b + 1) : ℕ) : ℝ)
            ((7 / 8 : ℝ) - 1 / (48 * (N : ℝ)) + eps) := by
  exact twoABCompleteReciprocalBand_of_mertensGrowth
    ((7 / 8 : ℝ) - 1 / (48 * (N : ℝ))) eps heps hsource

#print axioms twoABCompleteReciprocalBand_of_mertensGrowth
#print axioms twoABCompleteReciprocalBand_of_strict_oai_input

end RHLean.Proof
