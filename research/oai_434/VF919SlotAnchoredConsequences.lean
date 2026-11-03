import «research.oai_434.VF919SlotAnchoredEndpoint»

/-!
# Actual Mertens and signed-energy consequences with the same constructed tilt

The source witness precedes every positive exponent loss and every integer.
The diagonal is retained. No sharp local sum-of-squares estimate is inferred.
-/
noncomputable section
namespace RHLean.Analysis
open MertensExponent OAI.SevenEighths
open RHLeanNativeSevenEighthsReplay RHLeanFullPhysicalTilt

theorem native_slot_tilt_growth_exponent :
    ∃ D : Parameters.HighData (1/1000000 : ℝ),
      0 < slotTilt D ∧ mertensGrowthExponent ≤ 7/8 - slotTilt D := by
  obtain ⟨D, hD, hbound⟩ := native_beta_le_constructed_slot_tilt
  refine ⟨D, hD, ?_⟩
  rw [growthExponent_eq_rightmost]
  exact native_zeta_rightmost_le_hecke_beta.trans hbound

theorem native_slot_tilt_fixed_power :
    ∃ D : Parameters.HighData (1/1000000 : ℝ),
      0 < slotTilt D ∧ MertensPowerBound (7/8 - slotTilt D / 2) := by
  obtain ⟨D, hD, hgrowth⟩ := native_mertens_constructed_slot_tilt
  refine ⟨D, hD, ?_⟩
  convert hgrowth (slotTilt D / 2) (by positivity) using 1 <;> ring

theorem native_slot_tilt_signed_pairs :
    ∃ D : Parameters.HighData (1/1000000 : ℝ),
      0 < slotTilt D ∧ ∀ eps : ℝ, 0 < eps →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x →
          2 * realMertensPositiveLagPairSum (x+1) ≤
            (C * Real.rpow (x:ℝ) (7/8-slotTilt D+eps))^2 -
              realMertensDiagonal (x+1) := by
  obtain ⟨D, hD, hgrowth⟩ := native_mertens_constructed_slot_tilt
  refine ⟨D, hD, ?_⟩
  intro eps heps
  obtain ⟨C, hC, hbound⟩ := hgrowth eps heps
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hsquare : ‖mertensSummatory x‖^2 ≤
      (C * Real.rpow (x:ℝ) (7/8-slotTilt D+eps))^2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg x) _))).mpr (hbound x hx)
  rw [vf919_mertens_sq_eq_signedPair] at hsquare
  linarith only [hsquare]

theorem native_slot_tilt_signed_energy :
    ∃ D : Parameters.HighData (1/1000000 : ℝ),
      0 < slotTilt D ∧ ∀ eps : ℝ, 0 < eps →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x →
          realMertensDiagonal (x+1) + 2 * realMertensPositiveLagPairSum (x+1) ≤
            C * Real.rpow (x:ℝ) (7/4-2*slotTilt D+eps) := by
  obtain ⟨D, hD, hgrowth⟩ := native_mertens_constructed_slot_tilt
  refine ⟨D, hD, ?_⟩
  intro eps heps
  obtain ⟨C, hC, hbound⟩ := hgrowth (eps/2) (by positivity)
  refine ⟨C^2, sq_nonneg C, ?_⟩
  intro x hx
  have hxpos : (0:ℝ) < x := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx)
  have hsquare : ‖mertensSummatory x‖^2 ≤
      (C * Real.rpow (x:ℝ) (7/8-slotTilt D+eps/2))^2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg x) _))).mpr (hbound x hx)
  rw [vf919_mertens_sq_eq_signedPair] at hsquare
  apply hsquare.trans_eq
  rw [mul_pow, ← Real.rpow_mul_natCast hxpos.le]
  congr 2 <;> ring

#check native_slot_tilt_growth_exponent
#print axioms native_slot_tilt_growth_exponent
#check native_slot_tilt_fixed_power
#print axioms native_slot_tilt_fixed_power
#print axioms native_slot_tilt_signed_pairs
#print axioms native_slot_tilt_signed_energy
end RHLean.Analysis
