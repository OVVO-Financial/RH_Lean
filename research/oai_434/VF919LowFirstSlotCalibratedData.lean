import «research.oai_434.VF919LowFirstPhysicalTiltFullBudget»

/-!
Source-calibrated HIGH data. Exact-head CI determines verification status.
Raise the HIGH saving to a fixed fraction of the actual minimum slot mass.
Only sigma is changed after the existing eps cap; no source slot is changed.
-/
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.RHLeanFullPhysicalTilt
open Parameters RHLeanFiniteSlotGap

def slotCalibratedHighDataLowFirst {Delta : ℝ} (D : HighData Delta) : HighData Delta := by
  let E := cappedHighData D
  let m : ℝ := (7/8) * E.rmin
  have hm : 0 < m := mul_pos (by norm_num) E.rmin_pos
  have hslot := E.slots_bounds ⟨0, E.slots_pos⟩
  have hmT : m ≤ E.t / 200 := by
    dsimp [m]
    linarith only [hslot.2.1, hslot.2.2]
  have hs := capped_high_data_bounds D
  change E.ε ≤ E.t / 2000 ∧ E.e ≤ E.t / 2000 ∧
    ((E.N : ℝ) + 8) * E.eps ≤ E.t ∧
    E.sigma ≤ m / 4 ∧ E.e ≤ m / 4 at hs
  refine { E with
    sigma := m / 4
    sigma_pos := div_pos hm (by norm_num)
    geometric_budget := ?_
    principal_budget := ?_
    window_budget := ?_
    floor_budget := ?_
    high_saving := ?_ }
  · linarith only [hmT, hs.2.1, E.t_small]
  · linarith only [hmT, E.t_small]
  · change m / 4 + E.e ≤ (7/8) * m
    linarith only [hs.2.2.2.2, hm]
  · linarith only [hmT, hs.2.1, hs.2.2.1, E.t_small]
  · linarith only [hmT, E.t_pos]

theorem slotCalibratedHighDataLowFirst_geometry {Delta : ℝ} (D : HighData Delta) :
    (slotCalibratedHighDataLowFirst D).t = D.t ∧
    (slotCalibratedHighDataLowFirst D).e = D.e ∧
    (slotCalibratedHighDataLowFirst D).rmin = D.rmin ∧
    (slotCalibratedHighDataLowFirst D).ell = D.ell := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem slotCalibratedHighDataLowFirst_reserves {Delta : ℝ} (D : HighData Delta) :
    let E := slotCalibratedHighDataLowFirst D
    E.ε ≤ E.t / 2000 ∧ E.e ≤ E.t / 2000 ∧
      ((E.N : ℝ) + 8) * E.eps ≤ E.t ∧
      E.sigma = 6 * slotTiltLowFirst E := by
  have h := capped_high_data_bounds D
  dsimp only
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  change ((7/8 : ℝ) * D.rmin) / 4 = 6 * (((7/8 : ℝ) * D.rmin) / 24)
  ring

/-- The constructor proves nonvacuity before choosing any character or zero. -/
theorem exists_slot_calibrated_data_low_first (Delta : ℝ) (hDelta : 0 < Delta)
    (mesh : ℝ -> ℝ) (hmesh : ∀ t : ℝ, 0 < t -> 0 < mesh t) :
    ∃ D : HighData Delta,
      (∀ j, D.ell j ≤ mesh D.t / 200) ∧
      D.ε ≤ D.t / 2000 ∧ D.e ≤ D.t / 2000 ∧
      ((D.N : ℝ) + 8) * D.eps ≤ D.t ∧
      D.sigma = 6 * slotTiltLowFirst D := by
  obtain ⟨D, hfine⟩ := Parameters.exists_high_data_fine Delta hDelta mesh hmesh
  exact ⟨slotCalibratedHighDataLowFirst D, hfine, slotCalibratedHighDataLowFirst_reserves D⟩

#print axioms slotCalibratedHighDataLowFirst
#print axioms exists_slot_calibrated_data_low_first
end SevenEighths.RHLeanFullPhysicalTilt
end
end OAI
