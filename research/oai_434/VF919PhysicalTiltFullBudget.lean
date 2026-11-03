import «research.oai_434.VF919TiltedProbe»

/-!
# Physical tilt budgets for the unchanged finite source

The slot-sized tilt is fixed from the source geometry before the character
and the arbitrary LOW loss. No new analytic premise is introduced here.
-/
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.RHLeanFullPhysicalTilt
open Parameters RHLeanFiniteSlotGap

theorem full_tilt_budget {Delta : ℝ} (D : HighData Delta) :
    0 < D.e ∧
    24 * D.e < (7 / 8 : ℝ) * D.rmin ∧
    D.e < 1 / 960 ∧
    24 * D.e < D.t := by
  have hs := high_data_small_errors D
  have hdet : 576 * D.e ≤ D.ε := by
    linarith only [D.detector_budget, D.kappa_pos, D.cost_pos]
  have hrt := mul_le_mul_of_nonneg_left D.t_small D.rmin_pos.le
  refine ⟨D.e_pos, ?_, ?_, ?_⟩
  · nlinarith only [hdet, D.epsilon_gap, hrt, D.rmin_pos]
  · linarith only [D.e_small]
  · linarith only [hs.2.1, D.t_pos]

theorem tilt_interval_budget {Delta : ℝ} (D : HighData Delta)
    (tilt : ℝ) (hpos : 0 < tilt) (hle : tilt ≤ D.e) :
    0 < tilt ∧
    24 * tilt < (7 / 8 : ℝ) * D.rmin ∧
    tilt < 1 / 960 ∧
    24 * tilt < D.t := by
  obtain ⟨_, hslot, hsmall, htail⟩ := full_tilt_budget D
  refine ⟨hpos, ?_, hle.trans_lt hsmall, ?_⟩ <;> linarith

theorem low_up_to_full_tilt {Delta : ℝ} {D : HighData Delta}
    (F : ProbeFinalAssembly.SourceData D)
    (tilt : ℝ) (hpos : 0 < tilt) (hle : tilt ≤ D.e)
    (loss : ℝ) (hloss : 0 < loss) (chi : HeckeFamily.Character) :
    Asymptotics.IsBigO Filter.atTop (F.tiltedProbe tilt chi)
      (fun Z : ℝ => Z ^ (3 / 16 - 9 * tilt + loss)) := by
  obtain ⟨_, hslot, hsmall, _⟩ := tilt_interval_budget D tilt hpos hle
  exact F.tiltedProbe_low tilt hpos.le hsmall hslot.le loss hloss chi

theorem floor_near_endpoint_budget {Delta : ℝ} (D : HighData Delta)
    (he : D.e ≤ D.t / 2000)
    (heps : ((D.N : ℝ) + 8) * D.eps ≤ D.t) :
    2 * D.t + 26 * D.e + ((D.N : ℝ) + 8) * D.eps +
      D.t + D.t / 6 + D.t / 8 + D.sigma + D.e ≤ 7 / 1200 := by
  linarith only [he, heps, D.high_saving, D.t_small]

theorem central_near_endpoint_budget {Delta : ℝ} (D : HighData Delta)
    (he : D.e ≤ D.t / 2000) :
    (1 / 1000000 : ℝ) + D.sigma + D.t / 8 + D.t / 8 + D.e
      ≤ 49 / 881280 := by
  linarith only [he, D.high_saving, D.t_small]

/-- A tilt determined by the actual positive lower slot mass. -/
def slotTilt {Delta : ℝ} (D : HighData Delta) : ℝ :=
  ((7 / 8 : ℝ) * D.rmin) / 48

theorem slot_tilt_budget {Delta : ℝ} (D : HighData Delta) :
    0 < slotTilt D ∧
    24 * slotTilt D < (7 / 8 : ℝ) * D.rmin ∧
    slotTilt D < 1 / 960 ∧
    24 * slotTilt D < D.t := by
  have hslot := D.slots_bounds ⟨0, D.slots_pos⟩
  have hminimum : (7 / 8 : ℝ) * D.rmin ≤ D.t / 200 := by
    linarith only [hslot.2.1, hslot.2.2]
  dsimp [slotTilt]
  refine ⟨div_pos (mul_pos (by norm_num) D.rmin_pos) (by norm_num), ?_, ?_, ?_⟩
  · linarith only [D.rmin_pos]
  · linarith only [hminimum, D.t_small]
  · linarith only [hminimum, D.t_pos]

/-- This comparison concerns source parameters, not a separate global gain. -/
theorem slot_tilt_dominates_detector_scale {Delta : ℝ} (D : HighData Delta) :
    1050000000 * D.e < slotTilt D := by
  have hdet : 576 * D.e ≤ D.ε := by
    linarith only [D.detector_budget, D.kappa_pos, D.cost_pos]
  have hrt := mul_le_mul_of_nonneg_left D.t_small D.rmin_pos.le
  dsimp [slotTilt]
  nlinarith only [hdet, D.epsilon_gap, hrt]

theorem low_at_slot_tilt {Delta : ℝ} {D : HighData Delta}
    (F : ProbeFinalAssembly.SourceData D)
    (loss : ℝ) (hloss : 0 < loss) (chi : HeckeFamily.Character) :
    Asymptotics.IsBigO Filter.atTop (F.tiltedProbe (slotTilt D) chi)
      (fun Z : ℝ => Z ^ (3 / 16 - 9 * slotTilt D + loss)) := by
  obtain ⟨hpos, hslot, hsmall, _⟩ := slot_tilt_budget D
  exact F.tiltedProbe_low (slotTilt D) hpos.le hsmall hslot.le loss hloss chi

#print axioms slot_tilt_budget
#print axioms slot_tilt_dominates_detector_scale
#print axioms low_at_slot_tilt
#print axioms full_tilt_budget
#print axioms low_up_to_full_tilt
#print axioms floor_near_endpoint_budget
#print axioms central_near_endpoint_budget
end SevenEighths.RHLeanFullPhysicalTilt
end
end OAI
