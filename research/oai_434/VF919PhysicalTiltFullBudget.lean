import «research.oai_434.VF919TiltedProbe»

/-!
LOW-first contraction ledger. The slot tilt saturates the certified
non-strict slot-charge gate. This is the same complete signed physical probe,
not a separate bound on the unsigned pieces. Exact-head CI determines status.
-/
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.RHLeanFullPhysicalTilt
open Parameters RHLeanFiniteSlotGap

/-- Saturate the existing certified slot-charge inequality. -/
def slotTilt {Delta : Real} (D : HighData Delta) : Real :=
  ((7 / 8 : Real) * D.rmin) / 24

theorem slot_tilt_exact_charge {Delta : Real} (D : HighData Delta) :
    24 * slotTilt D = (7 / 8 : Real) * D.rmin := by
  unfold slotTilt
  ring

/-- The complete LOW theorem uses a non-strict slot inequality. -/
theorem slot_tilt_budget {Delta : Real} (D : HighData Delta) :
    0 < slotTilt D ∧
    24 * slotTilt D ≤ (7 / 8 : Real) * D.rmin ∧
    slotTilt D < 1 / 960 ∧
    24 * slotTilt D < D.t := by
  have hslot := D.slots_bounds ⟨0, D.slots_pos⟩
  have hminimum : (7 / 8 : Real) * D.rmin ≤ D.t / 200 := by
    linarith only [hslot.2.1, hslot.2.2]
  have hm : 0 < (7 / 8 : Real) * D.rmin :=
    mul_pos (by norm_num) D.rmin_pos
  dsimp [slotTilt]
  refine ⟨div_pos hm (by norm_num), ?_, ?_, ?_⟩
  · linarith
  · linarith only [hminimum, D.t_small]
  · linarith only [hminimum, D.t_pos]

/-- Maximal for this sufficient gate, not a claimed arithmetic optimum. -/
theorem gate_implies_tilt_le_slotTilt {Delta : Real} (D : HighData Delta)
    (tilt : Real) (hgate : 24 * tilt ≤ (7 / 8 : Real) * D.rmin) :
    tilt ≤ slotTilt D := by
  unfold slotTilt
  linarith only [hgate]

/-- An existing complete analytic LOW estimate, specialized at the new tilt. -/
theorem low_at_slot_tilt {Delta : Real} {D : HighData Delta}
    (F : ProbeFinalAssembly.SourceData D)
    (loss : Real) (hloss : 0 < loss) (chi : HeckeFamily.Character) :
    Asymptotics.IsBigO Filter.atTop (F.tiltedProbe (slotTilt D) chi)
      (fun Z : Real => Z ^ (3 / 16 - 9 * slotTilt D + loss)) := by
  obtain ⟨hpos, hslot, hsmall, _⟩ := slot_tilt_budget D
  exact F.tiltedProbe_low (slotTilt D) hpos.le hsmall hslot loss hloss chi

/-- Exact one-component exchange rate: a row-energy gain gamma contributes
half as much at the amplitude crossing. No gain is asserted by this identity. -/
theorem low_energy_crossing (x y gamma : Real) :
    (5*x+y)/12-gamma/2-(x/3-5/6+1/36) =
      7/8-(5/6-(x+y))/12-gamma/2 := by
  ring

/-- The tilt lowers LOW by 9 delta and the signal by 8 delta. -/
theorem tilted_low_crossing (tilt : Real) :
    (3/16-9*tilt)-(-11/16-8*tilt) = (7/8 : Real)-tilt := by
  ring

/-- Recombination of two proved amplitude exponents keeps their maximum.
Thus a LOW improvement realizes its full gain while HIGH has enough reserve. -/
theorem complete_crossing_ledger (baseline lowGain highGain : Real) :
    max (baseline-lowGain) (baseline-highGain) =
      baseline-min lowGain highGain := by
  by_cases h : lowGain ≤ highGain
  · rw [min_eq_left h, max_eq_left (by linarith)]
  · have h' : highGain ≤ lowGain := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right h', max_eq_right (by linarith)]

#print axioms slot_tilt_budget
#print axioms low_at_slot_tilt
#print axioms low_energy_crossing
#print axioms complete_crossing_ledger
end SevenEighths.RHLeanFullPhysicalTilt
end OAI
