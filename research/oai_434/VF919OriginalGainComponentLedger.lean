import «research.oai_434.VF919NativeSourceMoments»
import «research.oai_434.VF919ActualSlotMinRetighten»
import «research.oai_434.VF919TiltedProbe»
import OAI.NumberTheory.DirichletL.Hecke.DetectorBranchBudget

/-!
# The ACTUAL OAI 1 -> 7/8 cancellation path: first lost moment saving

This is a source-based loss audit, NOT a substitute owner hypothesis.

Original upstream source:
* Detector/DetectorPlainMarkedFineField: marked width 1+t/4 and
  stage error t/4; retained proof is 1+t/2.
* Hecke/DetectorRawFiber: inverse/marked/unmarked moments share epsilon_m.
* Hecke/DetectorCountFromMoments: the same epsilon_m is passed to all four
  no-slot/inverse/marked count branches, then merged via a maximum.
* PrimeRows/HighFromMoments: the shared row-count loss is paid against the
  sigma budget in the complete compensated HIGH source.

RH_Lean VF919OriginalMarkedSharpenedSignedNNS proves the ACTUAL marked
1+t/2 bound under the original positive source input.
RH_Lean VF919NativeSourceMoments presently relaxes that field to 1+t.
Below is the exact amount a branch-sensitive replacement could save.

NNS second partial moments are EXACTLY the same squared complex norm:
their introduction alone creates NO arithmetic saving.  The 1/8
improvement is instead the actual low-vs-principal signal separation.
-/

noncomputable section

namespace RHLean.Analysis.OAIOriginalGainAudit

open OAI.SevenEighths
open HeckeDetectorBranchBudget

/-- Fixed OAI physical slot mass is exactly 1/6. The actual least
positive slot cannot exceed the total available mass. -/
theorem true_slot_min_le_sixth {Delta : ℝ}
    (D : OAI.SevenEighths.Parameters.HighData Delta) :
    OAI.SevenEighths.RHLeanActualSlotMin.actualSlotMinimum D ≤ 1 / 6 := by
  let j := OAI.SevenEighths.RHLeanActualSlotMin.leastSlotIndex D
  have hmin : D.ell j ≤ ∑ i, D.ell i :=
    Finset.single_le_sum
      (fun i _ => (D.slots_bounds i).1.le)
      (Finset.mem_univ j)
  rw [D.slots_sum] at hmin
  exact hmin

/-- The TRUE original 24-to-1 LOW slot-charge gate has a hard limit.
Repeatedly reusing the same finite physical source cannot accumulate
a tilt of 3/8: its entire certified tilt is <=1/144. -/
theorem slot_geometry_cannot_cover_RH_gap {Delta : ℝ}
    (D : OAI.SevenEighths.Parameters.HighData Delta) :
    OAI.SevenEighths.RHLeanActualSlotMin.actualSlotMinimum D / 24 ≤
      (1 / 144 : ℝ) := by
  have h := true_slot_min_le_sixth D
  linarith only [h]

/-- Signal minus LOW at the UNTILTED original exponent. At initial
beta=1 the difference is 1/8. It closes at beta=7/8. -/
theorem original_one_to_seven_eighths_gap (beta : ℝ) :
    (beta - 11 / 16) - 3 / 16 = beta - 7 / 8 := by ring

theorem original_initial_gap :
    ((1 : ℝ) - 11 / 16) - 3 / 16 = 1 / 8 := by
  norm_num

theorem original_gap_closes_at_seven_eighths :
    (((7 / 8 : ℝ) - 11 / 16) - 3 / 16) = 0 := by
  norm_num

/-- Same original source with the documented tilted physical lengths:
low=3/16-9*tilt, principal coefficient=-11/16-8*tilt.
Thus the gap is beta - 7/8 + tilt; not a beta->beta/2 renewal. -/
theorem physical_slot_tilt_reinvested_gap (beta tilt : ℝ) :
    (beta - 11 / 16 - 8 * tilt) -
      (3 / 16 - 9 * tilt) = beta - 7 / 8 + tilt := by
  ring

/-- Exact power exchange at the genuine OAI LOW inlet. The arithmetic
input must improve the FULL admitted signed squared inverse/tuple
source from baseline-+loss to baseline-saving+loss; the square-root
normalizer converts this into a saving/2 in LOW amplitude. -/
theorem original_signed_low_energy_sqrt_exchange
    (baseline loss saving : ℝ) :
    (baseline - saving + loss) / 2 =
      (baseline + loss) / 2 - saving / 2 := by
  ring

/-- At the original fixed physical geometry a saving nu in the
COMPLETE source energy, if retained through all compensations, moves
the exact LOW/principal crossing to 7/8-nu/2. This is an exchange
rate, NOT a proved saving or a new RH theorem. -/
theorem original_signed_low_improvement_exchange
    (beta nu : ℝ) :
    (beta - 11 / 16) - (3 / 16 - nu / 2) =
      beta - 7 / 8 + nu / 2 := by
  ring

/-- The original selected inverse row is bounded in energy at
5/6-2*d+507*eps. Replacing that source bound by the SAME admitted
signed-source family with a fixed nu saving would propagate half
the nu after the actual square-root normalization. -/
theorem original_inverse_energy_nominal_gain
    (d eps nu : ℝ) :
    ((5 / 6 - 2 * d + 507 * eps - nu) / 2) -
      ((5 / 6 - 2 * d + 507 * eps) / 2) = -nu / 2 := by
  ring

/-- Literal source moment price: RH_Lean proves the marked bound with
epsilon_m=t/2 but the common OAI row-count consumer is supplied t. -/
theorem retained_marked_half_error_is_real (t : ℝ) (ht : 0 < t) :
    0 < (1 + t) - (1 + t / 2) := by
  linarith

/-- The common row-count loss pays epsilon_m with coefficient exactly 1;
decreasing ALL moment losses by t/2 would save t/2. We have only proved
the improved marked field, NOT a decrease in all four sources. -/
theorem common_count_loss_half_t (epsilon t mesh nu : ℝ) :
    commonLoss epsilon t mesh nu -
      commonLoss epsilon (t / 2) mesh nu = t / 2 := by
  unfold commonLoss
  ring

/-- EXACT max-loss exchange rate for improving only one of two competing
OAI count branches. A smaller marked moment does not help when its branch
is not the actual binding one. -/
theorem one_branch_discount (a b d : ℝ) (hd : 0 ≤ d) :
    max a b - max a (b - d) =
      min d (max 0 (b - a)) := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab, max_eq_right (by linarith : (0 : ℝ) ≤ b - a)]
    by_cases hmark : b - d ≤ a
    · rw [max_eq_left hmark, min_eq_right (by linarith)]
    · have hmark' : a ≤ b - d := le_of_lt (lt_of_not_ge hmark)
      rw [max_eq_right hmark', min_eq_left (by linarith)]
      ring
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    have hmark : b - d ≤ a := by linarith
    rw [max_eq_left hba, max_eq_left hmark,
      max_eq_left (by linarith : b - a ≤ 0),
      min_eq_right hd]
    ring

/-- Precisely the discount available after replacing the common
marked error t by t/2 while leaving another competing branch at t. -/
theorem marked_half_error_survival (other marked t : ℝ)
    (ht : 0 ≤ t) :
    max (other + t) (marked + t) -
      max (other + t) (marked + t / 2) =
        min (t / 2) (max 0 (marked - other)) := by
  have h := one_branch_discount (other + t) (marked + t)
    (t / 2) (by linarith)
  have h1 : marked + t - t / 2 = marked + t / 2 := by ring
  have h2 : marked + t - (other + t) = marked - other := by ring
  simpa only [h1, h2] using h

/-- Structural obstruction: if an unchanged count branch dominates,
the proved sharper marked moment buys literally no overall power. -/
theorem marked_discount_zero_if_other_dominates
    (other marked t : ℝ) (ht : 0 ≤ t) (hother : marked ≤ other) :
    max (other + t) (marked + t) =
      max (other + t) (marked + t / 2) := by
  have hs := marked_half_error_survival other marked t ht
  have hz : max (0 : ℝ) (marked - other) = 0 :=
    max_eq_left (by linarith)
  rw [hz, min_eq_right (by linarith : (0 : ℝ) ≤ t / 2)] at hs
  linarith only [hs]

/-- Positive savings from the MARKED branch require a strict binding
advantage over every unchanged branch; this is the source-level gate
the next arithmetic proof must discharge on the original OAI masks. -/
theorem marked_discount_pos_iff
    (other marked t : ℝ) (ht : 0 < t) :
    0 < max (other + t) (marked + t) -
       max (other + t) (marked + t / 2) ↔ other < marked := by
  rw [marked_half_error_survival other marked t ht.le]
  constructor
  · intro h
    by_contra hn
    have hle : marked ≤ other := le_of_not_gt hn
    have hz : max (0 : ℝ) (marked - other) = 0 :=
      max_eq_left (by linarith)
    rw [hz, min_eq_right (by linarith : (0 : ℝ) ≤ t / 2)] at h
    exact (lt_irrefl (0 : ℝ)) h
  · intro h
    have hz : max (0 : ℝ) (marked - other) = marked - other :=
      max_eq_right (by linarith)
    rw [hz]
    exact lt_min (by linarith) (by linarith)

#print axioms true_slot_min_le_sixth
#print axioms slot_geometry_cannot_cover_RH_gap
#print axioms original_initial_gap
#print axioms original_signed_low_energy_sqrt_exchange
#print axioms original_signed_low_improvement_exchange
#print axioms original_inverse_energy_nominal_gain
#print axioms physical_slot_tilt_reinvested_gap
#print axioms common_count_loss_half_t
#print axioms one_branch_discount
#print axioms marked_half_error_survival
#print axioms marked_discount_zero_if_other_dominates
#print axioms marked_discount_pos_iff

end RHLean.Analysis.OAIOriginalGainAudit
end
