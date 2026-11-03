import «research.oai_434.VF919LowFirstSlotAnchoredEndpoint»

/-!
# Recover the exact minimum of the original finite slot population

The original physical slot constructor sets
  rmin = (minimum slot length) / (2 * (7/8)).
The LOW-first source gate only uses (7/8)*rmin.  This module replaces the
conservative *parameter* by the true minimum.  No physical slot, Hecke atom,
coefficient, character mask, smooth cutoff, or normalization is changed.

The complete compensated LOW/HIGH suppliers and their original moment
dependencies remain the ones checked in the existing anchored endpoint.
This is a source-geometric gain, NOT a new NNS signed-moment theorem.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.RHLeanActualSlotMin
open Parameters RHLeanFullPhysicalTilt
open RHLeanNativeSevenEighthsReplay
open ProbeFinalAssembly

private theorem slotUniverse_nonempty {Delta : ℝ} (D : HighData Delta) :
    (Finset.univ : Finset (Fin D.N)).Nonempty := by
  exact ⟨⟨0, D.slots_pos⟩, Finset.mem_univ _⟩

/-- A minimum index for the ACTUAL, finite, positive source slot family. -/
noncomputable def leastSlotIndex {Delta : ℝ} (D : HighData Delta) : Fin D.N :=
  Classical.choose
    (Finset.exists_min_image (Finset.univ : Finset (Fin D.N))
      D.ell (slotUniverse_nonempty D))

theorem leastSlotIndex_le {Delta : ℝ} (D : HighData Delta)
    (i : Fin D.N) : D.ell (leastSlotIndex D) ≤ D.ell i := by
  exact (Classical.choose_spec
    (Finset.exists_min_image (Finset.univ : Finset (Fin D.N))
      D.ell (slotUniverse_nonempty D))).2.2 i (Finset.mem_univ i)

noncomputable def actualSlotMinimum {Delta : ℝ} (D : HighData Delta) : ℝ :=
  D.ell (leastSlotIndex D)

theorem actualSlotMinimum_pos {Delta : ℝ} (D : HighData Delta) :
    0 < actualSlotMinimum D := (D.slots_bounds (leastSlotIndex D)).1

theorem original_slot_floor_le_actual {Delta : ℝ} (D : HighData Delta) :
    (7/8 : ℝ) * D.rmin ≤ actualSlotMinimum D :=
  (D.slots_bounds (leastSlotIndex D)).2.1

/-- Calibrate rmin to the true source minimum, not an arbitrary lower bound. -/
noncomputable def trueMinimumRmin {Delta : ℝ} (D : HighData Delta) : ℝ :=
  actualSlotMinimum D / (7/8 : ℝ)

theorem trueMinimumRmin_pos {Delta : ℝ} (D : HighData Delta) :
    0 < trueMinimumRmin D :=
  div_pos (actualSlotMinimum_pos D) (by norm_num)

theorem trueMinimumRmin_ge {Delta : ℝ} (D : HighData Delta) :
    D.rmin ≤ trueMinimumRmin D := by
  unfold trueMinimumRmin
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 7/8)).mpr
  nlinarith only [original_slot_floor_le_actual D]

theorem trueMinimumRmin_exact {Delta : ℝ} (D : HighData Delta) :
    (7/8 : ℝ) * trueMinimumRmin D = actualSlotMinimum D := by
  unfold trueMinimumRmin
  field_simp
  ring

/-- Change only the scale certificate rmin.  In particular all original
coefficients, selected slots, source scales, and analytic error allowances
are definitional equalities; every HighData inequality is rechecked. -/
noncomputable def sourceWithExactSlotMinimum {Delta : ℝ} (D : HighData Delta) :
    HighData Delta := by
  let m := trueMinimumRmin D
  have hm : D.rmin ≤ m := trueMinimumRmin_ge D
  have hexact : (7/8 : ℝ) * m = actualSlotMinimum D :=
    trueMinimumRmin_exact D
  refine { D with
    rmin := m
    slots_bounds := ?_
    rmin_pos := ?_
    epsilon_gap := ?_
    window_budget := ?_ }
  · intro i
    refine ⟨(D.slots_bounds i).1, ?_, (D.slots_bounds i).2.2⟩
    change (7/8 : ℝ) * m ≤ D.ell i
    rw [hexact]
    exact leastSlotIndex_le D i
  · exact trueMinimumRmin_pos D
  · exact lt_of_lt_of_le D.epsilon_gap
      (mul_le_mul_of_nonneg_right hm D.t_pos.le)
  · have hs : (7/8 : ℝ) * ((7/8 : ℝ) * D.rmin) ≤
        (7/8 : ℝ) * ((7/8 : ℝ) * m) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hm (by norm_num)) (by norm_num)
    exact D.window_budget.trans hs

theorem sourceWithExactSlotMinimum_physical_geometry {Delta : ℝ}
    (D : HighData Delta) :
    (sourceWithExactSlotMinimum D).t = D.t ∧
    (sourceWithExactSlotMinimum D).N = D.N ∧
    (sourceWithExactSlotMinimum D).ell = D.ell ∧
    (sourceWithExactSlotMinimum D).rmin = trueMinimumRmin D := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The exact minimum never gives a weaker bound than the old rmin gate. -/
theorem actualSlotMinimum_tilt_ge_old {Delta : ℝ} (D : HighData Delta) :
    slotTiltLowFirst D ≤ actualSlotMinimum D / 24 := by
  unfold slotTiltLowFirst
  have h := original_slot_floor_le_actual D
  linarith only [h]

/-- If the source has unused slot slack, its physical tilt improves strictly. -/
theorem actualSlotMinimum_tilt_gt_old_of_slack {Delta : ℝ}
    (D : HighData Delta)
    (hslack : (7/8 : ℝ) * D.rmin < actualSlotMinimum D) :
    slotTiltLowFirst D < actualSlotMinimum D / 24 := by
  unfold slotTiltLowFirst
  linarith only [hslack]

/-- Maximum possible tilt allowed by the existing complete reflected
finite-slot gate, using the ACTUAL minimum of all selected source slots. -/
theorem actual_minimum_gate_maximal {Delta : ℝ} (D : HighData Delta)
    (tilt : ℝ) (hgate : ∀ i : Fin D.N, 24 * tilt ≤ D.ell i) :
    tilt ≤ actualSlotMinimum D / 24 := by
  have h := hgate (leastSlotIndex D)
  change 24 * tilt ≤ actualSlotMinimum D at h
  linarith only [h]

/-- Recalibration preserves the source and raises the LOW-first gate
exactly to (true minimum)/24.  The HIGH allowance is recalibrated by the
existing proved six-to-one supplier. -/
theorem recalibrated_tilt_eq_true_minimum {Delta : ℝ}
    (D : HighData Delta) :
    slotTiltLowFirst
      (slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)) =
      actualSlotMinimum D / 24 := by
  change ((7/8 : ℝ) *
    (slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)).rmin) / 24 =
      actualSlotMinimum D / 24
  rw [(slotCalibratedHighDataLowFirst_geometry
    (sourceWithExactSlotMinimum D)).2.2.1]
  change ((7/8 : ℝ) * trueMinimumRmin D) / 24 =
    actualSlotMinimum D / 24
  rw [trueMinimumRmin_exact D]

/-- Genuine end-to-end endpoint: source records are fixed before characters
and zeros; all LOW/HIGH/moment suppliers are the existing complete proved
analytic lemmas.  The saved exponent is the actual selected-slot minimum. -/
theorem native_beta_le_true_physical_slot_minimum :
    ∃ D : HighData (1/1000000 : ℝ),
      0 < actualSlotMinimum D ∧
      HeckeZeroSupremum.beta ≤ 7/8 - actualSlotMinimum D / 24 := by
  obtain ⟨D, hfine⟩ :=
    Parameters.exists_high_data_fine (1/1000000) (by norm_num)
      (detectorMesh (1/1000000))
      (fun t ht => detectorMesh_pos (by norm_num) ht)
  let Dstar := sourceWithExactSlotMinimum D
  let E := slotCalibratedHighDataLowFirst Dstar
  have hfineE : ∀ i, E.ell i ≤
      detectorMesh (1/1000000) E.t / 200 := by
    exact hfine
  have hreserves := slotCalibratedHighDataLowFirst_reserves Dstar
  change E.ε ≤ E.t / 2000 ∧ E.e ≤ E.t / 2000 ∧
    ((E.N : ℝ) + 8) * E.eps ≤ E.t ∧
    E.sigma = 6 * slotTiltLowFirst E at hreserves
  obtain ⟨hepsilon, he, heps, hsigma⟩ := hreserves
  have htpos : 0 < slotTiltLowFirst E := (slot_tilt_budget_low_first E).1
  have hreserve : slotTiltLowFirst E ≤ E.sigma := by
    linarith only [hsigma, htpos]
  obtain ⟨F⟩ := exists_source_data E
  obtain ⟨counts⟩ := source_count_parameters F
  have hbound := native_beta_le_slot_calibrated_boundary_low_first
    E hfineE hepsilon he heps hreserve F counts
  change HeckeZeroSupremum.beta ≤ 7/8 -
    slotTiltLowFirst (slotCalibratedHighDataLowFirst
      (sourceWithExactSlotMinimum D)) at hbound
  rw [recalibrated_tilt_eq_true_minimum D] at hbound
  exact ⟨D, actualSlotMinimum_pos D, hbound⟩

#print axioms sourceWithExactSlotMinimum
#print axioms recalibrated_tilt_eq_true_minimum
#print axioms native_beta_le_true_physical_slot_minimum

end SevenEighths.RHLeanActualSlotMin
end OAI

namespace RHLean.Analysis
open MertensExponent OAI.SevenEighths
open RHLeanActualSlotMin RHLeanNativeSevenEighthsReplay

/-- The proven exact-minimum LOW gain reaches every actual Möbius prefix. -/
theorem native_mertens_true_physical_slot_minimum :
    ∃ D : Parameters.HighData (1/1000000 : ℝ),
      0 < actualSlotMinimum D ∧
      MertensGrowthAtMost (7/8 - actualSlotMinimum D / 24) := by
  obtain ⟨D, hD, hbeta⟩ := native_beta_le_true_physical_slot_minimum
  exact ⟨D, hD, growthAtMost_mono hbeta native_mertens_growth_at_hecke_beta⟩

/-- Complete integer-by-integer signed-pair return with its actual diagonal. -/
theorem native_signed_pair_true_physical_slot_minimum :
    ∃ D : Parameters.HighData (1/1000000 : ℝ),
      0 < actualSlotMinimum D ∧ ∀ eps : ℝ, 0 < eps →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x →
        2 * realMertensPositiveLagPairSum (x+1) ≤
          (C * Real.rpow (x:ℝ)
            (7/8 - actualSlotMinimum D / 24 + eps))^2 -
            realMertensDiagonal (x+1) := by
  obtain ⟨D, hD, hgrowth⟩ := native_mertens_true_physical_slot_minimum
  refine ⟨D, hD, ?_⟩
  intro eps heps
  obtain ⟨C, hC, hbound⟩ := hgrowth eps heps
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hsquare : ‖mertensSummatory x‖^2 ≤
      (C * Real.rpow (x:ℝ)
        (7/8 - actualSlotMinimum D / 24 + eps))^2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg x) _))).mpr
      (hbound x hx)
  rw [vf919_mertens_sq_eq_signedPair] at hsquare
  linarith only [hsquare]

#print axioms native_mertens_true_physical_slot_minimum
#print axioms native_signed_pair_true_physical_slot_minimum
end RHLean.Analysis
