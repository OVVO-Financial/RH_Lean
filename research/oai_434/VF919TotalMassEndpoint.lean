import «research.oai_434.VF919TotalMassLowPhysical»
import «research.oai_434.VF919ActualSlotMinRetighten»

/-!
# Complete endpoint from the actual total slot mass

The new LOW supplier uses the total mass of the original finite source.
For the existing tilted physical probe its charge is `36 * tilt`, while
the actual total slot mass is `1 / 6`.  The existing physical admissibility
range `tilt < 1 / 960` therefore pays this charge without a minimum-slot
condition.  All probe scales, coefficients, masks, and normalization remain
those of `SourceData.tiltedProbe`.

The unchanged anchored HIGH supplier is used with its full moment source
and its actual tail budget.  On the same exact-minimum calibrated source,
we may set the physical tilt equal to the available HIGH reserve
`sigma = actualSlotMinimum D / 4`.  The resulting complete endpoint is
strictly stronger than the previous same-source minimum-slot endpoint
`7 / 8 - actualSlotMinimum D / 24`.

The native transfer retains the exact zeta-to-Hecke product and all signed
Mertens pair terms.  The fixed power theorem spends half the new saving.
No zero-free region, Mertens estimate, or amplification conclusion is added
as a hypothesis.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Asymptotics

namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual RHLeanFiniteSlotGap

/-- The total-mass LOW estimate for the same actual normalized tilted probe.
The existing physical admissibility range alone pays the aggregate charge. -/
theorem SourceData.tiltedProbe_low_total_mass {Delta : ℝ}
    {D : Parameters.HighData Delta} (F : SourceData D)
    (tilt : ℝ) (htilt : 0 ≤ tilt) (htilt1 : tilt < 1 / 960)
    (loss : ℝ) (hloss : 0 < loss) (eta : Character) :
    F.tiltedProbe tilt eta =O[atTop]
      (fun Z : ℝ => Z ^ (3 / 16 - 9 * tilt + loss)) := by
  let phys := tiltedPhysicalExponents tilt htilt htilt1
  have hbudget :
      (3 / 2 : ℝ) * ((5 / 3 : ℝ) - 2 * (phys.x + phys.y)) ≤
        ∑ j, D.ell j := by
    rw [D.slots_sum]
    dsimp [phys, tiltedPhysicalExponents]
    linarith only [htilt1]
  obtain ⟨C, hC, hb⟩ := original_normalized_compensatedPhysicalProbe_low_total_mass phys
    F.modulus ⊤ le_top F.S F.exclusions F.maximal 1 2 1 loss
    (by norm_num) (by norm_num) hloss D.ell (fun j => (D.slots_bounds j).1)
    D.slots_injective D.slots_sum hbudget
    (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact) (fun _ => F.support)
    (fun _ => F.bounded) (fun _ => F.nonzero) F.W F.W 1 2 1 2
    (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero eta
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨C, hC, hb.mono ?_⟩
  intro Z hZ
  have he : (5 * phys.x + phys.y) / 12 = 3 / 16 - 9 * tilt := by
    dsimp [phys, tiltedPhysicalExponents]
    ring
  have hh := hZ.2
  rw [he] at hh
  simpa only [SourceData.tiltedProbe, normalizedProbe_tilted, phys,
    tiltedPhysicalExponents] using hh

end SevenEighths.ProbeFinalAssembly

namespace SevenEighths.RHLeanNativeSevenEighthsReplay
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open ProbeFinalAssembly PrincipalSignalComparison RHLeanFiniteSlotGap
open RHLeanFullPhysicalTilt ProbeFinalAssemblyCertifiedBands
open CenteredMomentDetectorPlainMomentParameters

/-- Both complete bounds use one fixed actual probe.  The new LOW estimate
is combined with the unchanged anchored HIGH and native moment suppliers. -/
theorem native_fixed_total_mass_probe_bounds
    (D : HighData (1 / 1000000 : ℝ))
    (tilt : ℝ) (htilt : 0 < tilt) (htilt1 : tilt < 1 / 960)
    (htail : 24 * tilt < D.t)
    (hfine : ∀ j, D.ell j ≤ detectorMesh (1 / 1000000) D.t / 200)
    (hepsilon : D.ε ≤ D.t / 2000) (he : D.e ≤ D.t / 2000)
    (heps : ((D.N : ℝ) + 8) * D.eps ≤ D.t) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t)
    (hbetalow : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∀ chi : Character,
      (∀ loss : ℝ, 0 < loss →
        F.tiltedProbe tilt chi =O[atTop]
          (fun Z : ℝ => Z ^ (3 / 16 - 9 * tilt + loss))) ∧
      (fun Z => F.tiltedProbe tilt chi Z -
        HeckeSignal.signal (chi.excludePrimes F.S F.exclusions.prime)
          (sourceCorrection chi F.S) (-11 / 16 - 8 * tilt) Z) =O[atTop]
        (fun Z : ℝ => Z ^ ((7 / 8 : ℝ) - 11 / 16 - 8 * tilt - D.sigma)) := by
  obtain ⟨J, hJ, hmom⟩ := native_uniform_fixed_source_moments D hbetalow
    (by linarith [native_beta_le_seven_eighths]) hfine F counts
  have hsource : ∀ chi : Character, ∃ C : ℝ, 0 < C ∧
      ∀ tau : ℝ, 0 < tau → tau ≤ 1 →
      ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts chi Z tau
          (C * (1 + Z ^ (2 * tau)) ^ J) (Z ^ (2 * tau)) := by
    intro chi
    obtain ⟨C, hC, Z0, hZ0, hb⟩ := hmom chi
    refine ⟨C, hC, ?_⟩
    intro tau _ _
    filter_upwards [eventually_ge_atTop Z0] with Z hZ
    exact (nativeSourceMomentBound_iff F counts chi Z tau _ _).mp
      (hb Z hZ tau (Z ^ (2 * tau)) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨tau, htau, htaud, htaucost, htaut, htau2, htaueps, hsource⟩ :=
    chosen_data_height D F counts J hJ hsource
  obtain ⟨C, hC, hhigh⟩ := fixed_tilted_high_bound_anchored
    D tilt htilt.le htail hepsilon he heps F counts
    tau htau htaud htaucost htaut htau2 htaueps
  intro chi
  refine ⟨fun loss hloss =>
    F.tiltedProbe_low_total_mass tilt htilt.le htilt1 loss hloss chi, ?_⟩
  obtain ⟨Ct, hCt, hhigh⟩ := hhigh chi
  obtain ⟨Cm, hCm, hsource⟩ := hsource chi
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct + C * Cm * (chi.modulus.absNorm : ℝ) ^ (2 * D.eps), by positivity, ?_⟩
  filter_upwards [hhigh, hsource] with Z hh hs
  exact hh Cm hCm.le hs

/-- A physical tilt paid by total slot mass realizes its full gain whenever
the unchanged anchored HIGH reserve covers it. -/
theorem native_beta_le_total_mass_boundary
    (D : HighData (1 / 1000000 : ℝ))
    (tilt : ℝ) (htilt : 0 < tilt) (htilt1 : tilt < 1 / 960)
    (htail : 24 * tilt < D.t)
    (hfine : ∀ j, D.ell j ≤ detectorMesh (1 / 1000000) D.t / 200)
    (hepsilon : D.ε ≤ D.t / 2000) (he : D.e ≤ D.t / 2000)
    (heps : ((D.N : ℝ) + 8) * D.eps ≤ D.t)
    (hreserve : tilt ≤ D.sigma) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) :
    HeckeZeroSupremum.beta ≤ 7 / 8 - tilt := by
  by_contra hn
  have hupper := native_beta_le_seven_eighths
  have hbelow : 7 / 8 - tilt < HeckeZeroSupremum.beta := lt_of_not_ge hn
  have hprobes := native_fixed_total_mass_probe_bounds
    D tilt htilt htilt1 htail hfine hepsilon he heps F counts (by linarith)
  let loss : ℝ := (HeckeZeroSupremum.beta - (7 / 8 - tilt)) / 2
  have hloss : 0 < loss := by dsimp [loss]; linarith
  have hlosslt : loss < (7 / 8 : ℝ) - (7 / 8 - tilt) := by
    dsimp [loss]
    linarith
  have hlowline : 7 / 8 - tilt + loss = HeckeZeroSupremum.beta - loss := by
    dsimp [loss]
    ring
  obtain ⟨chi, rho, _hprimitive, hhalf, _hstrip, hpole, hzero, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hloss (by linarith)
  let chi' := chi.excludePrimes F.S F.exclusions.prime
  have hmask := excludePrimes_mask chi F.S F.exclusions.prime
  have hpole' : rho ≠ 1 ∨ chi'.residue ≠ 1 := by
    rcases hpole with h1 | hchi
    · exact Or.inl h1
    · exact Or.inr
        (fun hc => hchi ((HeckeFiniteDeletion.principal_iff_of_mask chi' chi hmask).mp hc))
  have hzero' : LFunction chi' rho = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole chi' chi hmask
      (by linarith) hpole', hzero, zero_mul]
  have hboundary :
      max (7 / 8 - tilt + loss) ((7 / 8 : ℝ) - D.sigma) < rho.re :=
    max_lt (by rw [hlowline]; exact hnear) (by linarith)
  obtain ⟨hlow, hhigh⟩ := hprobes chi
  apply (HeckeSignal.nonzero_of_probe_bounds_variable_boundary
    chi' (sourceCorrection chi F.S) (F.tiltedProbe tilt chi)
    (21 / 25) (7 / 8 - tilt) (7 / 8) loss D.sigma (-11 / 16 - 8 * tilt)
    (by norm_num) (by linarith) (by linarith) (by norm_num)
    hloss hlosslt D.sigma_pos
    (sourceCorrection_analytic_wide chi F.S F.exclusions)
    (sourceCorrection_bound_wide chi F.S F.exclusions)
    ?_ ?_ hboundary hpole') hzero'
  · convert hlow loss hloss using 1 <;> ring_nf
  · convert hhigh using 1 <;> ring_nf

end SevenEighths.RHLeanNativeSevenEighthsReplay

namespace SevenEighths.RHLeanActualSlotMin
open Parameters RHLeanFullPhysicalTilt RHLeanNativeSevenEighthsReplay
open ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands

/-- The same already-certified source calibration supplies exactly one
quarter of the actual selected-slot minimum as its HIGH reserve. -/
theorem recalibrated_sigma_eq_true_minimum_quarter {Delta : ℝ}
    (D : HighData Delta) :
    (slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)).sigma =
      actualSlotMinimum D / 4 := by
  rw [(slotCalibratedHighDataLowFirst_reserves
    (sourceWithExactSlotMinimum D)).2.2.2,
    recalibrated_tilt_eq_true_minimum D]
  ring

/-- The new tilt uses the same physical slot family and its original total
mass; no source scale or slot length is rescaled by the calibration. -/
theorem total_mass_calibration_preserves_physical_geometry {Delta : ℝ}
    (D : HighData Delta) :
    let E := slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)
    E.t = D.t ∧ E.N = D.N ∧ E.ell = D.ell := by
  exact ⟨rfl, rfl, rfl⟩

/-- Taking the full calibrated HIGH reserve as tilt remains inside both
the original physical range and the unchanged anchored HIGH tail budget. -/
theorem recalibrated_total_mass_tilt_budget {Delta : ℝ}
    (D : HighData Delta) :
    let E := slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)
    0 < E.sigma ∧ E.sigma < 1 / 960 ∧ 24 * E.sigma < E.t := by
  let E := slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)
  change 0 < E.sigma ∧ E.sigma < 1 / 960 ∧ 24 * E.sigma < E.t
  have hmT : actualSlotMinimum D ≤ D.t / 200 := by
    have h := (D.slots_bounds (leastSlotIndex D)).2.2
    change D.ell (leastSlotIndex D) ≤ D.t / 200
    linarith only [h]
  have ht : E.t = D.t := rfl
  have hsigma : E.sigma = actualSlotMinimum D / 4 :=
    recalibrated_sigma_eq_true_minimum_quarter D
  refine ⟨E.sigma_pos, ?_, ?_⟩
  · rw [hsigma]
    linarith only [hmT, D.t_small]
  · rw [hsigma, ht]
    linarith only [hmT, D.t_pos]

/-- Numerical comparison on one and the same original physical source. -/
theorem total_mass_boundary_strictly_improves_low_first {Delta : ℝ}
    (D : HighData Delta) :
    (7 / 8 : ℝ) - actualSlotMinimum D / 4 <
      7 / 8 - slotTiltLowFirst
        (slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)) := by
  rw [recalibrated_tilt_eq_true_minimum D]
  linarith only [actualSlotMinimum_pos D]

/-- Even after spending half the new saving, the fixed power exponent is
strictly smaller than the previous same-source growth endpoint. -/
theorem total_mass_fixed_power_strictly_improves_low_first {Delta : ℝ}
    (D : HighData Delta) :
    (7 / 8 : ℝ) - actualSlotMinimum D / 8 <
      7 / 8 - slotTiltLowFirst
        (slotCalibratedHighDataLowFirst (sourceWithExactSlotMinimum D)) := by
  rw [recalibrated_tilt_eq_true_minimum D]
  linarith only [actualSlotMinimum_pos D]

/-- Complete LOW/HIGH/moment endpoint for any licensed original fine source.
The actual minimum is taken before calibration, characters, and losses. -/
theorem native_beta_le_true_physical_slot_minimum_total_mass_of_fine
    (D : HighData (1 / 1000000 : ℝ))
    (hfine : ∀ i, D.ell i ≤ detectorMesh (1 / 1000000) D.t / 200) :
    HeckeZeroSupremum.beta ≤ 7 / 8 - actualSlotMinimum D / 4 := by
  let Dstar := sourceWithExactSlotMinimum D
  let E := slotCalibratedHighDataLowFirst Dstar
  have hfineE : ∀ i, E.ell i ≤ detectorMesh (1 / 1000000) E.t / 200 := by
    exact hfine
  have hreserves := slotCalibratedHighDataLowFirst_reserves Dstar
  change E.ε ≤ E.t / 2000 ∧ E.e ≤ E.t / 2000 ∧
    ((E.N : ℝ) + 8) * E.eps ≤ E.t ∧
    E.sigma = 6 * slotTiltLowFirst E at hreserves
  obtain ⟨hepsilon, he, heps, _hsigma⟩ := hreserves
  have hbudget := recalibrated_total_mass_tilt_budget D
  change 0 < E.sigma ∧ E.sigma < 1 / 960 ∧ 24 * E.sigma < E.t at hbudget
  obtain ⟨htilt, htilt1, htail⟩ := hbudget
  obtain ⟨F⟩ := exists_source_data E
  obtain ⟨counts⟩ := source_count_parameters F
  have hbound := native_beta_le_total_mass_boundary
    E E.sigma htilt htilt1 htail hfineE hepsilon he heps le_rfl F counts
  have hsigma : E.sigma = actualSlotMinimum D / 4 :=
    recalibrated_sigma_eq_true_minimum_quarter D
  rwa [hsigma] at hbound

/-- One fixed original physical source supplies the full positive saving. -/
theorem native_beta_le_true_physical_slot_minimum_total_mass :
    ∃ D : HighData (1 / 1000000 : ℝ),
      0 < actualSlotMinimum D ∧
      HeckeZeroSupremum.beta ≤ 7 / 8 - actualSlotMinimum D / 4 := by
  obtain ⟨D, hfine⟩ :=
    Parameters.exists_high_data_fine (1 / 1000000) (by norm_num)
      (detectorMesh (1 / 1000000))
      (fun t ht => detectorMesh_pos (by norm_num) ht)
  exact ⟨D, actualSlotMinimum_pos D,
    native_beta_le_true_physical_slot_minimum_total_mass_of_fine D hfine⟩

#print axioms recalibrated_sigma_eq_true_minimum_quarter
#print axioms total_mass_calibration_preserves_physical_geometry
#print axioms recalibrated_total_mass_tilt_budget
#print axioms native_beta_le_true_physical_slot_minimum_total_mass

end SevenEighths.RHLeanActualSlotMin
end
end OAI

namespace RHLean.Analysis
open MertensExponent OAI.SevenEighths
open RHLeanActualSlotMin RHLeanNativeSevenEighthsReplay

/-- The exact native transfer supplies every positive-loss Mertens bound
at the improved same-source endpoint. -/
theorem native_mertens_true_physical_slot_minimum_total_mass :
    ∃ D : Parameters.HighData (1 / 1000000 : ℝ),
      0 < actualSlotMinimum D ∧
      MertensGrowthAtMost (7 / 8 - actualSlotMinimum D / 4) := by
  obtain ⟨D, hD, hbeta⟩ := native_beta_le_true_physical_slot_minimum_total_mass
  exact ⟨D, hD, growthAtMost_mono hbeta native_mertens_growth_at_hecke_beta⟩

/-- Spend half the actual saving to obtain a single fixed power envelope. -/
theorem native_mertens_fixed_true_physical_slot_minimum_total_mass :
    ∃ D : Parameters.HighData (1 / 1000000 : ℝ),
      0 < actualSlotMinimum D ∧
      MertensPowerBound (7 / 8 - actualSlotMinimum D / 8) := by
  obtain ⟨D, hD, hgrowth⟩ := native_mertens_true_physical_slot_minimum_total_mass
  refine ⟨D, hD, ?_⟩
  convert hgrowth (actualSlotMinimum D / 8) (by positivity) using 1 <;> ring

/-- Complete integer-by-integer signed return, retaining every lag pair
and the actual squarefree diagonal. -/
theorem native_signed_pair_true_physical_slot_minimum_total_mass :
    ∃ D : Parameters.HighData (1 / 1000000 : ℝ),
      0 < actualSlotMinimum D ∧ ∀ eps : ℝ, 0 < eps →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x →
        2 * realMertensPositiveLagPairSum (x + 1) ≤
          (C * Real.rpow (x : ℝ)
            (7 / 8 - actualSlotMinimum D / 4 + eps)) ^ 2 -
            realMertensDiagonal (x + 1) := by
  obtain ⟨D, hD, hgrowth⟩ := native_mertens_true_physical_slot_minimum_total_mass
  refine ⟨D, hD, ?_⟩
  intro eps heps
  obtain ⟨C, hC, hbound⟩ := hgrowth eps heps
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hsquare : ‖mertensSummatory x‖ ^ 2 ≤
      (C * Real.rpow (x : ℝ)
        (7 / 8 - actualSlotMinimum D / 4 + eps)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg x) _))).mpr
      (hbound x hx)
  rw [vf919_mertens_sq_eq_signedPair] at hsquare
  linarith only [hsquare]

#print axioms native_mertens_true_physical_slot_minimum_total_mass
#print axioms native_mertens_fixed_true_physical_slot_minimum_total_mass
#print axioms native_signed_pair_true_physical_slot_minimum_total_mass
end RHLean.Analysis
