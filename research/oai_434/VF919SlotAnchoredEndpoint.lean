import «research.oai_434.VF919AnchoredHighAssembly»
import «research.oai_434.VF919SlotCalibratedData»
import «research.oai_434.VF919NativeStrictMertens»

/-!
LOW-first source-calibrated endpoint. See exact-head CI for proof status.
The HIGH contour and exponent reference is the already-proved 7/8 ceiling.
The actual Hecke supremum is NOT redefined. Native moments are supplied
internally at fixed auxiliary Delta. The endpoint saving is slotTilt D.
-/
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Asymptotics
namespace SevenEighths.RHLeanNativeSevenEighthsReplay
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open ProbeFinalAssembly PrincipalSignalComparison RHLeanFiniteSlotGap
open RHLeanFullPhysicalTilt ProbeFinalAssemblyCertifiedBands
open CenteredMomentDetectorPlainMomentParameters

theorem native_fixed_slot_anchored_probe_bounds
    (D : HighData (1/1000000 : ℝ))
    (hfine : ∀ j, D.ell j ≤ detectorMesh (1/1000000) D.t / 200)
    (hepsilon : D.ε ≤ D.t / 2000) (he : D.e ≤ D.t / 2000)
    (heps : ((D.N : ℝ) + 8) * D.eps ≤ D.t) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t)
    (hbetalow : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∀ chi : Character,
      (∀ loss : ℝ, 0 < loss ->
        F.tiltedProbe (slotTilt D) chi =O[atTop]
          (fun Z : ℝ => Z ^ (3/16 - 9*slotTilt D + loss))) ∧
      (fun Z => F.tiltedProbe (slotTilt D) chi Z -
        HeckeSignal.signal (chi.excludePrimes F.S F.exclusions.prime)
          (sourceCorrection chi F.S) (-11/16 - 8*slotTilt D) Z) =O[atTop]
        (fun Z : ℝ => Z ^ ((7/8 : ℝ) - 11/16 - 8*slotTilt D - D.sigma)) := by
  obtain ⟨J, hJ, hmom⟩ := native_uniform_fixed_source_moments D hbetalow
    (by linarith [native_beta_le_seven_eighths]) hfine F counts
  have hsource : ∀ chi : Character, ∃ C : ℝ, 0 < C ∧
      ∀ tau : ℝ, 0 < tau -> tau ≤ 1 ->
      ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts chi Z tau (C*(1+Z^(2*tau))^J) (Z^(2*tau)) := by
    intro chi
    obtain ⟨C, hC, Z0, hZ0, hb⟩ := hmom chi
    refine ⟨C, hC, ?_⟩
    intro tau _ _
    filter_upwards [eventually_ge_atTop Z0] with Z hZ
    exact (nativeSourceMomentBound_iff F counts chi Z tau _ _).mp
      (hb Z hZ tau (Z^(2*tau)) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨tau, htau, htaud, htaucost, htaut, htau2, htaueps, hsource⟩ :=
    chosen_data_height D F counts J hJ hsource
  obtain ⟨hpos, _hslot, _hsmall, htail⟩ := slot_tilt_budget D
  obtain ⟨C, hC, hhigh⟩ := fixed_tilted_high_bound_anchored
    D (slotTilt D) hpos.le htail hepsilon he heps F counts
    tau htau htaud htaucost htaut htau2 htaueps
  intro chi
  refine ⟨fun loss hloss => low_at_slot_tilt F loss hloss chi, ?_⟩
  obtain ⟨Ct, hCt, hhigh⟩ := hhigh chi
  obtain ⟨Cm, hCm, hsource⟩ := hsource chi
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*Cm*(chi.modulus.absNorm : ℝ)^(2*D.eps), by positivity, ?_⟩
  filter_upwards [hhigh, hsource] with Z hh hs
  exact hh Cm hCm.le hs

/-- A source-calibrated endpoint, not an unnamed spectral-gap witness.
The extra sigma condition is discharged by exists_slot_calibrated_data. -/
theorem native_beta_le_slot_calibrated_boundary
    (D : HighData (1/1000000 : ℝ))
    (hfine : ∀ j, D.ell j ≤ detectorMesh (1/1000000) D.t / 200)
    (hepsilon : D.ε ≤ D.t / 2000) (he : D.e ≤ D.t / 2000)
    (heps : ((D.N : ℝ) + 8) * D.eps ≤ D.t)
    (hreserve : slotTilt D ≤ D.sigma) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) :
    HeckeZeroSupremum.beta ≤ 7/8 - slotTilt D := by
  by_contra hn
  have hupper := native_beta_le_seven_eighths
  have hbelow : 7/8 - slotTilt D < HeckeZeroSupremum.beta := lt_of_not_ge hn
  obtain ⟨hdelta, _hslot, hdsmall, _htail⟩ := slot_tilt_budget D
  have hprobes := native_fixed_slot_anchored_probe_bounds D hfine hepsilon he heps F counts
    (by linarith)
  let loss : ℝ := (HeckeZeroSupremum.beta - (7/8 - slotTilt D)) / 2
  have hloss : 0 < loss := by dsimp [loss]; linarith
  have hlosslt : loss < (7/8 : ℝ) - (7/8 - slotTilt D) := by
    dsimp [loss]; linarith
  have hlowline : 7/8 - slotTilt D + loss = HeckeZeroSupremum.beta - loss := by
    dsimp [loss]; ring
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
  have hboundary : max (7/8 - slotTilt D + loss) ((7/8 : ℝ) - D.sigma) < rho.re :=
    max_lt (by rw [hlowline]; exact hnear) (by linarith)
  obtain ⟨hlow, hhigh⟩ := hprobes chi
  apply (HeckeSignal.nonzero_of_probe_bounds_variable_boundary
    chi' (sourceCorrection chi F.S) (F.tiltedProbe (slotTilt D) chi)
    (21/25) (7/8 - slotTilt D) (7/8) loss D.sigma (-11/16 - 8*slotTilt D)
    (by norm_num) (by linarith) (by linarith) (by norm_num)
    hloss hlosslt D.sigma_pos
    (sourceCorrection_analytic_wide chi F.S F.exclusions)
    (sourceCorrection_bound_wide chi F.S F.exclusions)
    ?_ ?_ hboundary hpole') hzero'
  · convert hlow loss hloss using 1; ring_nf
  · convert hhigh using 1; ring_nf

theorem native_beta_le_constructed_slot_tilt :
    ∃ D : HighData (1/1000000 : ℝ),
      0 < slotTilt D ∧ HeckeZeroSupremum.beta ≤ 7/8 - slotTilt D := by
  obtain ⟨D, hfine, hepsilon, he, heps, hsigma⟩ :=
    exists_slot_calibrated_data (1/1000000) (by norm_num)
      (detectorMesh (1/1000000))
      (fun t ht => detectorMesh_pos (by norm_num) ht)
  obtain ⟨F⟩ := exists_source_data D
  obtain ⟨counts⟩ := source_count_parameters F
  have hdelta := (slot_tilt_budget D).1
  exact ⟨D, hdelta, native_beta_le_slot_calibrated_boundary
    D hfine hepsilon he heps (by linarith) F counts⟩

#print axioms native_fixed_slot_anchored_probe_bounds
#print axioms native_beta_le_slot_calibrated_boundary
#check native_beta_le_constructed_slot_tilt
#print axioms native_beta_le_constructed_slot_tilt
end SevenEighths.RHLeanNativeSevenEighthsReplay
end
end OAI

namespace RHLean.Analysis
open MertensExponent OAI.SevenEighths
open RHLeanNativeSevenEighthsReplay RHLeanFullPhysicalTilt

theorem native_mertens_constructed_slot_tilt :
    ∃ D : Parameters.HighData (1/1000000 : ℝ),
      0 < slotTilt D ∧ MertensGrowthAtMost (7/8 - slotTilt D) := by
  obtain ⟨D, hD, hbound⟩ := native_beta_le_constructed_slot_tilt
  exact ⟨D, hD, growthAtMost_mono hbound native_mertens_growth_at_hecke_beta⟩

/-- A strict fixed power envelope after spending half the calibrated gap. -/
theorem native_mertens_slot_fixed_power :
    ∃ D : Parameters.HighData (1/1000000 : ℝ),
      0 < slotTilt D ∧ MertensExponent.MertensPowerBound (7/8-slotTilt D/2) := by
  obtain ⟨D, hD, hgrowth⟩ := native_mertens_constructed_slot_tilt
  refine ⟨D, hD, ?_⟩
  convert hgrowth (slotTilt D/2) (by positivity) using 1; ring

/-- The actual signed pairs retain their exact squarefree diagonal. -/
theorem native_signed_pair_constructed_slot_tilt :
    ∃ D : Parameters.HighData (1/1000000 : ℝ),
      0 < slotTilt D ∧ ∀ eps : ℝ, 0 < eps →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x →
        2*realMertensPositiveLagPairSum (x+1) ≤
          (C*Real.rpow (x:ℝ) (7/8-slotTilt D+eps))^2-realMertensDiagonal (x+1) := by
  obtain ⟨D, hD, hgrowth⟩ := native_mertens_constructed_slot_tilt
  refine ⟨D, hD, ?_⟩
  intro eps heps
  obtain ⟨C, hC, hbound⟩ := hgrowth eps heps
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hsquare : ‖mertensSummatory x‖^2 ≤
      (C*Real.rpow (x:ℝ) (7/8-slotTilt D+eps))^2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg x) _))).mpr (hbound x hx)
  rw [vf919_mertens_sq_eq_signedPair] at hsquare
  linarith only [hsquare]

#print axioms native_mertens_constructed_slot_tilt
#print axioms native_mertens_slot_fixed_power
#print axioms native_signed_pair_constructed_slot_tilt
end RHLean.Analysis
