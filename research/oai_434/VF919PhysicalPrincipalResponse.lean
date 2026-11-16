import «research.oai_434.VF919PrincipalAllDelayReturn»
import «research.oai_434.VF919AnchoredPrincipalRemainder»
import OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized

/-!
# Complete physical principal response

This supplies the principal-row component of accepted claim
20261110-coordinator-2309-EST/FFR4. The actual ray pools, residue weights,
phases, and signed normalizer are unchanged. Every labelled delay is kept,
including evaluations below one. No minimum-slot restriction on the
physical tilt is required. The central rows and both tails are separate
obligations; this module does not establish a new global exponent.
-/

namespace OAI
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter MeasureTheory
namespace SevenEighths.PhysicalPrincipalResponse
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open ProbeRaySlots PrincipalSlotEstimate PrincipalAllDelayReturn
open ActualEisensteinCubic ProbeEuler
local notation "Id" => Ideal HeckeFamily.O

/-- A fixed positive pool prefactor is absorbed by half the slot exponent. -/
theorem eventually_power_lower (c ell : ℝ) (hc : 0 < c) (hell : 0 < ell) :
    ∀ᶠ Z : ℝ in atTop, Z ^ (ell / 2) ≤ c * Z ^ ell := by
  have ht := tendsto_rpow_atTop (show 0 < ell / 2 by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    ht.eventually (eventually_ge_atTop (1 / c))] with Z hZ hlarge
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hone : 1 ≤ c * Z ^ (ell / 2) := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hlarge
  calc
    Z ^ (ell / 2) = 1 * Z ^ (ell / 2) := by ring
    _ ≤ (c * Z ^ (ell / 2)) * Z ^ (ell / 2) :=
      mul_le_mul_of_nonneg_right hone (Real.rpow_nonneg hZ0.le _)
    _ = c * Z ^ ell := by
      rw [mul_assoc, ← Real.rpow_add hZ0]
      congr 2
      ring

/-- The finite return on the genuine arithmetic residue, with all analytic
and character hypotheses supplied by the original excluded source. -/
theorem actual_window_all_delay_error {κ : Type*}
    (E : Finset Id) (hE : SourceExclusions E) (η : Character)
    (W0 W1 : SchwartzMap ℝ ℂ) (S : Finset κ)
    (T : κ → Finset PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ)
    (tilt Y : ℝ) {a Z m : ℝ}
    (ha : 7 / 8 < a) (ha2 : a ≤ 2) (hbeta : HeckeZeroSupremum.beta < a)
    (hZ : 1 ≤ Z) (order : ℕ) (horder : 2 ≤ (7 / 8 : ℝ) * m * (order + 1))
    (hP : 480 ≤ Z ^ m) (hsmall : 1440 * (Z ^ m) ^ (-(7 / 8 : ℝ)) ≤ 1)
    (hW : ∀ j ∈ S, ∀ p ∈ T j, 0 ≤ W j ((Ideal.absNorm p.val : ℝ) / scale j))
    (hnorm : ∀ j ∈ S, ∀ p ∈ T j, Z ^ m ≤ (Ideal.absNorm p.val : ℝ))
    (hcop : ∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus)
    (hmass : ∀ j ∈ S, 0 < slotMass T (residueWeights W scale) j) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    sourceResidueConstant W0 W1 (∏ p ∈ E, p) ≠ 0 →
    let c := -11 / 16 - 8 * tilt
    let f := HeckeSignal.signal (η.excludePrimes E hE.prime) (sourceCorrection η E) c
    let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
      (Probe.principalScalar S Z (1 / 6) (slotMass T (residueWeights W scale)) : ℂ)
    normer ≠ 0 ∧
    ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
        a (Z ^ ((17 / 48 : ℝ) - 24 * tilt)) Y Z (globalClosedCorrection η E)
        (windowMultiplier η S T (fun j t => (W j t : ℂ)) scale) / normer -
      (f Z + PrincipalAllDelayReturn.FiniteResponse.applyTerms f c Z
        (principalProductResponseTerms order S T (residueWeights W scale)
          (fun _ p => Ideal.absNorm p.val)
          (fun _ p => actualAPhase η (primaryGenerator p.val))
          (fun _ p => idealCoeff η p.val)))‖ ≤
      (S.card * (5 : ℝ) ^ S.card * 4 * 2 ^ (order + 1)) *
        HeckeSignal.endpointConstant 2 * Z ^ c := by
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  intro hconstant
  dsimp only
  have hslots : SlotBounds S T (residueWeights W scale)
      (fun _ p => (Ideal.absNorm p.val : ℝ))
      (fun _ p => actualAPhase η (primaryGenerator p.val))
      (fun _ p => idealCoeff η p.val) (Z ^ m) :=
    ⟨hP, hsmall, (fun j hj p hp =>
      mul_nonneg (hW j hj p hp) (Real.rpow_nonneg (by positivity) _)),
      hnorm, (fun _ _ _ _ => actualAPhase_norm_le_one η _),
      (fun j hj p hp => idealCoeff_norm_one_of_coprime η p.val
        p.property.ne_zero (hcop j hj p hp)), hmass⟩
  refine ⟨mul_ne_zero hconstant
    (source_normalizer_ne_zero S T _ (zero_lt_one.trans_le hZ) hmass), ?_⟩
  have herr := normalized_source_all_delay_error W0 W1 (∏ p ∈ E, p)
    (η.excludePrimes E hE.prime) (globalClosedCorrection η E)
    (windowMultiplier η S T (fun j t => (W j t : ℂ)) scale)
    (sourceCorrection_differentiable η E hE) (sourceCorrection_bound η E hE)
    ((17 / 48 : ℝ) - 24 * tilt) Y ha ha2 hbeta hZ order horder S T
    (residueWeights W scale) (fun _ p => (Ideal.absNorm p.val : ℝ))
    (fun _ p => actualAPhase η (primaryGenerator p.val))
    (fun _ p => idealCoeff η p.val) hslots hconstant
    (fun _ => actual_window_residue η S T W scale _)
  have hexp : ((17 / 48 : ℝ) - 24 * tilt) / 3 - 5 / 6 + 1 / 36 =
      -11 / 16 - 8 * tilt := by ring
  dsimp only at herr
  simpa only [hexp, sourceCorrection] using herr

/-- Quantitative control of the complete original principal-row sum minus
its full finite response. The truncation order depends on the fixed slots,
not on Z. In particular, there is no hypothesis relating tilt to ellMin. -/
theorem actual_ray_principal_response (tilt : ℝ) (htilt : 0 ≤ tilt) {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B) (hmin : 0 < ellMin)
    (ell : Fin K → ℝ) (hell : ∀ j, ellMin ≤ ell j) (hdis : Function.Injective ell)
    (hsum : (∑ j, ell j) = 1 / 6)
    (W : Fin K → ℝ → ℝ) (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hcompact : ∀ j, HasCompactSupport (W j))
    (hsupp : ∀ j, Function.support (W j) ⊆ Set.Ioo c d)
    (hWbounds : ∀ j y, 0 ≤ W j y ∧ W j y ≤ B) (hne : ∀ j, W j ≠ 0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hr0 : ∀ y, (W0 y).im = 0) (hr1 : ∀ y, (W1 y).im = 0)
    (hp0 : ∀ y, 0 ≤ (W0 y).re) (hp1 : ∀ y, 0 ≤ (W1 y).re) (hn0 : W0 ≠ 0) (hn1 : W1 ≠ 0)
    (e nu : ℝ) (he : 0 < e) (hehi : e ≤ 1 / 1000) (hnu : 0 < nu)
    (order : ℕ) (horder : 2 ≤ (7 / 8 : ℝ) * (ellMin / 2) * (order + 1)) :
    letI : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let T := fun j => pool (RayQuotient.identityClass M H) S c d (Z ^ (ell j))
      let w := residueWeights W (fun j => Z ^ (ell j))
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ S, p) *
        (Probe.principalScalar Finset.univ Z (1 / 6) (slotMass T w) : ℂ)
      let f := HeckeSignal.signal (η.excludePrimes S hS.prime)
        (sourceCorrection η S) (-11 / 16 - 8 * tilt)
      normer ≠ 0 ∧
      ‖(∑ P : (∀ j, T j), (∏ j, (W j ((Ideal.absNorm (P j).val.val : ℝ) / Z ^ (ell j)) : ℂ)) *
        principalRowIntegral η S (fun j => primaryGenerator (P j).val.val)
          W0 W1 (Z ^ ((17 / 48 : ℝ) - 24 * tilt)) (Z ^ ((23 / 48 : ℝ) + 12 * tilt)) Z) / normer -
        (f Z + PrincipalAllDelayReturn.FiniteResponse.applyTerms f (-11 / 16 - 8 * tilt) Z
          (principalProductResponseTerms order Finset.univ T w
            (fun _ p => Ideal.absNorm p.val)
            (fun _ p => actualAPhase η (primaryGenerator p.val))
            (fun _ p => idealCoeff η p.val)))‖ ≤
      C * (Z ^ ((7 / 8 : ℝ) - 11 / 16 - 8 * tilt - 17 / 48000 + nu) +
        Z ^ (-11 / 16 - 8 * tilt)) := by
  let : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have ha : (7 / 8 : ℝ) < 7 / 8 + e := by linarith
  have ha2 : (7 / 8 : ℝ) + e ≤ 2 := by linarith
  have hbeta : HeckeZeroSupremum.beta < 7 / 8 + e :=
    RHLeanNativeSevenEighthsReplay.native_beta_le_seven_eighths.trans_lt ha
  obtain ⟨C0, hC0, hrem⟩ :=
    ProbePrincipalPhysical.physical_principal_residue_remainder_tilted_anchored
      η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K := K)
  let cs := sourceResidueConstant W0 W1 (∏ p ∈ S, p)
  have hcs : cs ≠ 0 := ProbePrincipalNormalizer.sourceResidueConstant_ne_zero _
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  let D : ℝ := ((K : ℝ) * (5 : ℝ) ^ K * 4 * 2 ^ (order + 1)) *
    HeckeSignal.endpointConstant 2
  let C := C0 / e * ‖cs⁻¹‖ + |D| + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hpos (j : Fin K) : tsupport (W j) ⊆ Set.Ioi 0 := by
    apply subset_trans (closure_minimal
      (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin ell hell,
    power_pool_thresholds (RayQuotient.identityClass M H) S η 1 1 (ellMin / 2)
      (by norm_num) (by norm_num) (by linarith) ell (fun j => by linarith [hell j]),
    eventually_power_lower c ellMin hc hmin,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y => (hWbounds j y).1) hne ell (fun j => hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ => c) (fun _ => d) ell (fun _ => hc) (fun _ => hd) hdis]
      with Z hthreshold haux hlower hmass htuple
  rcases hthreshold with ⟨hZ, _h480, _hsmall, hslot, hpool⟩
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let T := fun j => pool (RayQuotient.identityClass M H) S c d (Z ^ (ell j))
  let normer := cs * (Probe.principalScalar Finset.univ Z (1 / 6)
    (slotMass T (residueWeights W (fun j => Z ^ (ell j)))) : ℂ)
  have hr := actual_window_all_delay_error S hS η W0 W1 Finset.univ T W
    (fun j => Z ^ (ell j)) tilt (Z ^ ((23 / 48 : ℝ) + 12 * tilt))
    ha ha2 hbeta hZ order horder (by simpa using haux.2.1) (by simpa using haux.2.2.1)
    (fun j _ _ _ => (hWbounds j _).1)
    (fun j _ p hp => hlower.trans (hpool j p hp).1)
    (fun j _ p hp => (hpool j p hp).2.1) (fun j _ => hmass.1 j) hcs
  dsimp only at hr ⊢
  refine ⟨hr.1, ?_⟩
  have hraw := hrem tilt htilt ell hsum W hWbounds
    (fun j => Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp => (hpool j p hp).2.2) htuple Z hZ
    (fun j => (hslot j).1) (fun j => (hslot j).2)
  have hinv : ‖normer⁻¹‖ ≤ ‖cs⁻¹‖ * Z ^ nu := by
    dsimp only [normer]
    rw [mul_inv_rev, norm_mul, ← Complex.ofReal_inv, norm_real]
    simpa only [hsum, Real.norm_eq_abs, mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hres := hr.2
  simp only [Finset.card_univ, Fintype.card_fin] at hres
  have hh := ProbePrincipalNormalized.normalized_error _ _ _ normer _ _ _
    (by positivity) hraw hinv hres
  change _ ≤ (C0 / e * Z ^ ((7 / 8 : ℝ) - 11 / 16 - 8 * tilt - 17 / 48000)) *
    (‖cs⁻¹‖ * Z ^ nu) + D * Z ^ (-11 / 16 - 8 * tilt) at hh
  have heq : (C0 / e * Z ^ ((7 / 8 : ℝ) - 11 / 16 - 8 * tilt - 17 / 48000)) *
      (‖cs⁻¹‖ * Z ^ nu) =
      (C0 / e * ‖cs⁻¹‖) * Z ^ ((7 / 8 : ℝ) - 11 / 16 - 8 * tilt - 17 / 48000 + nu) := by
    rw [Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq]
  have h1 : C0 / e * ‖cs⁻¹‖ ≤ C := by dsimp [C]; linarith [abs_nonneg D]
  have h2 : D ≤ C := by
    have hnonneg : 0 ≤ C0 / e * ‖cs⁻¹‖ := by positivity
    dsimp [C]
    linarith [le_abs_self D]
  calc
    _ ≤ C * Z ^ ((7 / 8 : ℝ) - 11 / 16 - 8 * tilt - 17 / 48000 + nu) +
        C * Z ^ (-11 / 16 - 8 * tilt) := by gcongr
    _ = _ := by ring

#print axioms eventually_power_lower
#print axioms actual_window_all_delay_error
#print axioms actual_ray_principal_response
end SevenEighths.PhysicalPrincipalResponse
end
end OAI
