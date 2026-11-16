import «research.oai_434.VF919PhysicalPrincipalResponse»

namespace OAI
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter MeasureTheory
namespace SevenEighths.PhysicalPrincipalResponse
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open ProbeRaySlots PrincipalSlotEstimate PrincipalAllDelayReturn ActualEisensteinCubic ProbeEuler
local notation "Id" => Ideal HeckeFamily.O

#check eventually_power_lower
#check actual_window_all_delay_error
#check actual_ray_principal_response

example (c ell : ℝ) (hc : 0 < c) (hell : 0 < ell) :
    ∀ᶠ Z : ℝ in atTop, Z ^ (ell / 2) ≤ c * Z ^ ell :=
  eventually_power_lower c ell hc hell

example (tilt : ℝ) (htilt : 0 ≤ tilt) {K : ℕ}
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
  exact actual_ray_principal_response tilt htilt M H hH η S hS c d B ellMin hc hd hB hmin
    ell hell hdis hsum W hW hcompact hsupp hWbounds hne W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 e nu he hehi hnu order horder

end SevenEighths.PhysicalPrincipalResponse
end
end OAI

