import «research.oai_434.VF919TiltedLowPhysical»

/-!
# Reflected LOW energy from the total slot mass

The two source calls below use the same marked completed rows.  Their physical
exponents enter only the upper row cap and the resulting energy bound; the
actual row, its scale, coefficients, masks, and period remain unchanged.

If the selected mass pays the original reflected gate, use the actual physical
exponents.  Otherwise use the fixed source with sum 5/6.  The total-mass budget
pays for enlarging that row cap, leaving the common energy exponent S - d.
The downstream inverse normalization still uses the original physical scale.

This file is a proof candidate until the authorized remote Lean audit succeeds.
-/

namespace OAI
noncomputable section
open scoped Classical ContDiff SchwartzMap BigOperators
open Filter MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- The original physical geometry, used only as an auxiliary reflected cap. -/
def totalMassAuxiliaryPhysicalExponents : LowPhysicalExponents where
  x := 17/48
  y := 23/48
  sum_lo := by norm_num
  sum_hi := by norm_num
  x_gt_slot := by norm_num
  x_lt_y := by norm_num
  gram_gap := by norm_num
  y_le_one := by norm_num

theorem low_selected_nominal_energy_total_mass
    (phys : LowPhysicalExponents) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (hsum : ∑ i, ell i ≤ 1/6)
    (hbudget : (3/2 : ℝ) * ((5/3 : ℝ) - 2*(phys.x+phys.y)) ≤ ∑ i, ell i)
    (Ck b ε : ℝ) (hCk : 0 < Ck) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧
      ∀ (T : Fin K → Finset PrimeIdeal),
        (∀ i P, P ∈ T i → Supported P.val) →
        (∀ i P, P ∈ T i → P.val ∉ S) →
        Pairwise (fun i j => Disjoint (T i) (T j)) →
        (∀ i P, P ∈ T i → (Ideal.absNorm P.val : ℝ) ≤ b*Z^(ell i)) →
      ∀ (J : Finset (Fin K)) (R : Finset O),
        (∀ z ∈ R, z ≠ 0 ∧
          elementNorm z ≤ Ck*Z^((phys.x+phys.y)-2*lowUnselectedLength ell J)) →
      ∀ X : ℝ, 0 < X →
        Z^(1+lowSelectedLength ell J-ε/2) ≤ X →
        X ≤ Z^(1+lowSelectedLength ell J+ε/2) →
      ∀ (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (Y : Fin K → ℝ) (t : ℝ) (σ : RayRing),
        (∑ z ∈ R, ‖lowSelectedInverseRow Finset.univ
          (lowSelectedWeight η (fun i => canonicalSlotSupport (T i)) J W Y t)
          η S hS (lowSelectedIdeal (fun i => canonicalSlotSupport (T i)) J)
          X t σ z‖^2) ≤
          C*(1+‖t‖)^degree*
            Z^((phys.x+phys.y)-lowUnselectedLength ell J+507*ε) := by
  obtain ⟨degree₁, C₁, Z₁, hC₁, _hZ₁, he₁⟩ :=
    low_selected_physical_energy_tilted phys η S hS hbad K Ck ε hCk hε hε1
  obtain ⟨degree₂, C₂, Z₂, hC₂, _hZ₂, he₂⟩ :=
    low_selected_physical_energy_tilted totalMassAuxiliaryPhysicalExponents
      η S hS hbad K Ck ε hCk hε hε1
  refine ⟨max degree₁ degree₂, C₁+C₂, add_pos hC₁ hC₂, ?_⟩
  filter_upwards [eventually_low_selected_caps ell hell b ε hε,
    Filter.eventually_ge_atTop Z₁, Filter.eventually_ge_atTop Z₂] with Z hc hZ₁ hZ₂
  refine ⟨hc.1, ?_⟩
  intro T hT hout hdis hnorm J R hR X hX hXlo hXhi W hW Y t σ
  obtain ⟨hd, hd1, hs, hscap⟩ := lowLength_bounds ell hell hsum J
  have hlength := lowLength_sum ell J
  have hscale := lowCentralShift_scale Z X (lowSelectedLength ell J+ε/2) hc.1 hX
  have hshift := lowCentralShift_bound Z X (lowSelectedLength ell J) ε
    hc.1 hX hε.le hXlo hXhi
  have hheight : 1 ≤ 1+‖t‖ := le_add_of_nonneg_right (norm_nonneg t)
  have hpower₁ : (1+‖t‖)^degree₁ ≤ (1+‖t‖)^(max degree₁ degree₂) :=
    pow_le_pow_right₀ hheight (le_max_left _ _)
  have hpower₂ : (1+‖t‖)^degree₂ ≤ (1+‖t‖)^(max degree₁ degree₂) :=
    pow_le_pow_right₀ hheight (le_max_right _ _)
  have hcoefficient₁ : C₁*(1+‖t‖)^degree₁ ≤
      (C₁+C₂)*(1+‖t‖)^(max degree₁ degree₂) :=
    mul_le_mul (le_add_of_nonneg_right hC₂.le) hpower₁
      (by positivity) (add_pos hC₁ hC₂).le
  have hcoefficient₂ : C₂*(1+‖t‖)^degree₂ ≤
      (C₁+C₂)*(1+‖t‖)^(max degree₁ degree₂) :=
    mul_le_mul (le_add_of_nonneg_left hC₁.le) hpower₂
      (by positivity) (add_pos hC₁ hC₂).le
  rw [←hscale]
  by_cases hgate : (5/3 : ℝ)-2*(phys.x+phys.y) ≤ lowSelectedLength ell J
  · have hb := he₁ Z (lowUnselectedLength ell J) (lowSelectedLength ell J+ε/2)
      (lowCentralShift Z X (lowSelectedLength ell J+ε/2)) hZ₁ hd hd1
      (by linarith) (by linarith) hshift
      R hR T hT hout hdis J (fun i => max 1 (b*Z^(ell i.val)))
      (Or.inr (by linarith))
      (fun i => le_max_left _ _)
      (fun i P hP => (hnorm i.val P hP).trans (le_max_right _ _))
      (hc.2 J) W hW Y t σ
    apply hb.trans
    exact mul_le_mul hcoefficient₁
      (Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith only [hd]))
      (Real.rpow_nonneg (lt_trans zero_lt_one hc.1).le _) (by positivity)
  · have haux : totalMassAuxiliaryPhysicalExponents.x+
        totalMassAuxiliaryPhysicalExponents.y = (5/6 : ℝ) := by
      norm_num [totalMassAuxiliaryPhysicalExponents]
    have hcap : phys.x+phys.y ≤ totalMassAuxiliaryPhysicalExponents.x+
        totalMassAuxiliaryPhysicalExponents.y := by
      rw [haux]
      exact phys.sum_hi
    have hRaux : ∀ z ∈ R, z ≠ 0 ∧
        elementNorm z ≤ Ck*Z^((totalMassAuxiliaryPhysicalExponents.x+
          totalMassAuxiliaryPhysicalExponents.y)-2*lowUnselectedLength ell J) := by
      intro z hz
      refine ⟨(hR z hz).1, (hR z hz).2.trans ?_⟩
      apply mul_le_mul_of_nonneg_left _ hCk.le
      exact Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith only [hcap])
    have hauxgate : IsEmpty (SelectedSlot J) ∨
        (5/3 : ℝ)-2*(totalMassAuxiliaryPhysicalExponents.x+
          totalMassAuxiliaryPhysicalExponents.y) ≤ lowSelectedLength ell J+ε/2 := by
      apply Or.inr
      rw [haux]
      linarith only [hs, hε]
    have hpayment : (totalMassAuxiliaryPhysicalExponents.x+
        totalMassAuxiliaryPhysicalExponents.y)-2*lowUnselectedLength ell J+507*ε ≤
        (phys.x+phys.y)-lowUnselectedLength ell J+507*ε := by
      rw [haux]
      have hbadgate := lt_of_not_ge hgate
      linarith only [hbudget, hlength, hbadgate]
    have hb := he₂ Z (lowUnselectedLength ell J) (lowSelectedLength ell J+ε/2)
      (lowCentralShift Z X (lowSelectedLength ell J+ε/2)) hZ₂ hd hd1
      (by linarith) (by linarith) hshift
      R hRaux T hT hout hdis J (fun i => max 1 (b*Z^(ell i.val))) hauxgate
      (fun i => le_max_left _ _)
      (fun i P hP => (hnorm i.val P hP).trans (le_max_right _ _))
      (hc.2 J) W hW Y t σ
    apply hb.trans
    exact mul_le_mul hcoefficient₂
      (Real.rpow_le_rpow_of_exponent_le hc.1.le hpayment)
      (Real.rpow_nonneg (lt_trans zero_lt_one hc.1).le _) (by positivity)

#print axioms low_selected_nominal_energy_total_mass

end SevenEighths.ProbePhysical
end
end OAI
