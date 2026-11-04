import «research.VF_919_RESONANT_FIBER_NNS_RECOMBINATION_20261022»
import OAI.NumberTheory.DirichletL.Detector.LowSlotPolynomial
import OAI.NumberTheory.DirichletL.Detector.LowCentralTuple

/-!
# Original OAI LOW physical tuple Gram, before the first triangle inequality

This module is NOT an assumed owner bound. It specializes the existing
kernel-proved RH_Lean NNS Gram polarization to the LITERAL complex
unselected-tuple source in OAI's pinned LowSlotPolynomial.lean.

OAI LowTupleGram.compensation_tuple_actual_gram currently uses
  compensation_tuple_low_polynomial; norm_sum_le
and irreversibly discards the signed off-diagonal at that point.

We keep it, and retain the actual Hecke character, original physical
slot products, Fourier phase, original W0/W1, low outer cutoff, actual
reflected inverse row, and the exact original Mellin normalizer.

Nothing here assumes that the signed off-diagonal is negative.
-/

noncomputable section
open scoped Classical BigOperators ContDiff

namespace OAI
namespace SevenEighths.ProbePhysical

open ActualEisensteinCubic
open MeasureTheory CompletedGauss CanonicalQuadraticSieve RayFourExpansion
open RHLean.Analysis RHLean.Proof

local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- A single TRUE unselected-tuple term in the original OAI LOW
polynomial identity. This is the right-hand term of the pinned theorem
compensation_tuple_low_polynomial, with no model coefficients. -/
def actualUnselectedLowAtom
    {K : ℕ} (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ)
    (slots : Fin K → Finset O) (J : Finset (Fin K))
    (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ)
    (X Y T t : ℝ) (a : LowUnselectedTuple slots J) : ℂ :=
  lowUnselectedWeight slots J W P a *
    ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
       (X / elementNorm (∏ i : J, (a i).val))
       (Y / elementNorm (∏ i : J, (a i).val))) : ℂ)⁻¹ *
      (1 / (2 * Real.pi) : ℂ)) *
      ∫ v : ℝ, lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
        (lowOuterCutoff (a0 * a1) (max 1 (b0 * b1)))
        (X / elementNorm (∏ i : J, (a i).val))
        (Y / elementNorm (∏ i : J, (a i).val))
        (lowSelectedInverseRow Finset.univ
          (lowSelectedWeight eta slots J W P t)
          eta S hS (lowSelectedIdeal slots J) T t) v

/-- The original physical LOW complex polynomial, after the EXACT
original source Fubini, with its true signs and rows still inside atoms. -/
theorem actual_low_tuple_polynomial_eq_sum_atoms
    {K : ℕ} (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    (hbad : fixedBadPrimes ⊆ S)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0)
    (slots : Fin K → Finset O)
    (hslots : ∀ i x, x ∈ slots i → x ≠ 0)
    (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ)
    (X Y T t : ℝ) (hX : 0 < X) (hY : 0 < Y) (hT : 0 < T) :
    (∑ p : ∀ i, ↥(slots i),
      compensationSubsetWeight eta W P (fun i => (p i).val) J *
        compensationRowTest eta (calibrationForSet S hS)
          W0 W1 (fun i => (p i).val) J X Y T t *
        selectedSlotFactor W P (fun i => (p i).val) J t) =
      ∑ a : LowUnselectedTuple slots J,
        actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
          slots J W P X Y T t a := by
  have he := compensation_tuple_low_polynomial
    eta S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hWs slots hslots J W P X Y T t hX hY hT
  simpa only [actualUnselectedLowAtom] using he

set_option maxHeartbeats 2000000

/-- EXACT signed OAI LOW NNS Gram, before the OAI norm_sum_le step.
The off-diagonal is literal, not defined as total-minus-diagonal. -/
theorem actual_low_tuple_polynomial_sq_eq_signed_gram
    {K : ℕ} (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    (hbad : fixedBadPrimes ⊆ S)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0)
    (slots : Fin K → Finset O)
    (hslots : ∀ i x, x ∈ slots i → x ≠ 0)
    (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ)
    (X Y T t : ℝ) (hX : 0 < X) (hY : 0 < Y) (hT : 0 < T) :
    ‖∑ p : ∀ i, ↥(slots i),
      compensationSubsetWeight eta W P (fun i => (p i).val) J *
        compensationRowTest eta (calibrationForSet S hS)
          W0 W1 (fun i => (p i).val) J X Y T t *
        selectedSlotFactor W P (fun i => (p i).val) J t‖ ^ 2 =
      (∑ a : LowUnselectedTuple slots J,
         ‖actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
           slots J W P X Y T t a‖ ^ 2) +
      (∑ a : LowUnselectedTuple slots J,
         ∑ b ∈ (Finset.univ : Finset (LowUnselectedTuple slots J)).erase a,
           (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
               slots J W P X Y T t a *
             star (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
               slots J W P X Y T t b)).re) := by
  have heq := actual_low_tuple_polynomial_eq_sum_atoms
    eta S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hWs slots hslots J W P X Y T t hX hY hT
  have hnorm := congrArg (fun z : ℂ => ‖z‖ ^ 2) heq
  have hgram := resonant_norm_sq_sum_eq_diagonal_plus_off
    (Finset.univ : Finset (LowUnselectedTuple slots J))
    (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
      slots J W P X Y T t)
  have herase (a : LowUnselectedTuple slots J) :
      (Finset.univ : Finset (LowUnselectedTuple slots J)).erase a =
        @Finset.erase (LowUnselectedTuple slots J)
          (Classical.decEq (LowUnselectedTuple slots J)) Finset.univ a := by
    ext b
    simp only [Finset.mem_erase]
  simpa only [herase] using hnorm.trans hgram

/-- LITERAL finite-source NNS UPM/Co on the actual original LOW tuple
source. This is equal to the weighted singleton-row Co definition, but
avoids introducing an extraneous synthetic row type in the formal source. -/
def actualLowNNSCo
    {K : ℕ} (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ)
    (slots : Fin K → Finset O) (J : Finset (Fin K))
    (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ)
    (X Y T t : ℝ) : ℝ :=
  ((zeroTargetCoPartialGram
      (Finset.univ : Finset (LowUnselectedTuple slots J))
      (fun a => (stableFarComplexToRealPair
        (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
          slots J W P X Y T t a)).1)) +
   (zeroTargetCoPartialGram
      (Finset.univ : Finset (LowUnselectedTuple slots J))
      (fun a => (stableFarComplexToRealPair
        (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
          slots J W P X Y T t a)).2))) / 2

/-- LITERAL NNS LPM/Div, retaining every real/imaginary phase
coordinate of the source atom. -/
def actualLowNNSDiv
    {K : ℕ} (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ)
    (slots : Fin K → Finset O) (J : Finset (Fin K))
    (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ)
    (X Y T t : ℝ) : ℝ :=
  ((zeroTargetDivergentGram
      (Finset.univ : Finset (LowUnselectedTuple slots J))
      (fun a => (stableFarComplexToRealPair
        (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
          slots J W P X Y T t a)).1)) +
   (zeroTargetDivergentGram
      (Finset.univ : Finset (LowUnselectedTuple slots J))
      (fun a => (stableFarComplexToRealPair
        (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
          slots J W P X Y T t a)).2))) / 2

/-- Exact OAI LOW finite complex source equals its NNS Co minus Div.
This uses the previously kernel-verified native finite-source identity,
not an assumed signed covariance power saving. -/
theorem actual_low_NNS_co_minus_div_eq_normSq
    {K : ℕ} (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ)
    (slots : Fin K → Finset O) (J : Finset (Fin K))
    (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ)
    (X Y T t : ℝ) :
    actualLowNNSCo eta S hS W0 W1 a0 b0 a1 b1 slots J W P X Y T t -
      actualLowNNSDiv eta S hS W0 W1 a0 b0 a1 b1 slots J W P X Y T t =
      ‖∑ a : LowUnselectedTuple slots J,
        actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
          slots J W P X Y T t a‖ ^ 2 := by
  have hNNS := vf919FiniteSource_normSq_eq_NNS
    (Finset.univ : Finset (LowUnselectedTuple slots J))
    (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
      slots J W P X Y T t)
  dsimp only [actualLowNNSCo, actualLowNNSDiv]
  rw [hNNS]
  ring

#print axioms actual_low_tuple_polynomial_eq_sum_atoms
#print axioms actual_low_tuple_polynomial_sq_eq_signed_gram
#print axioms actual_low_NNS_co_minus_div_eq_normSq

end SevenEighths.ProbePhysical
end OAI
end


/- Source-faithful proof attempt for 20261103-lean-3, NOT CI-certified.
   Baseline: RH_Lean 040980c16901af749202e9b0f91211c43909404a.
   OAI pin: 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
   Only GitHub Actions may compile this file. -/

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

lemma supportedIdeal_inverse_square_tail (rho : ℝ) (hrho : 0 < rho)
    (hrho1 : rho < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ), 0 < Y → ∀ (F : Finset SupportedIdeal),
      (∀ I ∈ F, Y ≤ ProbeGramCommon.gramIdealNorm I) →
      (∑ I ∈ F, ProbeGramCommon.gramIdealNorm I ^ (-2 : ℝ)) ≤
        C * Y ^ (rho - 1) := by
  obtain ⟨C, hC, hb⟩ :=
    ProbeGramCommon.supportedIdeal_rpow_finite_bound (-1 - rho) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro Y hY F hF
  calc
    _ ≤ ∑ I ∈ F, ProbeGramCommon.gramIdealNorm I ^ (-1 - rho) *
        Y ^ (rho - 1) := by
      apply Finset.sum_le_sum
      intro I hI
      have hn := ProbeGramCommon.gramIdealNorm_pos I
      have he : ProbeGramCommon.gramIdealNorm I ^ (-2 : ℝ) =
          ProbeGramCommon.gramIdealNorm I ^ (-1 - rho) *
            ProbeGramCommon.gramIdealNorm I ^ (rho - 1) := by
        rw [← Real.rpow_add hn]
        congr 1
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hY (hF I hI) (by linarith))
        (Real.rpow_nonneg hn.le _)
    _ = (∑ I ∈ F, ProbeGramCommon.gramIdealNorm I ^ (-1 - rho)) *
        Y ^ (rho - 1) := (Finset.sum_mul ..).symm
    _ ≤ C * Y ^ (rho - 1) :=
      mul_le_mul_of_nonneg_right (hb F) (Real.rpow_nonneg hY.le _)

lemma canonical_slot_inverse_square_tail (rho : ℝ) (hrho : 0 < rho)
    (hrho1 : rho < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset PrimeIdeal)
      (_hT : ∀ P ∈ T, Supported P.val) (Y : ℝ), 0 < Y →
      (∀ P ∈ T, Y ≤ (Ideal.absNorm P.val : ℝ)) →
      (∑ a : canonicalSlotSupport T, elementNorm a.val ^ (-2 : ℝ)) ≤
        C * Y ^ (rho - 1) := by
  obtain ⟨C, hC, hb⟩ := supportedIdeal_inverse_square_tail rho hrho hrho1
  refine ⟨C, hC, ?_⟩
  intro T hT Y hY hnorm
  let f : T → SupportedIdeal := fun P => ⟨P.val.val, hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal => I.val) h
  have he : (∑ a : canonicalSlotSupport T, elementNorm a.val ^ (-2 : ℝ)) =
      ∑ I ∈ Finset.univ.image f, ProbeGramCommon.gramIdealNorm I ^ (-2 : ℝ) := by
    rw [Finset.sum_image (fun P _ Q _ h => hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp
      (fun a => elementNorm a.val ^ (-2 : ℝ))
    rw [← hh]
    apply Finset.sum_congr rfl
    intro P hP
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  apply hb Y hY
  intro I hI
  obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp hI
  change Y ≤ (Ideal.absNorm P.val.val : ℝ)
  exact hnorm P.val P.property

-- C is chosen before K, the slot sets, the cutoffs, and the windows.
theorem lowUnselectedMass_moving_bound (rho : ℝ) (hrho : 0 < rho)
    (hrho1 : rho < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (T : Fin K → Finset PrimeIdeal)
      (_hT : ∀ i P, P ∈ T i → Supported P.val) (Y B : Fin K → ℝ),
      (∀ i, 0 < Y i) → (∀ i, 0 ≤ B i) →
      (∀ i P, P ∈ T i → Y i ≤ (Ideal.absNorm P.val : ℝ)) →
      ∀ (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ),
      (∀ i x, ‖W i x‖ ≤ B i) →
      (∑ a : LowUnselectedTuple (fun i => canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i => canonicalSlotSupport (T i)) J W P a‖ *
          elementNorm (∏ i : J, (a i).val) ^ (-(1 / 2 : ℝ))) ≤
        ∏ i : J, (C * B i.val) * (Y i.val) ^ (rho - 1) := by
  obtain ⟨C, hC, hb⟩ := canonical_slot_inverse_square_tail rho hrho hrho1
  refine ⟨C, hC, ?_⟩
  intro K T hT Y B hY hB hnorm J W P hW
  simp_rw [lowUnselectedWeight_norm_identity _
    (fun i => canonicalSlotSupport_nonzero _ (hT i))]
  rw [← Fintype.prod_sum
    (fun (i : J) (a : canonicalSlotSupport (T i.val)) =>
      elementNorm a.val ^ (-2 : ℝ) *
        ‖W i.val (elementNorm a.val / P i.val)‖)]
  apply Finset.prod_le_prod₀
    (fun i _ => Finset.sum_nonneg (fun a _ =>
      mul_nonneg (Real.rpow_nonneg (by unfold elementNorm; positivity) _)
        (norm_nonneg _)))
  intro i hi
  calc
    _ ≤ ∑ a : canonicalSlotSupport (T i.val),
        elementNorm a.val ^ (-2 : ℝ) * B i.val := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hW i.val _)
        (Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    _ = (∑ a : canonicalSlotSupport (T i.val),
        elementNorm a.val ^ (-2 : ℝ)) * B i.val := (Finset.sum_mul ..).symm
    _ ≤ (C * (Y i.val) ^ (rho - 1)) * B i.val :=
      mul_le_mul_of_nonneg_right
        (hb (T i.val) (hT i.val) (Y i.val) (hY i.val) (hnorm i.val))
        (hB i.val)
    _ = (C * B i.val) * (Y i.val) ^ (rho - 1) := by ring

theorem lowUnselectedMass_moving_power_bound (rho : ℝ) (hrho : 0 < rho)
    (hrho1 : rho < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (T : Fin K → Finset PrimeIdeal)
      (_hT : ∀ i P, P ∈ T i → Supported P.val)
      (ell : Fin K → ℝ) (a Z B : ℝ), 0 < a → 0 < Z → 0 ≤ B →
      (∀ i P, P ∈ T i → a * Z ^ (ell i) ≤ (Ideal.absNorm P.val : ℝ)) →
      ∀ (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ),
      (∀ i x, ‖W i x‖ ≤ B) →
      (∑ u : LowUnselectedTuple (fun i => canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i => canonicalSlotSupport (T i)) J W P u‖ *
          elementNorm (∏ i : J, (u i).val) ^ (-(1 / 2 : ℝ))) ≤
        (C * B * a ^ (rho - 1)) ^ J.card *
          Z ^ ((rho - 1) * (∑ i ∈ J, ell i)) := by
  obtain ⟨C, hC, hb⟩ := lowUnselectedMass_moving_bound rho hrho hrho1
  refine ⟨C, hC, ?_⟩
  intro K T hT ell a Z B ha hZ hB hnorm J W P hW
  have hm := hb K T hT (fun i => a * Z ^ (ell i)) (fun _ => B)
    (fun _ => by positivity) (fun _ => hB) hnorm J W P hW
  have hp : ∀ i : Fin K,
      (C * B) * (a * Z ^ (ell i)) ^ (rho - 1) =
        (C * B * a ^ (rho - 1)) * Z ^ ((rho - 1) * ell i) := by
    intro i
    rw [Real.mul_rpow ha.le (Real.rpow_nonneg hZ.le _), ← Real.rpow_mul hZ.le]
    rw [mul_comm (ell i) (rho - 1)]
    ring
  calc
    _ ≤ ∏ i : J, (C * B) * (a * Z ^ (ell i.val)) ^ (rho - 1) := hm
    _ = ∏ i : J, (C * B * a ^ (rho - 1)) *
        Z ^ ((rho - 1) * ell i.val) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hp i.val
    _ = (C * B * a ^ (rho - 1)) ^ J.card *
        Z ^ ((rho - 1) * (∑ i ∈ J, ell i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_coe, ← Real.rpow_sum_of_pos hZ, Finset.mul_sum]

theorem lowUnselectedMass_empty (K : ℕ) (T : Fin K → Finset PrimeIdeal)
    (hT : ∀ i P, P ∈ T i → Supported P.val)
    (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ) :
    (∑ a : LowUnselectedTuple (fun i => canonicalSlotSupport (T i))
        (∅ : Finset (Fin K)),
      ‖lowUnselectedWeight (fun i => canonicalSlotSupport (T i)) ∅ W P a‖ *
        elementNorm (∏ i : (∅ : Finset (Fin K)), (a i).val) ^
          (-(1 / 2 : ℝ))) = 1 := by
  simp_rw [lowUnselectedWeight_norm_identity _
    (fun i => canonicalSlotSupport_nonzero _ (hT i))]
  rw [← Fintype.prod_sum
    (fun (i : (∅ : Finset (Fin K))) (a : canonicalSlotSupport (T i.val)) =>
      elementNorm a.val ^ (-2 : ℝ) *
        ‖W i.val (elementNorm a.val / P i.val)‖)]
  simp

end SevenEighths.ProbePhysical
end

end OAI

#print axioms OAI.SevenEighths.ProbePhysical.supportedIdeal_inverse_square_tail
#print axioms OAI.SevenEighths.ProbePhysical.canonical_slot_inverse_square_tail
#print axioms OAI.SevenEighths.ProbePhysical.lowUnselectedMass_moving_bound
#print axioms OAI.SevenEighths.ProbePhysical.lowUnselectedMass_moving_power_bound
#print axioms OAI.SevenEighths.ProbePhysical.lowUnselectedMass_empty


/- Uncompiled continuation of 20261103-lean-3 and Referee R9.
   The original LowCentralTuple proof is retained until its final mass step.
   Only authorized GitHub Actions may compile this proof attempt. -/

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem low_central_compensated_tuple_moving_mass
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(X : ℝ),0<X→
      Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      ‖∑p : ∀i,canonicalSlotSupport (T i),
        compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J*
          compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J
            (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) X t*
          selectedSlotFactor W (fun i=>Z^(ell i)) (fun i=>(p i).val) J t‖≤
        C*(1+‖t‖)^degree*
          Z^(3/16+254*ε+(rho-1)*(∑i∈J,ell i)) := by
  obtain ⟨Cg,hCg,hgram⟩ := compensation_tuple_actual_gram ε hε hε1 W0 W1
    a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM S hS hbad
  obtain ⟨degree,Ci,hCi,hinverse⟩ := low_physical_inverse_normalized η S hS hbad ell hell hsum
    a b (a0*a1) (max 1 (b0*b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cm,hCm,hmass⟩ := lowUnselectedMass_moving_power_bound rho hrho hrho1
  let Cu := (max 1 (Cm * a ^ (rho - 1))) ^ K
  have hCu : 0 < Cu := by dsimp [Cu]; positivity
  let q := elementNorm (calibrationForSet S hS).generator
  have hq : 0<q := calibration_elementNorm_pos _
  let C0 := Cg*Ci*Real.sqrt (3*q)*Cu
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hinverse,eventually_original_slot_scales (calibrationForSet S hS)
    ell hell hsum (max 1 b) (le_max_left _ _)] with Z hInv hScale
  refine ⟨hInv.1,?_⟩
  intro T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  let slots := fun i=>canonicalSlotSupport (T i)
  let Yp := fun i=>Z^(ell i)
  have hz : 0<Z := lt_trans zero_lt_one hInv.1
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈slots i→elementNorm n ≤ max 1 b * Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) X t
    (by positivity) (by positivity) hX (fun p=>(hs p).1) (fun p=>(hs p).2.1)
  apply hg.trans
  let G := Z^(3/16+(23/96)*ε:ℝ)
  let V := Ci*(1+‖t‖)^degree*Z^(507*ε/2)
  have hGV : G*V≤Ci*(1+‖t‖)^degree*Z^(3/16+254*ε) := by
    dsimp only [G,V]
    calc
      _=Ci*(1+‖t‖)^degree*(Z^(3/16+(23/96)*ε:ℝ)*Z^(507*ε/2)) := by ring
      _≤_ := by
        rw [←Real.rpow_add hz]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hInv.1.le (by linarith)
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
      ‖lowUnselectedWeight slots J W Yp p‖*((Real.sqrt Q)⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ε*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
            η S hS (lowSelectedIdeal slots J) X t)≤
      (Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(3/16+254*ε))*
        (‖lowUnselectedWeight slots J W Yp p‖*L^(-(1/2:ℝ))) := by
    dsimp only
    let L := elementNorm (∏i : J,(p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
    have hL := lowUnselectedProduct_norm_pos slots hslots J p
    have hgb := (hs p).2.2 ε hε.le
    have hib := hInv.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
      (div_pos (by positivity) hL) (div_pos (by positivity) hL)
    have hgn : 0≤lowGramFactor (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ε := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hib
      (mul_nonneg (norm_nonneg (lowUnselectedWeight slots J W Yp p)) hgn)
    have hh2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgb (norm_nonneg (lowUnselectedWeight slots J W Yp p)))
      (show 0≤V by dsimp [V];positivity)
    calc
      _=‖lowUnselectedWeight slots J W Yp p‖*
        lowGramFactor (calibrationForSet S hS) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ε*
        (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L)
          (div_pos (by positivity) hL) (div_pos (by positivity) hL)
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t) η S hS (lowSelectedIdeal slots J) X t) := by ring
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*(G*V) := by
        have hh3 := hh.trans hh2
        simp only [G,V,div_eq_mul_inv,mul_assoc] at hh3 ⊢
        convert hh3 using 1 ; congr 7
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*
          (Ci*(1+‖t‖)^degree*Z^(3/16+254*ε)) :=
        mul_le_mul_of_nonneg_left hGV (by positivity)
      _=_ := by rw [low_compensated_sqrt_factor q L hq.le hL];ring
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hterm p)) hCg.le
  apply hh.trans
  rw [←Finset.mul_sum]
  have hm0 := hmass K T hT ell a Z 1 ha hz (by norm_num)
    (fun i P hP => (hnorm i P hP).1) J W Yp hW
  have hpow : (Cm * 1 * a ^ (rho - 1)) ^ J.card ≤ Cu := by
    simp only [mul_one]
    apply (pow_le_pow_left₀ (by positivity)
      (le_max_right 1 (Cm * a ^ (rho - 1))) J.card).trans
    exact pow_le_pow_right₀ (le_max_left _ _)
      (by simpa using Finset.card_le_card (Finset.subset_univ J))
  have hm :
      (∑p : LowUnselectedTuple slots J,
        ‖lowUnselectedWeight slots J W Yp p‖*
          elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ))) ≤
        Cu * Z ^ ((rho - 1) * (∑i∈J,ell i)) :=
    hm0.trans (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hz.le _))
  calc
    _≤Cg*((Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(3/16+254*ε))*
        (Cu * Z ^ ((rho - 1) * (∑i∈J,ell i)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hm (by positivity)) hCg.le
    _=C0*(1+‖t‖)^degree*
        (Z^(3/16+254*ε)*Z^((rho-1)*(∑i∈J,ell i))) := by dsimp [C0]; ring
    _=_ := by rw [← Real.rpow_add hz]

end SevenEighths.ProbePhysical
end

end OAI

#print axioms OAI.SevenEighths.ProbePhysical.low_central_compensated_tuple_moving_mass

#check OAI.SevenEighths.ProbePhysical.lowUnselectedMass_moving_bound
#check OAI.SevenEighths.ProbePhysical.lowUnselectedMass_moving_power_bound
#check OAI.SevenEighths.ProbePhysical.lowUnselectedMass_empty
#check OAI.SevenEighths.ProbePhysical.low_central_compensated_tuple_moving_mass
