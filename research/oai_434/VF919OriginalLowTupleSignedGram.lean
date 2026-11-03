import «research.VF_919_RESONANT_FIBER_NNS_RECOMBINATION_20261022»
import OAI.NumberTheory.DirichletL.Detector.LowSlotPolynomial

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
  calc
    _ = ‖∑ a : LowUnselectedTuple slots J,
        actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
          slots J W P X Y T t a‖ ^ 2 :=
      congrArg (fun z : ℂ => ‖z‖ ^ 2) heq
    _ = _ := resonant_norm_sq_sum_eq_diagonal_plus_off
      (Finset.univ : Finset (LowUnselectedTuple slots J))
      (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
        slots J W P X Y T t)

/-- LITERAL NNS UPM/Co source on a singleton original LOW probe
row. Original ideal, character and Fourier weights remain in the atom. -/
def actualLowNNSCo
    {K : ℕ} (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ)
    (slots : Fin K → Finset O) (J : Finset (Fin K))
    (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ)
    (X Y T t : ℝ) : ℝ :=
  vf919WeightedPhiCoMass
    (Finset.univ : Finset Unit)
    (Finset.univ : Finset (LowUnselectedTuple slots J))
    (fun _ => 1)
    (fun _ a =>
      (stableFarComplexToRealPair
        (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
          slots J W P X Y T t a)).1)
    (fun _ a =>
      (stableFarComplexToRealPair
        (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
          slots J W P X Y T t a)).2)

/-- LITERAL NNS LPM/Div source paired with the true Co field above. -/
def actualLowNNSDiv
    {K : ℕ} (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 : ℝ)
    (slots : Fin K → Finset O) (J : Finset (Fin K))
    (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ)
    (X Y T t : ℝ) : ℝ :=
  vf919WeightedPhiDivMass
    (Finset.univ : Finset Unit)
    (Finset.univ : Finset (LowUnselectedTuple slots J))
    (fun _ => 1)
    (fun _ a =>
      (stableFarComplexToRealPair
        (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
          slots J W P X Y T t a)).1)
    (fun _ a =>
      (stableFarComplexToRealPair
        (actualUnselectedLowAtom eta S hS W0 W1 a0 b0 a1 b1
          slots J W P X Y T t a)).2)

/-- Actual OAI LOW polynomial source is EXACTLY NNS Co minus Div.
This is a source-level equality, not a new signed estimate. -/
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
  let f : Unit → LowUnselectedTuple slots J → ℂ :=
    fun _ a => actualUnselectedLowAtom eta S hS W0 W1
      a0 b0 a1 b1 slots J W P X Y T t a
  have hNNS := resonant_fiber_recombination_NNS_eq
    (Finset.univ : Finset Unit)
    (Finset.univ : Finset (LowUnselectedTuple slots J))
    (fun a : LowUnselectedTuple slots J => a) f (fun _ => 1)
  have hGram := resonant_fiber_recombination_eq
    (Finset.univ : Finset Unit)
    (Finset.univ : Finset (LowUnselectedTuple slots J))
    (fun a : LowUnselectedTuple slots J => a) f (fun _ => 1)
  rw [← hGram] at hNNS
  simpa [actualLowNNSCo, actualLowNNSDiv, f] using hNNS

#print axioms actual_low_tuple_polynomial_eq_sum_atoms
#print axioms actual_low_tuple_polynomial_sq_eq_signed_gram
#print axioms actual_low_NNS_co_minus_div_eq_normSq

end SevenEighths.ProbePhysical
end OAI
end
