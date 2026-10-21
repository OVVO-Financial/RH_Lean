import Mathlib
import «research.LOW_OWNER_RETURNED_CORE_ZERO_TARGET_GRAM»
import «research.STABLE_FAR_PERRON_REALIFICATION»
import «research.VF_919_OAI_POLARIZED_EULER_BRIDGE_20261021»

/-!
# The ACTUAL marked weighted Hecke kernel in unnormalized NNS covariance

The source uses the original selected physical-row weight `‖W(u)‖²`.
If the marked product `P_j(u)*P_k(u)` is represented by the FINITE
original ideal-atom field in full real Phi coordinates, the exact marked
moment is the signed NNS zero-target Co/Div quadratic form of those atoms.

Source admission is a VISIBLE hypothesis. The conclusion does NOT assume
that arbitrary ideal atoms already coincide with OAI's production source.

This is a signed second moment of the P_j*P_k PRODUCT (degree four
in the two derivative polynomials), not the fourth power of that product.
The weight is never normalized by the row count.

The compensation for one Euler pair A-B is the *positive* same-sign
partial-moment excess Co-Div, paid BEFORE the nonnegative squared norm.

No source saving, density hypothesis, RH or new zero-free exponent is
postulated. The open analytic estimate must be independently established.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Proof

/-- Finite ideal-product convolution, BEFORE taking any norm. This is the
unconditional algebraic source-lift for each selected j,k pair once their
ACTUAL OAI polynomial rows have been identified with their ideal sums. -/
theorem vf919MarkedFiniteProductAtoms
    {α β : Type*} (s : Finset α) (t : Finset β)
    (a : α → ℂ) (b : β → ℂ) :
    (∑ i ∈ s, a i) * (∑ j ∈ t, b j) =
      ∑ ij ∈ s.product t, a ij.1 * b ij.2 := by
  calc
    (∑ i ∈ s, a i) * (∑ j ∈ t, b j) =
      ∑ i ∈ s, a i * (∑ j ∈ t, b j) := by
        rw [Finset.sum_mul]
    _ = ∑ i ∈ s, ∑ j ∈ t, a i * b j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = ∑ ij ∈ s.product t, a ij.1 * b ij.2 := by
      rw [Finset.sum_product]

/-- Phi is additive even on full finite ideal-labelled sums: no phase
or multiplicity is lost in the REAL coordinate transfer. -/
theorem vf919Phi_sum_idealAtoms
    {α : Type*} (s : Finset α) (a : α → ℂ) :
    stableFarComplexToRealPair (∑ i ∈ s, a i) =
      ((∑ i ∈ s, (stableFarComplexToRealPair (a i)).1),
       (∑ i ∈ s, (stableFarComplexToRealPair (a i)).2)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [stableFarComplexToRealPair]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      have hadd (z w : ℂ) :
          stableFarComplexToRealPair (z + w) =
          ((stableFarComplexToRealPair z).1 +
             (stableFarComplexToRealPair w).1,
           (stableFarComplexToRealPair z).2 +
             (stableFarComplexToRealPair w).2) := by
        simp [stableFarComplexToRealPair]
        constructor <;> ring
      rw [hadd, ih]

/-- OpenAI's own detector_row_eq_source gives a NORMALIZED finite ideal
column sum. The selected physical product is ALREADY part of the individual
source coefficient. It is incorrect to multiply by |W(u)|^2 again here.

This theorem is the exact unnormalized NNS reading of one such finite
Hecke column source, with no source-specific assumptions and no lost phase. -/
theorem vf919FiniteSource_normSq_eq_NNS
    {α : Type*} [DecidableEq α] (atoms : Finset α) (a : α → ℂ) :
    ‖∑ I ∈ atoms, a I‖ ^ 2 =
      ((zeroTargetCoPartialGram atoms
          (fun I => (stableFarComplexToRealPair (a I)).1) +
        zeroTargetCoPartialGram atoms
          (fun I => (stableFarComplexToRealPair (a I)).2)) -
       (zeroTargetDivergentGram atoms
          (fun I => (stableFarComplexToRealPair (a I)).1) +
        zeroTargetDivergentGram atoms
          (fun I => (stableFarComplexToRealPair (a I)).2))) / 2 := by
  have hphi := vf919Phi_sum_idealAtoms atoms a
  have hnorm := stableFarRealPairNormalizedEnergy_complexToRealPair
    (∑ I ∈ atoms, a I)
  rw [hphi] at hnorm
  change (((∑ I ∈ atoms, (stableFarComplexToRealPair (a I)).1) ^ 2 +
      (∑ I ∈ atoms, (stableFarComplexToRealPair (a I)).2) ^ 2) / 2) =
    ‖∑ I ∈ atoms, a I‖ ^ 2 at hnorm
  rw [← hnorm]
  rw [zeroTarget_globalGram_reassembly,
      zeroTarget_globalGram_reassembly]
  ring

/-- This is the EXACT SOURCE FORM OpenAI supplies after
detector_row_eq_source and its normalized_norm_sq lemma:
  D_U^(-1) sum_{u∈F.rows} |sum_{I∈finiteColumns} c_I R_u(I)|^2.
Here n stands for that literal D_U and the actual physical selected masks
are ALREADY embedded in a(u,I). -/
theorem vf919NormalizedColumnSource_NNSCovariance
    {ι α : Type*} [DecidableEq α]
    (rows : Finset ι) (atoms : Finset α)
    (a : ι → α → ℂ) (n : ℝ) :
    (∑ u ∈ rows, (1 / n) * ‖∑ I ∈ atoms, a u I‖ ^ 2) =
      (∑ u ∈ rows, (1 / n) *
        ((zeroTargetCoPartialGram atoms
            (fun I => (stableFarComplexToRealPair (a u I)).1) +
          zeroTargetCoPartialGram atoms
            (fun I => (stableFarComplexToRealPair (a u I)).2)) / 2)) -
      (∑ u ∈ rows, (1 / n) *
        ((zeroTargetDivergentGram atoms
            (fun I => (stableFarComplexToRealPair (a u I)).1) +
          zeroTargetDivergentGram atoms
            (fun I => (stableFarComplexToRealPair (a u I)).2)) / 2)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [vf919FiniteSource_normSq_eq_NNS]
  ring

/-- Original finite row energy in Fred's invertible two-real-coordinate Phi
representation. The row amplitude is the sum of all retained source atoms. -/
def vf919WeightedPhiMarkedMoment
    {ι α : Type*} (rows : Finset ι) (atoms : Finset α)
    (w : ι → ℝ) (x y : ι → α → ℝ) : ℝ :=
  ∑ u ∈ rows, w u *
    (((∑ i ∈ atoms, x u i) ^ 2 +
      (∑ i ∈ atoms, y u i) ^ 2) / 2)

/-- Total (including the diagonal) SAME-sign NNS quadrant population.
An arbitrary external physical weight is preserved at its original row. -/
def vf919WeightedPhiCoMass
    {ι α : Type*} [DecidableEq α] (rows : Finset ι)
    (atoms : Finset α) (w : ι → ℝ)
    (x y : ι → α → ℝ) : ℝ :=
  ∑ u ∈ rows, (w u / 2) *
    (zeroTargetCoPartialGram atoms (x u) +
     zeroTargetCoPartialGram atoms (y u))

/-- Total OPPOSITE-sign NNS quadrant population at the same physical rows. -/
def vf919WeightedPhiDivMass
    {ι α : Type*} [DecidableEq α] (rows : Finset ι)
    (atoms : Finset α) (w : ι → ℝ)
    (x y : ι → α → ℝ) : ℝ :=
  ∑ u ∈ rows, (w u / 2) *
    (zeroTargetDivergentGram atoms (x u) +
     zeroTargetDivergentGram atoms (y u))

/-- THIS is the direct unnormalized NNS covariance decomposition of the
complete weighted, labelled ideal-character kernel. Every pair is retained,
including its exact character phase, with no triangle inequality. -/
theorem vf919WeightedPhiMarkedMoment_eq_co_sub_div
    {ι α : Type*} [DecidableEq α] (rows : Finset ι)
    (atoms : Finset α) (w : ι → ℝ)
    (x y : ι → α → ℝ) :
    vf919WeightedPhiMarkedMoment rows atoms w x y =
      vf919WeightedPhiCoMass rows atoms w x y -
        vf919WeightedPhiDivMass rows atoms w x y := by
  unfold vf919WeightedPhiMarkedMoment vf919WeightedPhiCoMass
    vf919WeightedPhiDivMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hx := zeroTarget_globalGram_reassembly atoms (x u)
  have hy := zeroTarget_globalGram_reassembly atoms (y u)
  calc
    w u * (((∑ i ∈ atoms, x u i) ^ 2 +
        (∑ i ∈ atoms, y u i) ^ 2) / 2) =
      (w u / 2) *
        ((∑ i ∈ atoms, x u i) ^ 2 +
         (∑ i ∈ atoms, y u i) ^ 2) := by ring
    _ = (w u / 2) *
        ((zeroTargetCoPartialGram atoms (x u) -
          zeroTargetDivergentGram atoms (x u)) +
         (zeroTargetCoPartialGram atoms (y u) -
          zeroTargetDivergentGram atoms (y u))) := by rw [hx, hy]
    _ = (w u / 2) *
        (zeroTargetCoPartialGram atoms (x u) +
         zeroTargetCoPartialGram atoms (y u)) -
      (w u / 2) *
        (zeroTargetDivergentGram atoms (x u) +
         zeroTargetDivergentGram atoms (y u)) := by ring

/-- Original diagonal of the REAL normalized Phi Gram, without replacing
the original physical row weights or assigning artificial equal weights. -/
def vf919WeightedPhiDiagonal
    {ι α : Type*} (rows : Finset ι) (atoms : Finset α)
    (w : ι → ℝ) (x y : ι → α → ℝ) : ℝ :=
  ∑ u ∈ rows, w u *
    (∑ i ∈ atoms, ((x u i)^2 + (y u i)^2) / 2)

/-- The exact remaining same-sign CO-PARTIAL energy AFTER paying the
diagonal once. This definition is the full Co sum minus its diagonal.
The physical offdiagonal interpretation follows from the finite pair carrier,
not from an extra capacity reserve. -/
def vf919WeightedPhiCoOff
    {ι α : Type*} [DecidableEq α] (rows : Finset ι)
    (atoms : Finset α) (w : ι → ℝ)
    (x y : ι → α → ℝ) : ℝ :=
  vf919WeightedPhiCoMass rows atoms w x y -
    vf919WeightedPhiDiagonal rows atoms w x y

/-- An exact diagonal + signed covariance identity in native NNS terms. -/
theorem vf919WeightedPhiMarkedMoment_eq_diagonal_add_offCo_sub_div
    {ι α : Type*} [DecidableEq α] (rows : Finset ι)
    (atoms : Finset α) (w : ι → ℝ)
    (x y : ι → α → ℝ) :
    vf919WeightedPhiMarkedMoment rows atoms w x y =
      vf919WeightedPhiDiagonal rows atoms w x y +
        vf919WeightedPhiCoOff rows atoms w x y -
        vf919WeightedPhiDivMass rows atoms w x y := by
  rw [vf919WeightedPhiMarkedMoment_eq_co_sub_div]
  unfold vf919WeightedPhiCoOff
  ring

/-- Genuine production-style OAI marked moment: W is the ORIGINAL complex
physical selected-prime product; j,k index the ORIGINAL derivative polynomials.
The only premise is explicit FULL source-atom equality in Fred's Phi
coordinates. It is intentionally NOT constructed out of thin air. -/
theorem vf919ActualMarkedMoment_eq_exactWeightedNNSCovariance
    {ι α : Type*} [DecidableEq α] (rows : Finset ι)
    (atoms : Finset α) (Pj Pk W : ι → ℂ)
    (x y : ι → α → ℝ)
    (hActualAtoms : ∀ u ∈ rows,
      stableFarComplexToRealPair (Pj u * Pk u) =
        ((∑ i ∈ atoms, x u i), (∑ i ∈ atoms, y u i))) :
    (∑ u ∈ rows, ‖W u‖ ^ 2 * ‖Pj u * Pk u‖ ^ 2) =
      vf919WeightedPhiCoMass rows atoms
        (fun u => ‖W u‖ ^ 2) x y -
      vf919WeightedPhiDivMass rows atoms
        (fun u => ‖W u‖ ^ 2) x y := by
  have hrep :
      (∑ u ∈ rows, ‖W u‖ ^ 2 * ‖Pj u * Pk u‖ ^ 2) =
        vf919WeightedPhiMarkedMoment rows atoms
          (fun u => ‖W u‖ ^ 2) x y := by
    unfold vf919WeightedPhiMarkedMoment
    apply Finset.sum_congr rfl
    intro u hu
    have he := stableFarRealPairNormalizedEnergy_complexToRealPair
      (Pj u * Pk u)
    rw [hActualAtoms u hu] at he
    change (((∑ i ∈ atoms, x u i) ^ 2 +
        (∑ i ∈ atoms, y u i) ^ 2) / 2) =
      ‖Pj u * Pk u‖ ^ 2 at he
    rw [he]
  rw [hrep]
  exact vf919WeightedPhiMarkedMoment_eq_co_sub_div rows atoms
    (fun u => ‖W u‖ ^ 2) x y

/-- The *local paired Euler source* has a concrete favorable Co-Div payment.
This is exactly where phase alignment must be supplied by the arithmetic.
The sign is MINUS because an Euler pair is A-B, not A+B. -/
theorem vf919EulerPairWeightedNNSCovariance
    {ι : Type*} (rows : Finset ι)
    (w : ι → ℝ) (A B : ι → ℝ × ℝ) :
    (∑ u ∈ rows, w u *
      ((((A u).1 - (B u).1)^2 +
         ((A u).2 - (B u).2)^2) / 2)) =
    ∑ u ∈ rows, w u *
      (((A u).1^2+(A u).2^2+
        (B u).1^2+(B u).2^2)/2 -
        ((zeroTargetCoPartialPair (A u).1 (B u).1 +
          zeroTargetCoPartialPair (A u).2 (B u).2) -
         (zeroTargetDivergentPair (A u).1 (B u).1 +
          zeroTargetDivergentPair (A u).2 (B u).2))) := by
  apply Finset.sum_congr rfl
  intro u hu
  have hx := zeroTargetCoPartial_sub_divergent_eq_mul
    (A u).1 (B u).1
  have hy := zeroTargetCoPartial_sub_divergent_eq_mul
    (A u).2 (B u).2
  calc
    w u * ((((A u).1-(B u).1)^2 +
        ((A u).2-(B u).2)^2) / 2) =
      w u *
      (((A u).1^2+(A u).2^2+(B u).1^2+(B u).2^2)/2 -
        ((A u).1*(B u).1+(A u).2*(B u).2)) := by ring
    _ = w u *
      (((A u).1^2+(A u).2^2+(B u).1^2+(B u).2^2)/2 -
        ((zeroTargetCoPartialPair (A u).1 (B u).1 +
          zeroTargetCoPartialPair (A u).2 (B u).2) -
         (zeroTargetDivergentPair (A u).1 (B u).1 +
          zeroTargetDivergentPair (A u).2 (B u).2))) := by
      rw [← hx, ← hy]
      ring

/-- The only way the previous finite NNS identity yields a new analytic
bound: an INDEPENDENT arithmetic LOWER bound on aligned Co-Div.
This theorem is conditional and records no unproved analytic axiom. -/
theorem vf919EulerPairPowerSaving_of_independent_alignment
    (diagonal co div bound energy : ℝ)
    (hE : energy = diagonal - (co - div))
    (hArithmetic : diagonal - bound ≤ co - div) :
    energy ≤ bound := by
  linarith

end RHLean.Analysis

#print axioms RHLean.Analysis.vf919FiniteSource_normSq_eq_NNS
#print axioms RHLean.Analysis.vf919NormalizedColumnSource_NNSCovariance
#print axioms RHLean.Analysis.vf919WeightedPhiMarkedMoment_eq_co_sub_div
#print axioms RHLean.Analysis.vf919ActualMarkedMoment_eq_exactWeightedNNSCovariance
#print axioms RHLean.Analysis.vf919EulerPairWeightedNNSCovariance
#print axioms RHLean.Analysis.vf919EulerPairPowerSaving_of_independent_alignment
