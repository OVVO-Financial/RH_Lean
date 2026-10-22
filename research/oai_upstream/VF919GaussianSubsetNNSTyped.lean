import OAI.NumberTheory.DirichletL.Detector.GaussianCommon

/-!
# Source-typed OAI Gaussian subset / NNS bridge

This file is intended for compilation INSIDE openai/math/lean, using the
original OAI project and its pinned Lean 4.34.1 + Mathlib environment.

It uses the actual OAI declarations:
* SevenEighths.ProbePhysical.compensatedPhysicalProbe_common_gaussian
* compensationSubsetWeight, compensationRowTest, selectedSlotFactor
* gaussianJointDensity, correctedCompletedT (inside compensationRowTest)
* compensatedPhysicalProbe, CalibrationData, HeckeFamily.Character.

It is intentionally not a fake OAI namespace inside RHLean. Neither
the original arithmetical source nor its covariance is replaced by a
norm-only or equal-phase surrogate.

The signed NNS Co and Div totals are the full ZERO-TARGET partial-moment
quadratic forms. Products of their positive/negative partial sums retain
all ordered cross-ideal, cross-subset, and principal/source interactions.
All dyadic and Mellin integration happens BEFORE taking the norm.

No new analytic saving is asserted.
-/

noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory FourierBridge CompletedGauss

namespace OAI
namespace SevenEighths.ProbePhysical

local notation "O" => ActualEisensteinCubic.O

private def nnsPhiMinus (z : ℂ) : ℝ := z.re - z.im
private def nnsPhiPlus (z : ℂ) : ℝ := z.re + z.im
private def nnsUp (x : ℝ) : ℝ := max x 0
private def nnsDown (x : ℝ) : ℝ := max (-x) 0

private theorem nnsUp_sub_down (x : ℝ) :
    nnsUp x - nnsDown x = x := by
  rcases le_total 0 x with hx | hx
  · simp [nnsUp, nnsDown, max_eq_left hx,
      max_eq_right (show -x ≤ (0 : ℝ) by linarith)]
  · simp [nnsUp, nnsDown, max_eq_right hx,
      max_eq_left (show (0 : ℝ) ≤ -x by linarith)]

private theorem nnsPhiMinus_add (z w : ℂ) :
    nnsPhiMinus (z + w) = nnsPhiMinus z + nnsPhiMinus w := by
  simp [nnsPhiMinus, Complex.add_re, Complex.add_im]
  ring

private theorem nnsPhiPlus_add (z w : ℂ) :
    nnsPhiPlus (z + w) = nnsPhiPlus z + nnsPhiPlus w := by
  simp [nnsPhiPlus, Complex.add_re, Complex.add_im]
  ring

private theorem nnsPhiMinus_sum {α : Type*}
    (s : Finset α) (a : α → ℂ) :
    nnsPhiMinus (∑ i ∈ s, a i) = ∑ i ∈ s, nnsPhiMinus (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nnsPhiMinus]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, nnsPhiMinus_add, ih]

private theorem nnsPhiPlus_sum {α : Type*}
    (s : Finset α) (a : α → ℂ) :
    nnsPhiPlus (∑ i ∈ s, a i) = ∑ i ∈ s, nnsPhiPlus (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nnsPhiPlus]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, nnsPhiPlus_add, ih]

private theorem nnsPhi_norm (z : ℂ) :
    ‖z‖ ^ 2 = (nnsPhiMinus z ^ 2 + nnsPhiPlus z ^ 2) / 2 := by
  rw [Complex.sq_norm]
  simp [nnsPhiMinus, nnsPhiPlus, Complex.normSq_apply]
  ring

private def nnsPositiveSum {α : Type*} (s : Finset α)
    (a : α → ℂ) (f : ℂ → ℝ) : ℝ :=
  ∑ i ∈ s, nnsUp (f (a i))

private def nnsNegativeSum {α : Type*} (s : Finset α)
    (a : α → ℂ) (f : ℂ → ℝ) : ℝ :=
  ∑ i ∈ s, nnsDown (f (a i))

/-- Full co-signed zero-target NNS moment, including diagonal and
    all offdiagonal ordered coefficient occurrences. -/
def oaiNNSCoAll {α : Type*} (s : Finset α) (a : α → ℂ) : ℝ :=
  ((nnsPositiveSum s a nnsPhiMinus) ^ 2 +
   (nnsNegativeSum s a nnsPhiMinus) ^ 2 +
   (nnsPositiveSum s a nnsPhiPlus) ^ 2 +
   (nnsNegativeSum s a nnsPhiPlus) ^ 2) / 2

/-- Full opposite-signed zero-target NNS moment, with all ordered
    offdiagonal interactions; no implicit covariance sign assumption. -/
def oaiNNSDivAll {α : Type*} (s : Finset α) (a : α → ℂ) : ℝ :=
  (2 * nnsPositiveSum s a nnsPhiMinus * nnsNegativeSum s a nnsPhiMinus +
   2 * nnsPositiveSum s a nnsPhiPlus * nnsNegativeSum s a nnsPhiPlus) / 2

private theorem nnsPhi_sum_eq_up_sub_down {α : Type*}
    (s : Finset α) (a : α → ℂ) (f : ℂ → ℝ) :
    (∑ i ∈ s, f (a i)) =
      nnsPositiveSum s a f - nnsNegativeSum s a f := by
  unfold nnsPositiveSum nnsNegativeSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact (nnsUp_sub_down (f (a i))).symm

/-- Native kernel-checked NNS identity, preserving every original
    complex source coefficient, its phase, its label and both signs.
    This is algebraic, not a large-sieve moment estimate. -/
theorem oaiNNS_norm_sq_exact {α : Type*}
    (s : Finset α) (a : α → ℂ) :
    ‖∑ i ∈ s, a i‖ ^ 2 =
      oaiNNSCoAll s a - oaiNNSDivAll s a := by
  rw [nnsPhi_norm, nnsPhiMinus_sum, nnsPhiPlus_sum]
  rw [nnsPhi_sum_eq_up_sub_down s a nnsPhiMinus,
      nnsPhi_sum_eq_up_sub_down s a nnsPhiPlus]
  unfold oaiNNSCoAll oaiNNSDivAll
  ring

/-- Source carrier for all OAI subsets plus the separately signed
    original principal signal. -/
def oaiGaussianSignalCarrier (K : ℕ) :
    Finset (Option (Finset (Fin K))) :=
  insert none (((Finset.univ : Finset (Fin K)).powerset).image some)

/-- A_J is the ENTIRE OAI completed dyadic sum and Mellin height
    integral, not a preintegrated coefficient. -/
def oaiGaussianSignalAtom {K : ℕ}
    (A : Finset (Fin K) → ℂ) (principal : ℂ)
    (l : Option (Finset (Fin K))) : ℂ :=
  match l with
  | none => -principal
  | some J => A J

theorem oaiGaussianSignalCarrier_sum {K : ℕ}
    (A : Finset (Fin K) → ℂ) (principal : ℂ) :
    (∑ l ∈ oaiGaussianSignalCarrier K,
      oaiGaussianSignalAtom A principal l) =
      (∑ J ∈ (Finset.univ : Finset (Fin K)).powerset, A J) -
        principal := by
  classical
  unfold oaiGaussianSignalCarrier
  have hnone : (none : Option (Finset (Fin K))) ∉
      ((Finset.univ : Finset (Fin K)).powerset).image some := by simp
  rw [Finset.sum_insert hnone]
  rw [Finset.sum_image (fun a _ b _ hab => Option.some.inj hab)]
  simp [oaiGaussianSignalAtom]
  ring

/-- Actual OpenAI/GaussianSubset source term, retaining exact
    theta–Poisson row weights, completed masks, Hecke phases,
    Gaussian test density and vertical slot log phases. -/
def oaiOriginalGaussianSubsetIntegrated {K : ℕ}
    (V : Finset (Fin K) → SchwartzMap ℝ ℂ)
    (hV : ∀J, HasCompactSupport (V J : ℝ → ℂ))
    (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ → ℂ) (slots : Fin K → Finset O)
    (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ)
    (X Y Z : ℝ) (J : Finset (Fin K)) : ℂ :=
  ∑' j : ℕ, ∫ t : ℝ,
    (∑ p : ((i : Fin K) → {a : O // a ∈ slots i}),
      compensationSubsetWeight η W P (fun i => (p i).val) J *
      compensationRowTest η C W0 W1
        (fun i => (p i).val) J X Y ((2 : ℝ) ^ j) t *
      selectedSlotFactor W P (fun i => (p i).val) J t) *
    gaussianJointDensity (V J) (hV J)
      ((2 : ℝ) ^ j / (Z * ∏ i ∈ Finset.univ \ J, P i)) t

/-- Direct ORIGINAL-TYPE instantiation of the OpenAI theorem
    compensatedPhysicalProbe_common_gaussian, followed by the
    precise signed NNS identity. No synthetic source labels, no
    missing W0/W1 and no factorization of the Gauss sum is assumed. -/
theorem oaiOriginalGaussianSubset_NNS_exact {K : ℕ}
    (W : Fin K → ℝ → ℂ) (M : Fin K → ℝ)
    (hM : ∀i, 0 ≤ M i)
    (hwindow : ∀i y, W i (Real.exp y) ≠ 0 → |y| ≤ M i) :
    ∃ V : Finset (Fin K) → SchwartzMap ℝ ℂ,
      ∃ hV : ∀J, HasCompactSupport (V J : ℝ → ℂ),
      ∀η : HeckeFamily.Character, ∀C : CalibrationData,
        ∀W0 W1 : ℝ → ℂ,
        HasCompactSupport W0 → HasCompactSupport W1 →
        ∀slots : Fin K → Finset O,
        (∀i a, a ∈ slots i → a ≠ 0) →
        ∀P : Fin K → ℝ, (∀i, 0 < P i) →
        ∀X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z →
        ∀principal : ℂ,
          ‖compensatedPhysicalProbe η C W0 W1 slots W P X Y Z -
              principal‖ ^ 2 =
            oaiNNSCoAll (oaiGaussianSignalCarrier K)
              (oaiGaussianSignalAtom
                (oaiOriginalGaussianSubsetIntegrated V hV η C
                  W0 W1 slots W P X Y Z) principal) -
            oaiNNSDivAll (oaiGaussianSignalCarrier K)
              (oaiGaussianSignalAtom
                (oaiOriginalGaussianSubsetIntegrated V hV η C
                  W0 W1 slots W P X Y Z) principal) := by
  obtain ⟨V, hV, _hMoments, hEq⟩ :=
    compensatedPhysicalProbe_common_gaussian W M hM hwindow
  refine ⟨V, hV, ?_⟩
  intro η C W0 W1 hW0 hW1 slots hp P hP X Y Z hX hY hZ principal
  have hOriginal :
      compensatedPhysicalProbe η C W0 W1 slots W P X Y Z =
        ∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
          oaiOriginalGaussianSubsetIntegrated V hV η C
            W0 W1 slots W P X Y Z J := by
    simpa only [oaiOriginalGaussianSubsetIntegrated] using
      (hEq η C W0 W1 hW0 hW1 slots hp P hP X Y Z hX hY hZ)
  rw [hOriginal]
  rw [← oaiGaussianSignalCarrier_sum
    (oaiOriginalGaussianSubsetIntegrated V hV η C W0 W1 slots W P X Y Z)
    principal]
  exact oaiNNS_norm_sq_exact (oaiGaussianSignalCarrier K)
    (oaiGaussianSignalAtom
      (oaiOriginalGaussianSubsetIntegrated V hV η C
        W0 W1 slots W P X Y Z) principal)

end SevenEighths.ProbePhysical
end OAI

#print axioms OAI.SevenEighths.ProbePhysical.oaiNNS_norm_sq_exact
#print axioms OAI.SevenEighths.ProbePhysical.oaiGaussianSignalCarrier_sum
#print axioms OAI.SevenEighths.ProbePhysical.oaiOriginalGaussianSubset_NNS_exact
