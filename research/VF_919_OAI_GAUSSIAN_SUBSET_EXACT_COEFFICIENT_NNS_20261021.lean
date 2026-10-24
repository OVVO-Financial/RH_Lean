import Mathlib
import «research.VF_919_ACTUAL_WEIGHTED_NNS_COVARIANCE_KERNEL_20261021»

/-!
# Exact GaussianSubset coefficient splitting and original-sign NNS moment

This is a FINITE, fully indexed algebraic specialization of the EXACT
coefficient layout in OAI Detector/GaussianSubset.lean:
  compensationSubsetWeight * compensationRowTest * selectedSlotFactor.

The coefficient below retains (-1)^|J|, selected ideal-norm product
to the -3/2 power, conjugated character, all slot windows, all
vertical log phases, and the COMPLETE complex physical row core.
The row core must be instantiated from OAI's physicalRowWeight *
correctedCompletedT * gaussianJointDensity; no source coefficient
may be replaced by a norm-only toy or its absolute value.

This theorem is NOT a Lean import of OAI's type-specialized
compensation_subset_common (the two repositories have distinct Lake
environments). It proves the concrete pointwise finite coefficient
factorization that is used *inside* that original theorem.
The full equality with OAI's completed spectral integrals already
appears upstream in compensation_subset_common and
compensatedPhysicalProbe_common_gaussian.

The signed moment identity retains every NNS same/opposite-sign
interaction. It supplies NO independent analytic power saving.
-/

noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis

open RHLean.Proof

/-- Literal coefficient shape from OAI GaussianCompensation.lean:
    (-1)^|J| * N(p_J)^(-3/2) * star(eta(p_complement)).
    Each q_i is an ORIGINAL elementNorm and each eta_i an ORIGINAL
    elementCoeff. This local factorization uses multiplicativity. -/
def gaussianSubsetOriginalCoefficient {K : ℕ}
    (q : Fin K → ℝ) (eta : Fin K → ℂ)
    (J : Finset (Fin K)) : ℂ :=
  (-1 : ℂ) ^ J.card *
    (((∏ i ∈ J, q i) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
    star (∏ i ∈ (Finset.univ \ J), eta i)

/-- The COMPLETELY INDEXED, unsplit slot/window coefficient,
    before OAI's GaussianSubset.gaussian_slot_window_split.
    The core remains the original complex physical row, with its
    W0/W1, sextic Gauss, mark D, density, and spectral phases. -/
def gaussianOriginalCoefficient {K : ℕ}
    (q : Fin K → ℝ) (eta : Fin K → ℂ)
    (J : Finset (Fin K)) (W phase : Fin K → ℂ)
    (core : ℂ) : ℂ :=
  gaussianSubsetOriginalCoefficient q eta J *
    (∏ i : Fin K, W i) * core *
    (∏ i ∈ (Finset.univ \ J), phase i)

/-- The actual GaussianSubset source coefficient layout:
    subset weight = originalCoefficient * product of J-slot windows;
    selected slot factor = product over complement of (window*logPhase).
    No norm bound or phase averaging is taken. -/
def gaussianReassembledCoefficient {K : ℕ}
    (q : Fin K → ℝ) (eta : Fin K → ℂ)
    (J : Finset (Fin K)) (W phase : Fin K → ℂ)
    (core : ℂ) : ℂ :=
  (gaussianSubsetOriginalCoefficient q eta J *
    (∏ i ∈ J, W i)) * core *
    (∏ i ∈ (Finset.univ \ J), W i * phase i)

/-- Exact splitting of ALL original slot windows, retaining
    multiplicity even if distinct prime ideals have equal norms. -/
theorem gaussianSubset_slot_product_exact {K : ℕ}
    (J : Finset (Fin K)) (W : Fin K → ℂ) :
    (∏ i : Fin K, W i) =
      (∏ i ∈ J, W i) *
      (∏ i ∈ (Finset.univ \ J), W i) := by
  have h := Finset.prod_sdiff (Finset.subset_univ J) (f := W)
  simpa only [mul_comm] using h.symm

/-- THIS is the original pointwise GaussianSubset coefficient
    correspondence at each labelled p,J,physical row,frequency and
    Gaussian dyadic scale. Nothing is discarded or conjugated away. -/
theorem gaussianSubset_coefficient_exact {K : ℕ}
    (q : Fin K → ℝ) (eta : Fin K → ℂ)
    (J : Finset (Fin K)) (W phase : Fin K → ℂ)
    (core : ℂ) :
    gaussianOriginalCoefficient q eta J W phase core =
      gaussianReassembledCoefficient q eta J W phase core := by
  unfold gaussianOriginalCoefficient gaussianReassembledCoefficient
  rw [gaussianSubset_slot_product_exact J W]
  rw [Finset.prod_mul_distrib]
  ring

/-- The *real* carrier keeps distinct subset, selected-prime tuple,
    and physical row labels (including duplicate rational norms). -/
def gaussianLabelCarrier {K : ℕ} {α β : Type*}
    (primeTuples : Finset α) (physicalRows : Finset β) :
    Finset (Finset (Fin K) × (α × β)) :=
  ((Finset.univ : Finset (Fin K)).powerset).product
    (primeTuples.product physicalRows)

/-- A source row with ALL ORIGINAL INDEXED COEFFICIENTS.
    In the OAI specialization:
    q u p i := elementNorm (p i)
    eta u p i := elementCoeff eta (p i)
    W u p i := slotWindow i (elementNorm (p i)/slotScale i)
    phase u J p i := logPhase (-t) (log (elementNorm(p i)/slotScale i))
    core u J p r := physicalRowWeight*correctedCompletedT*jointDensity.
    No ideal labels are compressed into rational norms. -/
def gaussianIndexedOriginalAtom {K : ℕ} {ι α β : Type*}
    (q : ι → α → Fin K → ℝ) (eta : ι → α → Fin K → ℂ)
    (W : ι → α → Fin K → ℂ)
    (phase : ι → Finset (Fin K) → α → Fin K → ℂ)
    (core : ι → Finset (Fin K) → α → β → ℂ)
    (u : ι) (l : Finset (Fin K) × (α × β)) : ℂ :=
  gaussianOriginalCoefficient (q u l.2.1) (eta u l.2.1)
    l.1 (W u l.2.1) (phase u l.1 l.2.1)
    (core u l.1 l.2.1 l.2.2)

def gaussianIndexedReassembledAtom {K : ℕ} {ι α β : Type*}
    (q : ι → α → Fin K → ℝ) (eta : ι → α → Fin K → ℂ)
    (W : ι → α → Fin K → ℂ)
    (phase : ι → Finset (Fin K) → α → Fin K → ℂ)
    (core : ι → Finset (Fin K) → α → β → ℂ)
    (u : ι) (l : Finset (Fin K) × (α × β)) : ℂ :=
  gaussianReassembledCoefficient (q u l.2.1) (eta u l.2.1)
    l.1 (W u l.2.1) (phase u l.1 l.2.1)
    (core u l.1 l.2.1 l.2.2)

/-- Pointwise ALL-INDEXED correspondence, with no sum/density change. -/
theorem gaussianIndexed_atom_exact {K : ℕ} {ι α β : Type*}
    (q : ι → α → Fin K → ℝ) (eta : ι → α → Fin K → ℂ)
    (W : ι → α → Fin K → ℂ)
    (phase : ι → Finset (Fin K) → α → Fin K → ℂ)
    (core : ι → Finset (Fin K) → α → β → ℂ)
    (u : ι) (l : Finset (Fin K) × (α × β)) :
    gaussianIndexedOriginalAtom q eta W phase core u l =
      gaussianIndexedReassembledAtom q eta W phase core u l := by
  exact gaussianSubset_coefficient_exact _ _ _ _ _ _

/-- Full finite sum keeps every phase, original ideal occurrence and
    subset; it is the coefficient-level atom analogue of the sum
    in OAI GaussianSubset.compensation_subset_common. -/
theorem gaussianIndexed_source_sum_exact {K : ℕ} {ι α β : Type*}
    (primeTuples : Finset α) (physicalRows : Finset β)
    (q : ι → α → Fin K → ℝ) (eta : ι → α → Fin K → ℂ)
    (W : ι → α → Fin K → ℂ)
    (phase : ι → Finset (Fin K) → α → Fin K → ℂ)
    (core : ι → Finset (Fin K) → α → β → ℂ) (u : ι) :
    (∑ l ∈ gaussianLabelCarrier primeTuples physicalRows,
       gaussianIndexedOriginalAtom q eta W phase core u l) =
    (∑ l ∈ gaussianLabelCarrier primeTuples physicalRows,
       gaussianIndexedReassembledAtom q eta W phase core u l) := by
  apply Finset.sum_congr rfl
  intro l hl
  exact gaussianIndexed_atom_exact q eta W phase core u l

/-! The NNS layer enters on exactly those ORIGINAL complex atoms,
    BEFORE taking a triangle inequality or collapsing selected subsets. -/

/-- All original source terms remain inside the Co-minus-Div moment.
    The external row weight is the genuine (unnormalized) physical weight
    and can be chosen as 1/D_U or |W(u)|^2 in the appropriate OAI
    coordinate, but MUST NOT be applied twice. -/
theorem gaussianIndexed_signed_NNS_moment_exact
    {K : ℕ} {ι α β : Type*}
    (rows : Finset ι) (primeTuples : Finset α)
    (physicalRows : Finset β)
    (weight : ι → ℝ)
    (q : ι → α → Fin K → ℝ) (eta : ι → α → Fin K → ℂ)
    (W : ι → α → Fin K → ℂ)
    (phase : ι → Finset (Fin K) → α → Fin K → ℂ)
    (core : ι → Finset (Fin K) → α → β → ℂ) :
    (∑ u ∈ rows, weight u *
      ‖∑ l ∈ gaussianLabelCarrier primeTuples physicalRows,
        gaussianIndexedOriginalAtom q eta W phase core u l‖ ^ 2) =
      vf919WeightedPhiCoMass rows
        (gaussianLabelCarrier primeTuples physicalRows) weight
        (fun u l =>
          (stableFarComplexToRealPair
            (gaussianIndexedOriginalAtom q eta W phase core u l)).1)
        (fun u l =>
          (stableFarComplexToRealPair
            (gaussianIndexedOriginalAtom q eta W phase core u l)).2) -
      vf919WeightedPhiDivMass rows
        (gaussianLabelCarrier primeTuples physicalRows) weight
        (fun u l =>
          (stableFarComplexToRealPair
            (gaussianIndexedOriginalAtom q eta W phase core u l)).1)
        (fun u l =>
          (stableFarComplexToRealPair
            (gaussianIndexedOriginalAtom q eta W phase core u l)).2) := by
  classical
  unfold vf919WeightedPhiCoMass vf919WeightedPhiDivMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [vf919FiniteSource_normSq_eq_NNS]
  ring

/-- Even the complete NORMALIZED moment can be rewritten without
    double-counting physical W. D is the original OAI positive scale
    D_U = U^(2*m) * product(U^slotWidth), NOT a row-count surrogate. -/
theorem gaussianIndexed_normalized_signed_NNS_moment_exact
    {K : ℕ} {ι α β : Type*}
    (rows : Finset ι) (primeTuples : Finset α)
    (physicalRows : Finset β) (D : ℝ)
    (q : ι → α → Fin K → ℝ) (eta : ι → α → Fin K → ℂ)
    (W : ι → α → Fin K → ℂ)
    (phase : ι → Finset (Fin K) → α → Fin K → ℂ)
    (core : ι → Finset (Fin K) → α → β → ℂ) :
    (∑ u ∈ rows, (1 / D) *
      ‖∑ l ∈ gaussianLabelCarrier primeTuples physicalRows,
        gaussianIndexedOriginalAtom q eta W phase core u l‖ ^ 2) =
      vf919WeightedPhiCoMass rows
        (gaussianLabelCarrier primeTuples physicalRows) (fun _ => 1 / D)
        (fun u l =>
          (stableFarComplexToRealPair
            (gaussianIndexedOriginalAtom q eta W phase core u l)).1)
        (fun u l =>
          (stableFarComplexToRealPair
            (gaussianIndexedOriginalAtom q eta W phase core u l)).2) -
      vf919WeightedPhiDivMass rows
        (gaussianLabelCarrier primeTuples physicalRows) (fun _ => 1 / D)
        (fun u l =>
          (stableFarComplexToRealPair
            (gaussianIndexedOriginalAtom q eta W phase core u l)).1)
        (fun u l =>
          (stableFarComplexToRealPair
            (gaussianIndexedOriginalAtom q eta W phase core u l)).2) :=
  gaussianIndexed_signed_NNS_moment_exact rows primeTuples physicalRows
    (fun _ => 1 / D) q eta W phase core

/-- Exact analytic-estimate TARGET, with all covariance terms visible:
    a genuine independent OAI uniform moment theorem hBound can be moved
    to the ORIGINAL signed NNS ledger WITHOUT ANY quantitative loss.
    In particular this does not generate an unproved power saving. -/
theorem gaussianIndexed_uniform_signed_moment_of_source_estimate
    {K : ℕ} {ι α β : Type*}
    (rows : Finset ι) (primeTuples : Finset α)
    (physicalRows : Finset β)
    (weight : ι → ℝ)
    (q : ι → α → Fin K → ℝ) (eta : ι → α → Fin K → ℂ)
    (W : ι → α → Fin K → ℂ)
    (phase : ι → Finset (Fin K) → α → Fin K → ℂ)
    (core : ι → Finset (Fin K) → α → β → ℂ)
    (B : ℝ)
    (hBound :
      (∑ u ∈ rows, weight u *
        ‖∑ l ∈ gaussianLabelCarrier primeTuples physicalRows,
          gaussianIndexedOriginalAtom q eta W phase core u l‖ ^ 2) ≤ B) :
      vf919WeightedPhiCoMass rows
        (gaussianLabelCarrier primeTuples physicalRows) weight
        (fun u l =>
          (stableFarComplexToRealPair
            (gaussianIndexedOriginalAtom q eta W phase core u l)).1)
        (fun u l =>
          (stableFarComplexToRealPair
            (gaussianIndexedOriginalAtom q eta W phase core u l)).2) -
      vf919WeightedPhiDivMass rows
        (gaussianLabelCarrier primeTuples physicalRows) weight
        (fun u l =>
          (stableFarComplexToRealPair
            (gaussianIndexedOriginalAtom q eta W phase core u l)).1)
        (fun u l =>
          (stableFarComplexToRealPair
            (gaussianIndexedOriginalAtom q eta W phase core u l)).2) ≤ B := by
  rw [← gaussianIndexed_signed_NNS_moment_exact rows primeTuples
    physicalRows weight q eta W phase core]
  exact hBound


/-! ## The final norm must be taken AFTER full Gaussian-Mellin integration.
     In the OAI specialization, integrated(u,J) is the original complete
     tsum over dyadic j of integrals in height t of the original row test.
     The extra None atom is the ORIGINAL principal signal subtraction.
     No exchange of integrals with squares is used. -/

def gaussianIntegratedSignalCarrier (K : ℕ) :
    Finset (Option (Finset (Fin K))) :=
  insert none (((Finset.univ : Finset (Fin K)).powerset).image some)

def gaussianIntegratedSignalAtom {K : ℕ} {ι : Type*}
    (integrated : ι → Finset (Fin K) → ℂ)
    (principal : ι → ℂ) (u : ι)
    (l : Option (Finset (Fin K))) : ℂ :=
  match l with
  | none => -principal u
  | some J => integrated u J

theorem gaussianIntegrated_source_minus_principal_exact
    {K : ℕ} {ι : Type*}
    (integrated : ι → Finset (Fin K) → ℂ)
    (principal : ι → ℂ) (u : ι) :
    (∑ l ∈ gaussianIntegratedSignalCarrier K,
       gaussianIntegratedSignalAtom integrated principal u l) =
      (∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
         integrated u J) - principal u := by
  classical
  unfold gaussianIntegratedSignalCarrier
  have hnone : (none : Option (Finset (Fin K))) ∉
      ((Finset.univ : Finset (Fin K)).powerset).image some := by simp
  rw [Finset.sum_insert hnone]
  rw [Finset.sum_image (fun a _ b _ hab => Option.some.inj hab)]
  simp [gaussianIntegratedSignalAtom]
  ring

/-- Exact signed source moment on all subset and principal terms.
The cross-height and cross-dyad contributions are retained INSIDE the
complex integrated(u,J) before squaring. -/
theorem gaussianIntegrated_principal_signed_NNS_moment_exact
    {K : ℕ} {ι : Type*} (rows : Finset ι)
    (weight : ι → ℝ)
    (integrated : ι → Finset (Fin K) → ℂ)
    (principal : ι → ℂ) :
    (∑ u ∈ rows, weight u *
      ‖(∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
         integrated u J) - principal u‖ ^ 2) =
      vf919WeightedPhiCoMass rows (gaussianIntegratedSignalCarrier K) weight
        (fun u l => (stableFarComplexToRealPair
          (gaussianIntegratedSignalAtom integrated principal u l)).1)
        (fun u l => (stableFarComplexToRealPair
          (gaussianIntegratedSignalAtom integrated principal u l)).2) -
      vf919WeightedPhiDivMass rows (gaussianIntegratedSignalCarrier K) weight
        (fun u l => (stableFarComplexToRealPair
          (gaussianIntegratedSignalAtom integrated principal u l)).1)
        (fun u l => (stableFarComplexToRealPair
          (gaussianIntegratedSignalAtom integrated principal u l)).2) := by
  classical
  unfold vf919WeightedPhiCoMass vf919WeightedPhiDivMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← gaussianIntegrated_source_minus_principal_exact integrated principal u]
  rw [vf919FiniteSource_normSq_eq_NNS]
  ring

/-- This is a genuine uniform signed second-moment deduction from the
ORIGINAL OAI pointwise high-row norm estimate hOAI. It does not generate
a better exponent than hOAI; no arithmetic power saving is assumed. -/
theorem gaussianIntegrated_uniform_signed_NNS_of_original_bound
    {K : ℕ} {ι : Type*} (rows : Finset ι)
    (weight : ι → ℝ) (hweight : ∀ u ∈ rows, 0 ≤ weight u)
    (integrated : ι → Finset (Fin K) → ℂ)
    (principal : ι → ℂ) (B : ι → ℝ)
    (hOAI : ∀ u ∈ rows,
      ‖(∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
         integrated u J) - principal u‖ ≤ B u) :
      vf919WeightedPhiCoMass rows (gaussianIntegratedSignalCarrier K) weight
        (fun u l => (stableFarComplexToRealPair
          (gaussianIntegratedSignalAtom integrated principal u l)).1)
        (fun u l => (stableFarComplexToRealPair
          (gaussianIntegratedSignalAtom integrated principal u l)).2) -
      vf919WeightedPhiDivMass rows (gaussianIntegratedSignalCarrier K) weight
        (fun u l => (stableFarComplexToRealPair
          (gaussianIntegratedSignalAtom integrated principal u l)).1)
        (fun u l => (stableFarComplexToRealPair
          (gaussianIntegratedSignalAtom integrated principal u l)).2) ≤
        ∑ u ∈ rows, weight u * (B u) ^ 2 := by
  rw [← gaussianIntegrated_principal_signed_NNS_moment_exact
    rows weight integrated principal]
  apply Finset.sum_le_sum
  intro u hu
  have h := hOAI u hu
  have hn : 0 ≤ ‖(∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
    integrated u J) - principal u‖ := norm_nonneg _
  have hb : 0 ≤ B u := le_trans hn h
  have hsq :
      ‖(∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
        integrated u J) - principal u‖ ^ 2 ≤ (B u) ^ 2 := by
    nlinarith
  exact mul_le_mul_of_nonneg_left hsq (hweight u hu)

end RHLean.Analysis

#print axioms RHLean.Analysis.gaussianSubset_slot_product_exact
#print axioms RHLean.Analysis.gaussianSubset_coefficient_exact
#print axioms RHLean.Analysis.gaussianIndexed_atom_exact
#print axioms RHLean.Analysis.gaussianIndexed_source_sum_exact
#print axioms RHLean.Analysis.gaussianIndexed_signed_NNS_moment_exact
#print axioms RHLean.Analysis.gaussianIndexed_normalized_signed_NNS_moment_exact
#print axioms RHLean.Analysis.gaussianIndexed_uniform_signed_moment_of_source_estimate

#print axioms RHLean.Analysis.gaussianIntegrated_source_minus_principal_exact
#print axioms RHLean.Analysis.gaussianIntegrated_principal_signed_NNS_moment_exact
#print axioms RHLean.Analysis.gaussianIntegrated_uniform_signed_NNS_of_original_bound
