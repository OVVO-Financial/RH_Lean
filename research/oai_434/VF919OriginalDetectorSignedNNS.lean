import OAI.NumberTheory.DirichletL.Moments.DetectorPlainFiberSource
import «research.VF_919_ACTUAL_WEIGHTED_NNS_COVARIANCE_KERNEL_20261021»

/-!
# Real OAI finite Hecke detector columns -> exact signed NNS covariance

This is NOT an opaque or assumed coefficient adapter. It directly uses
the ORIGINAL compiled OAI theorem `detector_row_eq_source`, which
includes the exact original labelled ideal pool `fiberPool`, source
coefficient `fiberCoefficient`, and row mask `rowWeight`.

The normalization is the ORIGINAL
  D_U = (U^F.m)*(U^F.m)*prod_{s in selected} U^(F.widths s).
No row-count normalization, absolute-value-first bound, phase deletion,
or assumption of source equality is allowed.

The result is an exact pointwise and all-rows NNS Co-Div coordinate
correspondence for the detector polynomial source. It is logically
separate from the integrated GaussianSubset source in PR #1004; an
intertwining lemma would be needed to identify both sources termwise.
-/

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
open RHLean.Analysis RHLean.Proof

local notation "O" => HeckeFamily.O
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
variable {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- Original scale, not the row count. -/
def originalDetectorNNSScale
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) : ℝ :=
  (U ^ F.m) * (U ^ F.m) *
    ∏ s ∈ selected, U ^ (F.widths s)

/-- Full original ideal-column row coefficient: the Hecke phase and
    fixed mask are present exactly once. -/
def originalDetectorNNSAtom
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (selected : Finset Slot)
    (j k : ℕ) (σ t : ℝ) (u : FreeRow)
    (I : Ideal O) : ℂ :=
  fiberCoefficient F η selected j k σ t I *
    CenteredMomentHeckeExpansion.rowWeight η fixedBadMask 1 u.val 0 I

/-- Independently proved ORIGINAL-OAI source-to-NNS, with no source
    approximation and no missing labelled ideals. -/
theorem original_detector_row_exact_signed_NNS
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (selected : Finset Slot)
    (j k : ℕ) (σ t : ℝ) (hU : 0 < U) :
    let Q := finiteColumns (fiberPool F selected)
    let D := originalDetectorNNSScale F selected
    let atom := originalDetectorNNSAtom F η selected j k σ t
    (∑ u ∈ F.rows,
      ‖detectorPositiveRow F η selected j k σ t u‖ ^ 2) =
    (∑ u ∈ F.rows, (1 / D) *
      ((zeroTargetCoPartialGram Q
          (fun I => (stableFarComplexToRealPair (atom u I)).1) +
        zeroTargetCoPartialGram Q
          (fun I => (stableFarComplexToRealPair (atom u I)).2)) / 2)) -
    (∑ u ∈ F.rows, (1 / D) *
      ((zeroTargetDivergentGram Q
          (fun I => (stableFarComplexToRealPair (atom u I)).1) +
        zeroTargetDivergentGram Q
          (fun I => (stableFarComplexToRealPair (atom u I)).2)) / 2)) := by
  classical
  dsimp only
  let Q := finiteColumns (fiberPool F selected)
  let D := originalDetectorNNSScale F selected
  let atom := originalDetectorNNSAtom F η selected j k σ t
  have hD : 0 < D := by
    dsimp [D, originalDetectorNNSScale]
    apply mul_pos
    · exact mul_pos (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _)
    · exact Finset.prod_pos (fun _ _ => Real.rpow_pos_of_pos hU _)
  have hrow (u : FreeRow) :
      ‖detectorPositiveRow F η selected j k σ t u‖ ^ 2 =
        (1 / D) * ‖∑ I ∈ Q, atom u I‖ ^ 2 := by
    rw [detector_row_eq_source F η selected j k σ t u hU]
    change
      ‖(Real.sqrt D : ℂ)⁻¹ * (∑ I ∈ Q, atom u I)‖ ^ 2 =
        (1 / D) * ‖∑ I ∈ Q, atom u I‖ ^ 2
    rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hD]
    ring
  calc
    (∑ u ∈ F.rows, ‖detectorPositiveRow F η selected j k σ t u‖ ^ 2) =
        (∑ u ∈ F.rows, (1 / D) *
          ‖∑ I ∈ Q, atom u I‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro u _
        exact hrow u
    _ = _ := RHLean.Analysis.vf919NormalizedColumnSource_NNSCovariance
      F.rows Q atom D

end SevenEighths.CenteredMomentDetectorPlainFiberSource

#print axioms SevenEighths.CenteredMomentDetectorPlainFiberSource.original_detector_row_exact_signed_NNS

end OAI
