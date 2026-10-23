import «research.oai_434.VF919OriginalDetectorSignedNNS»
import «research.VF_919_RESONANT_FIBER_NNS_RECOMBINATION_20261022»

/-!
# Exact resonant fiber grouping of ORIGINAL finite OAI ideal columns

Fiber M H Label Slot, finiteColumns (fiberPool F selected), the exact
fiberCoefficient * masked rowWeight, D_U and detector_row_eq_source
are all the original OpenAI Lean declarations.

For any proposed class map Ideal O -> kappa, this is exact group-before-
squaring algebra on the ACTUAL admitted ideal columns. Identification
of those classes with the original global Hecke resonance relation is
a still-open arithmetic phase-admission theorem; a rowwise value 1
at one u does not suffice to declare a globally trivial character.

This finite detector source is distinct from the Gaussian-integrated
source including the principal correction; neither is conflated here.
-/

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource
open CenteredMomentRestrictedEnergy CenteredMomentNaturalFixedRaySource
open ProbeHighRowFamily HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial
open HeckeDetectorDyadicProfiles CenteredMomentPrimeSlot
open CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
open RHLean.Analysis RHLean.Proof

local notation "O" => HeckeFamily.O
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ}
variable {Label Slot κ : Type*}
variable {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- SOURCE-TYPED regrouping with actual OAI ideal labels and norm D_U.
    It does not require a guessed relative sextic character, but its
    classOf partition has NOT been certified as the true resonance. -/
theorem original_detector_resonant_fiber_recombination
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (eta : Character) (selected : Finset Slot)
    (j k : ℕ) (sigma t : ℝ) (hU : 0 < U)
    (classOf : Ideal O → κ) :
    let Q := finiteColumns (fiberPool F selected)
    let D := originalDetectorNNSScale F selected
    let atom := originalDetectorNNSAtom F eta selected j k sigma t
    (∑ u ∈ F.rows,
        ‖detectorPositiveRow F eta selected j k sigma t u‖ ^ 2) =
      resonantFiberEnergy F.rows Q classOf atom (fun _ => 1 / D) +
      nonresonantInterfiberGram F.rows Q classOf atom
        (fun _ => 1 / D) := by
  classical
  dsimp only
  let Q := finiteColumns (fiberPool F selected)
  let D := originalDetectorNNSScale F selected
  let atom := originalDetectorNNSAtom F eta selected j k sigma t
  have hD : 0 < D := by
    dsimp [D, originalDetectorNNSScale]
    apply mul_pos
    · exact mul_pos (Real.rpow_pos_of_pos hU _)
        (Real.rpow_pos_of_pos hU _)
    · exact Finset.prod_pos (fun _ _ => Real.rpow_pos_of_pos hU _)
  have hrow (u : FreeRow) :
      ‖detectorPositiveRow F eta selected j k sigma t u‖ ^ 2 =
        (1 / D) * ‖∑ I ∈ Q, atom u I‖ ^ 2 := by
    rw [detector_row_eq_source F eta selected j k sigma t u hU]
    change
      ‖(Real.sqrt D : ℂ)⁻¹ * (∑ I ∈ Q, atom u I)‖ ^ 2 =
        (1 / D) * ‖∑ I ∈ Q, atom u I‖ ^ 2
    rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hD]
    ring
  calc
    (∑ u ∈ F.rows,
        ‖detectorPositiveRow F eta selected j k sigma t u‖ ^ 2) =
      ∑ u ∈ F.rows,
        (1 / D) * ‖∑ I ∈ Q, atom u I‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hrow u
    _ = resonantFiberEnergy F.rows Q classOf atom (fun _ => 1 / D) +
        nonresonantInterfiberGram F.rows Q classOf atom
          (fun _ => 1 / D) :=
          resonant_fiber_recombination_eq F.rows Q classOf atom
            (fun _ => 1 / D)

end SevenEighths.CenteredMomentDetectorPlainFiberSource

#print axioms SevenEighths.CenteredMomentDetectorPlainFiberSource.original_detector_resonant_fiber_recombination

end
end OAI
