import OAI.NumberTheory.DirichletL.Moments.DetectorPlainFiberSource
import «research.VF_919_SEXTIC_SECTOR_MEAN_DEFECT_20261022»

/-!
# OAI-typed finite Hecke ideal-pair sector defect

These are ACTUAL original OAI finite detector labels and source atoms:
  Fiber M H Label Slot ...
  FreeRow
  Ideal HeckeFamily.O
  originalDetectorSectorPairAtom F eta selected j k sigma t u I
  originalDetectorNNSScale F selected

There is no asserted phase extractor for an arbitrary Hecke character:
hPhase explicitly states the source-specific sextic decomposition which
a future arithmetic proof MUST certify from the original ideal labels.
OAI's general Hecke coefficient need not be a sixth root of unity.
The exact sixth-sector deficit then follows from NNS realification
without equidistribution, norm-only phases, or lost row masks.

This theorem is an original-TYPED algebraic transport, NOT a proof of
uniform Stage-III saving or of the absent Hecke phase factorization.
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


/-- The ACTUAL OAI finite source coefficient, not a fitted sixth root:
    the same fiberCoefficient times original masked rowWeight as in
    original detector_row_eq_source. -/
def originalDetectorSectorPairAtom
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (eta : Character) (selected : Finset Slot)
    (j k : ℕ) (sigma t : ℝ) (u : FreeRow) (I : Ideal O) : ℂ :=
  fiberCoefficient F eta selected j k sigma t I *
    CenteredMomentHeckeExpansion.rowWeight eta fixedBadMask 1 u.val 0 I

/-- All ACTUAL pair-labelled OAI detector-row columns, at the ORIGINAL
    positive row-normalization scale D_U. The sector coefficient can be
    complex and row-dependent, retaining every Gauss, theta, radial and
    selected-prime factor. hPhase is the precise remaining phase audit. -/
theorem original_detector_ideal_pairs_sextic_sector_defect
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (eta : Character) (selected : Finset Slot)
    (j k : ℕ) (sigma t : ℝ)
    (pairs : Finset (Ideal O × Ideal O))
    (phase : (Ideal O × Ideal O) → FreeRow → Option (Fin 6))
    (coefficient : (Ideal O × Ideal O) → FreeRow → ℂ)
    (zeta : ℂ) (hpow : zeta ^ 6 = 1) (hne : zeta ≠ 1)
    (hPhase : ∀ pair ∈ pairs, ∀ u ∈ F.rows,
      originalDetectorSectorPairAtom F eta selected j k sigma t u pair.1 *
        star (originalDetectorSectorPairAtom F eta selected j k sigma t u pair.2) =
          coefficient pair u *
            sexticPhaseWithZero zeta (phase pair u)) :
    (∑ pair ∈ pairs, ∑ u ∈ F.rows,
      originalDetectorSectorPairAtom F eta selected j k sigma t u pair.1 *
        star (originalDetectorSectorPairAtom F eta selected j k sigma t u pair.2)) /
      (((U ^ F.m) * (U ^ F.m) * ∏ s ∈ selected, U ^ (F.widths s) : ℝ) : ℂ) =
    (∑ pair ∈ pairs,
      sexticSectorDefect zeta
        (sexticWeightedSectorMass F.rows (phase pair) (fun _ => 1)
          (coefficient pair))) /
      (((U ^ F.m) * (U ^ F.m) * ∏ s ∈ selected, U ^ (F.widths s) : ℝ) : ℂ) := by
  congr 1
  have h := sextic_admitted_offdiagonal_Hecke_pair_defect
    F.rows pairs
    (fun pair u =>
      originalDetectorSectorPairAtom F eta selected j k sigma t u pair.1)
    (fun pair u =>
      originalDetectorSectorPairAtom F eta selected j k sigma t u pair.2)
    phase (fun _ => (1 : ℝ)) coefficient zeta hpow hne hPhase
  simpa only [one_mul, Complex.ofReal_one] using h

end SevenEighths.CenteredMomentDetectorPlainFiberSource

#print axioms SevenEighths.CenteredMomentDetectorPlainFiberSource.original_detector_ideal_pairs_sextic_sector_defect

end

end OAI
