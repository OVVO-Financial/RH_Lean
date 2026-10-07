import Mathlib
import «research.VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE»
import «research.VF_MID_FAN_ESCAPE_CAPACITY_BILLS»

/-!
# VF dyadic continuation capacitor

This file globalizes the #903 six-sector greatest-owner continuation identity
over an actual contiguous dyadic square-root run `[A,B)`.

No new carrier is introduced.  The outer indices are exactly the existing
global owner indices at each endpoint scale:

* `R ∈ Finset.Ico A B`;
* `p ∈ primesUpTo (squareRootEndpoint R)`;
* `sig ∈ lowOwnerFirstOwnerSignatureSet R p`;
* `r ∈ lowOwnerRevealedPrimesAbove R p`.

Inside each `(R,p,sig,r)` fibre, sectors 1--5 are grouped as the local
"capacitor" or safe mass and sector 6 is retained literally as the recursive
continuation mass.  Because the local theorem is an exact signed Fubini
identity for an arbitrary weight, the run-level statement is also an exact
signed identity before any absolute value is taken.

This is the mechanical bridge needed by the capacity-bounce lemmas:

  totalRunMass = safeRunMass + recursiveRunMass.

Consequently, if the recursive run mass is assumed to stay in `[-H,H]`, the
safe mass is forced into the rigid window

  totalRunMass - H <= safeRunMass <= totalRunMass + H.

The theorem does not yet identify the total run mass with the first-bad VF
escape bill, nor does it yet regroup the recursive sector into contiguous
lower child runs.  Those are the two remaining source/reassembly splices.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Arbitrary signed weight on one greatest-owner pair in one endpoint cell. -/
abbrev VFMidContinuationRunPairWeight :=
  ℕ → ℕ → Finset ℕ → ℕ → (ℕ × ℕ) → ℝ

/-- Positive greatest-owner fibre mass for an arbitrary signed weight. -/
def lowOwnerFirstOwnerGreatestOwnerPositiveFiberMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : VFMidContinuationRunPairWeight) : ℝ :=
  ∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r,
    f R p sig r mn

/-- Sectors 1--5 of the #903 continuation partition, still at one
greatest-owner fibre and with exact signs retained. -/
def lowOwnerFirstOwnerGreatestOwnerSafeContinuationFiberMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : VFMidContinuationRunPairWeight) : ℝ :=
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerCurrentFamilyPairFiber R p sig r,
      f R p sig r mn) +
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerEqualParentPairFiber R p sig r,
      f R p sig r mn) +
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerClippedPairFiber R p sig r,
      f R p sig r mn) +
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerLowerFamilyPairFiber R p sig r,
      f R p sig r mn) +
  (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerLowerTerminalPairFiber R p sig r,
      f R p sig r mn)

/-- Sector 6 of the #903 continuation partition, retained as the unresolved
recursive continuation mass. -/
def lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationFiberMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : VFMidContinuationRunPairWeight) : ℝ :=
  ∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationPairFiber
      R p sig r,
    f R p sig r mn

/-- **Local capacitor equality.**

This is exactly the six-sector theorem with sectors 1--5 grouped and sector 6
left separate. -/
theorem lowOwnerFirstOwnerGreatestOwnerPositiveFiberMass_eq_safe_add_recursive
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : VFMidContinuationRunPairWeight) :
    lowOwnerFirstOwnerGreatestOwnerPositiveFiberMass R p sig r f =
      lowOwnerFirstOwnerGreatestOwnerSafeContinuationFiberMass R p sig r f +
        lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationFiberMass
          R p sig r f := by
  unfold lowOwnerFirstOwnerGreatestOwnerPositiveFiberMass
    lowOwnerFirstOwnerGreatestOwnerSafeContinuationFiberMass
    lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationFiberMass
  rw [sum_lowOwnerFirstOwnerGreatestOwnerPositivePairFiber_eq_sixContinuationSectors]
  ring

/-- Full positive greatest-owner mass over the contiguous endpoint run
`[A,B)`, using exactly the repository's existing first-owner/signature/owner
index sets at each scale. -/
def lowOwnerDyadicGreatestOwnerPositiveRunMass
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
          lowOwnerFirstOwnerGreatestOwnerPositiveFiberMass R p sig r f

/-- Run-level capacitor mass: exact signed sum of continuation sectors 1--5. -/
def lowOwnerDyadicGreatestOwnerSafeContinuationRunMass
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
          lowOwnerFirstOwnerGreatestOwnerSafeContinuationFiberMass
            R p sig r f

/-- Run-level unresolved recursive mass: exact signed sum of sector 6. -/
def lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
          lowOwnerFirstOwnerGreatestOwnerRecursiveContinuationFiberMass
            R p sig r f

/-- **Globalized six-sector Fubini on a complete dyadic run.**

The full positive greatest-owner run mass is exactly sectors 1--5 plus the
recursive sixth sector.  No norm or estimate occurs. -/
theorem lowOwnerDyadicGreatestOwnerPositiveRunMass_eq_safe_add_recursive
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) :
    lowOwnerDyadicGreatestOwnerPositiveRunMass A B f =
      lowOwnerDyadicGreatestOwnerSafeContinuationRunMass A B f +
        lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass A B f := by
  unfold lowOwnerDyadicGreatestOwnerPositiveRunMass
    lowOwnerDyadicGreatestOwnerSafeContinuationRunMass
    lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass
  simp_rw [lowOwnerFirstOwnerGreatestOwnerPositiveFiberMass_eq_safe_add_recursive]
  simp only [Finset.sum_add_distrib]

/-- **Run-level capacitor window.**

If the complete recursive sixth sector of the run is not supercritical, then
the exact signed mass of sectors 1--5 is trapped in the rigid `±H` window
around the total run mass. -/
theorem lowOwnerDyadicGreatestOwnerSafeContinuationRunMass_mem_totalWindow
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) (H : ℝ)
    (hrec :
      |lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass A B f| ≤ H) :
    lowOwnerDyadicGreatestOwnerPositiveRunMass A B f - H ≤
        lowOwnerDyadicGreatestOwnerSafeContinuationRunMass A B f ∧
      lowOwnerDyadicGreatestOwnerSafeContinuationRunMass A B f ≤
        lowOwnerDyadicGreatestOwnerPositiveRunMass A B f + H := by
  exact vfMidSafeMass_mem_parentWindow_of_recursive_abs_le
    (lowOwnerDyadicGreatestOwnerPositiveRunMass_eq_safe_add_recursive A B f)
    hrec

/-- **Positive-side run tripwire.**

Any upper bound on sectors 1--5 which lies more than `H` below the exact
total run mass forces the recursive sixth sector to be positively
supercritical. -/
theorem lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass_gt_of_safeCapacity
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) (cap H : ℝ)
    (hsafe :
      lowOwnerDyadicGreatestOwnerSafeContinuationRunMass A B f ≤ cap)
    (hexcess :
      cap + H < lowOwnerDyadicGreatestOwnerPositiveRunMass A B f) :
    H <
      lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass A B f := by
  exact vfMidRecursiveResidual_gt_of_safeCapacity
    (lowOwnerDyadicGreatestOwnerPositiveRunMass_eq_safe_add_recursive A B f)
    hsafe hexcess

/-- **Negative-side run tripwire.**

Any lower bound on sectors 1--5 which lies more than `H` above the exact
total run mass forces the recursive sixth sector to be negatively
supercritical. -/
theorem lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass_lt_neg_of_safeFloor
    (A B : ℕ) (f : VFMidContinuationRunPairWeight) (floorMass H : ℝ)
    (hsafe :
      floorMass ≤ lowOwnerDyadicGreatestOwnerSafeContinuationRunMass A B f)
    (hover :
      lowOwnerDyadicGreatestOwnerPositiveRunMass A B f + H < floorMass) :
    lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass A B f < -H := by
  exact vfMidRecursiveResidual_lt_neg_of_safeFloor
    (lowOwnerDyadicGreatestOwnerPositiveRunMass_eq_safe_add_recursive A B f)
    hsafe hover

/-! ## Canonical Dirichlet-polarization specialization

The local six-sector continuation is used by the existing owner Fubini in the
Dirichlet polarization currency.  These aliases freeze that actual weight so a
later source theorem cannot silently change currencies. -/

/-- Existing signed pair weight, lifted to the full run index type. -/
def vfMidContinuationDirichletPairWeight :
    VFMidContinuationRunPairWeight :=
  fun R p _sig _r mn =>
    lowOwnerFirstOwnerDirichletPolarizationAtom R p mn

def vfMidDyadicGreatestOwnerPositiveDirichletRunMass
    (A B : ℕ) : ℝ :=
  lowOwnerDyadicGreatestOwnerPositiveRunMass
    A B vfMidContinuationDirichletPairWeight

def vfMidDyadicGreatestOwnerSafeDirichletRunMass
    (A B : ℕ) : ℝ :=
  lowOwnerDyadicGreatestOwnerSafeContinuationRunMass
    A B vfMidContinuationDirichletPairWeight

def vfMidDyadicGreatestOwnerRecursiveDirichletRunMass
    (A B : ℕ) : ℝ :=
  lowOwnerDyadicGreatestOwnerRecursiveContinuationRunMass
    A B vfMidContinuationDirichletPairWeight

theorem vfMidDyadicGreatestOwnerPositiveDirichletRunMass_eq_safe_add_recursive
    (A B : ℕ) :
    vfMidDyadicGreatestOwnerPositiveDirichletRunMass A B =
      vfMidDyadicGreatestOwnerSafeDirichletRunMass A B +
        vfMidDyadicGreatestOwnerRecursiveDirichletRunMass A B := by
  exact lowOwnerDyadicGreatestOwnerPositiveRunMass_eq_safe_add_recursive
    A B vfMidContinuationDirichletPairWeight

end RHLean.Proof
