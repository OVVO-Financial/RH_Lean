import Mathlib
import «research.LOW_OWNER_CHILD_FAR_NORMAL_FORM»
import RHLean.Proof.StableFarAdaptiveLedgerCollapse

/-!
# Correlation-level physical census normal form

The Stokes audit shows that no estimate should be made on individual chronological
prime drops.  The ownerwise synthesis audit then removes every odd owner with
`q^2 >= R`, and the common-base bridge identifies every surviving owner atom
with the negative literal child-far slice.

This file composes those exact identities with the sharpened root correction.
For `R >= 56` the critical correlation is therefore one signed physical census:

  Corr_R
    = - low-q^2 child-far slices
      - owner-two child-far slice
      - stable-far renewal
      - terminal products
      - root correction.

The root correction has norm at most `8R`.  No norm is taken on the four census
populations separately, and no LOW-A estimate is asserted.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The low-owner physical child-far mass, still summed with its native signs. -/
def lowOwnerChildFarCensus (R : ℕ) : ℂ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
      canonicalMoebiusWeight dp.1

/-- The algebraic owner-two child-far slice.  Prime two is base mod-four
geometry in the energy recurrence, but it is an honest owner in the stable-far
largest-prime census and must remain in the scalar identity. -/
def ownerTwoChildFarCensus (R : ℕ) : ℂ :=
  ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R 2,
    canonicalMoebiusWeight dp.1

/-- The complete non-root physical census left after all high-q^2 scalar
cancellations. -/
def lowOwnerPhysicalFarCensus (R : ℕ) : ℂ :=
  -lowOwnerChildFarCensus R - ownerTwoChildFarCensus R -
    stableFarRenewalColumn R - stableFarTerminalProductColumn R

/-- First compose the low-owner scalar normal form with the rough-correlation
root splice, retaining the q-indexed owner atoms. -/
theorem squareRootCanonicalRoughCorrelation_eq_lowQ2Atoms_add_two_sub_chronology_sub_root
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootCanonicalRoughCorrelation R =
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        farFourQ2OwnerSynthesisAtom R q) +
      farFourQ2OwnerSynthesisAtom R 2 -
      stableFarRenewalColumn R - stableFarTerminalProductColumn R -
      frozenTopFarRoughRootCorrection R := by
  have hfar :=
    lowWheelFrozenTopFarResidual_eq_lowQ2Atoms_add_two_sub_renewal_sub_terminal
      R hR
  have hroot :=
    lowWheelFrozenTopFarResidual_eq_roughCorrelation_add_rootCorrection R hR
  linear_combination hfar - hroot

/-- **Correlation-level physical census normal form.**  Every surviving
non-root term is now on the literal stable-far carrier; the Stokes prime index
has disappeared completely. -/
theorem squareRootCanonicalRoughCorrelation_eq_physicalFarCensus_sub_root
    (R : ℕ) (hR : 56 ≤ R) :
    squareRootCanonicalRoughCorrelation R =
      lowOwnerPhysicalFarCensus R - frozenTopFarRoughRootCorrection R := by
  have h :=
    squareRootCanonicalRoughCorrelation_eq_lowQ2Atoms_add_two_sub_chronology_sub_root
      R hR
  have hlow := sum_lowQ2OwnerSynthesisAtoms_eq_neg_childFarSlices R
  have htwoMem : 2 ∈ primesUpTo (R - 1) :=
    mem_primesUpTo.mpr ⟨Nat.prime_two, by omega⟩
  have htwo := farFourQ2OwnerSynthesisAtom_eq_neg_childFarSlice htwoMem
  rw [hlow, htwo] at h
  unfold lowOwnerPhysicalFarCensus lowOwnerChildFarCensus
    ownerTwoChildFarCensus
  exact h

/-- The physical census and the critical correlation differ by only the already
compiled root-scale correction. -/
theorem norm_squareRootCanonicalRoughCorrelation_sub_physicalFarCensus_le_eight_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖squareRootCanonicalRoughCorrelation R - lowOwnerPhysicalFarCensus R‖ ≤
      8 * (R : ℝ) := by
  rw [squareRootCanonicalRoughCorrelation_eq_physicalFarCensus_sub_root R hR]
  have hcorr :
      lowOwnerPhysicalFarCensus R - frozenTopFarRoughRootCorrection R -
          lowOwnerPhysicalFarCensus R =
        -frozenTopFarRoughRootCorrection R := by ring
  rw [hcorr, norm_neg]
  exact norm_frozenTopFarRoughRootCorrection_le_eight_root R hR

end RHLean.Proof
