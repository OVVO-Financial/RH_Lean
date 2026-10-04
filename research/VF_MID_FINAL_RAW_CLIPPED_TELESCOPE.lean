import Mathlib
import «research.VF_MID_SUBDOUBLING_SURVIVOR_TO_OWNER_GATE»

/-!
# VF final raw clipped telescope entry

This file pushes the merged #886 restricted survivor packet one exact step
farther into the returned-core first-owner geometry.

For a genuine subdoubling frozen run `A <= R < B <= 2A`, every nonzero
restricted survivor site is already known to be clipped at every live first
owner `p > A`.  Therefore the admitted base part of every arbitrary-site
first-owner cell vanishes identically.

The result below is an exact signed identity: each live first-owner cell of the
#885/#886 restricted site is pure

  clipped-base amplitude * restricted-child amplitude.

No norm, reciprocal reweighting, or cancellation estimate is used.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Restricted #886 signed mass on the clipped p-free base side of one
first-owner/signature cell. -/
def vfMidSurvivorClippedBaseAmplitude
    (A B p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber B p sig,
    vfMidDyadicPrefixSurvivorSignedSite A B a

/-- Restricted #886 signed mass on the p-divisible child side of one
first-owner/signature cell. -/
def vfMidSurvivorChildAmplitude
    (A B p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ b ∈ lowOwnerFirstOwnerChildFiber B p sig,
    vfMidDyadicPrefixSurvivorSignedSite A B b

/-- Every live post-frozen owner has zero restricted survivor mass on the
admitted p-free base fibre. -/
theorem sum_admitted_vfMidSurvivorSignedSite_eq_zero
    {A B p : ℕ} {sig : Finset ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hpA : A < p) :
    (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber B p sig,
      vfMidDyadicPrefixSurvivorSignedSite A B a) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  exact
    vfMidDyadicPrefixSurvivorSignedSite_eq_zero_on_admitted_liveOwner
      hA hAB hBA hpA ha

/-- Hence the complete restricted p-free base sum is literally its clipped
part.  This is the raw signed carrier statement needed before any energy
conversion. -/
theorem sum_base_vfMidSurvivorSignedSite_eq_clipped
    {A B p : ℕ} {sig : Finset ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hpA : A < p) :
    (∑ a ∈ lowOwnerFirstOwnerBaseFiber B p sig,
      vfMidDyadicPrefixSurvivorSignedSite A B a) =
      vfMidSurvivorClippedBaseAmplitude A B p sig := by
  have hsplit :
      (∑ a ∈ lowOwnerFirstOwnerBaseFiber B p sig,
        vfMidDyadicPrefixSurvivorSignedSite A B a) =
        (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber B p sig,
          vfMidDyadicPrefixSurvivorSignedSite A B a) +
        ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber B p sig,
          vfMidDyadicPrefixSurvivorSignedSite A B a := by
    unfold lowOwnerFirstOwnerAdmittedBaseFiber
      lowOwnerFirstOwnerClippedBaseFiber
    simpa only [not_le] using
      (Finset.sum_filter_add_sum_filter_not
        (s := lowOwnerFirstOwnerBaseFiber B p sig)
        (p := fun a => p * a ≤ squareRootEndpoint B)
        (f := vfMidDyadicPrefixSurvivorSignedSite A B)).symm
  rw [hsplit, sum_admitted_vfMidSurvivorSignedSite_eq_zero
    hA hAB hBA hpA]
  simp [vfMidSurvivorClippedBaseAmplitude]

/-- **Pure clipped-cell form of every live #886 first-owner cell.**

Because the restricted site vanishes on admitted parents, its arbitrary-site
base x child Gram has no admitted-base contribution left. -/
theorem lowOwnerFirstOwnerCellGramWith_vfMidSurvivor_eq_clipped_mul_child
    {A B p : ℕ} {sig : Finset ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hpA : A < p) :
    lowOwnerFirstOwnerCellGramWith B p sig
        (vfMidDyadicPrefixSurvivorSignedSite A B) =
      vfMidSurvivorClippedBaseAmplitude A B p sig *
        vfMidSurvivorChildAmplitude A B p sig := by
  unfold lowOwnerFirstOwnerCellGramWith
  calc
    (∑ ab ∈ (lowOwnerFirstOwnerBaseFiber B p sig).product
        (lowOwnerFirstOwnerChildFiber B p sig),
      vfMidDyadicPrefixSurvivorSignedSite A B ab.1 *
        vfMidDyadicPrefixSurvivorSignedSite A B ab.2) =
      ∑ a ∈ lowOwnerFirstOwnerBaseFiber B p sig,
        ∑ b ∈ lowOwnerFirstOwnerChildFiber B p sig,
          vfMidDyadicPrefixSurvivorSignedSite A B a *
            vfMidDyadicPrefixSurvivorSignedSite A B b := by
          simpa only using
            (Finset.sum_product
              (s := lowOwnerFirstOwnerBaseFiber B p sig)
              (t := lowOwnerFirstOwnerChildFiber B p sig)
              (f := fun ab : ℕ × ℕ =>
                vfMidDyadicPrefixSurvivorSignedSite A B ab.1 *
                  vfMidDyadicPrefixSurvivorSignedSite A B ab.2))
    _ =
      (∑ a ∈ lowOwnerFirstOwnerBaseFiber B p sig,
        vfMidDyadicPrefixSurvivorSignedSite A B a) *
      (∑ b ∈ lowOwnerFirstOwnerChildFiber B p sig,
        vfMidDyadicPrefixSurvivorSignedSite A B b) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.mul_sum]
    _ =
      vfMidSurvivorClippedBaseAmplitude A B p sig *
        vfMidSurvivorChildAmplitude A B p sig := by
          rw [sum_base_vfMidSurvivorSignedSite_eq_clipped
            hA hAB hBA hpA]
          rfl

/-- **Global raw clipped entrance.**

After removing the diagonal, the complete #885/#886 survivor square is a sum
only of clipped-base x restricted-child first-owner cells with live owners
strictly above the frozen cutoff. -/
theorem vfMidDyadicPrefixSurvivorMobiusMass_sq_eq_diagonal_add_liveClippedCells
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSurvivorMobiusMassReal A B ^ 2 =
      lowOwnerGlobalDiagonalPairMassWith B
          (vfMidDyadicPrefixSurvivorSignedSite A B) +
        ∑ p ∈ vfMidDyadicPrefixSurvivorLiveFirstOwners A B,
          2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet B p,
            (vfMidSurvivorClippedBaseAmplitude A B p sig *
              vfMidSurvivorChildAmplitude A B p sig) := by
  rw [vfMidDyadicPrefixSurvivorMobiusMass_sq_eq_diagonal_add_liveFirstOwners
    hA hAB hBA]
  apply congrArg
    (fun x : ℝ =>
      lowOwnerGlobalDiagonalPairMassWith B
        (vfMidDyadicPrefixSurvivorSignedSite A B) + x)
  apply Finset.sum_congr rfl
  intro p hp
  have hpA : A < p :=
    (Finset.mem_filter.mp hp).2
  have hpPrime : p.Prime :=
    (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  rw [lowOwnerGlobalFirstOwnerPairMassWith_eq_two_sum_cells
      hpPrime (vfMidDyadicPrefixSurvivorSignedSite A B)]
  congr 1
  apply Finset.sum_congr rfl
  intro sig _hsig
  rw [lowOwnerFirstOwnerCellGramWith_vfMidSurvivor_eq_clipped_mul_child
    hA hAB hBA hpA]

end RHLean.Analysis
