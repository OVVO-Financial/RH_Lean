import Mathlib
import «research.VF_MID_FINAL_RAW_CLIPPED_TELESCOPE»
import «research.GLOBAL_RETURNED_CORE_ZERO_TARGET_CLIPPED_HISTORY_CONTRACTION»

/-!
# VF first-bad affine/owner splice: restricted incidence gate

This file continues the merged #887 carrier without ever enlarging the signed
survivor packet to a full physical cell.

The first result is the exact algebraic gate on the restricted live clipped
cell.  If

  C = restricted clipped-base amplitude,
  J = restricted child amplitude,

then the #887 off-diagonal cell is `2*C*J`, and

  2*C*J <= (1/2) * (C+J)^2.

The square on the right is therefore still the square of the *restricted*
amplitude; no subset-versus-whole positivity claim is used.

The second result records that the already-compiled clipped-exit quarter
contraction is stable under an arbitrary finite selection of parents and an
arbitrary retained scalar coefficient on each selected parent.  Thus, once the
restricted incidence square is reindexed parent-by-parent, the survivor
indicator may remain attached all the way through the quarter contraction.

No triangle inequality, prime-density estimate, RH hypothesis, `sorry`,
`admit`, or local axiom is introduced.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The signed completed amplitude of one #887 live restricted cell.  The
child term already carries the fresh-prime sign reversal, so this is exactly
the restricted `C-J` incidence amplitude when the returned-parent amplitude
is written with positive sign. -/
def vfMidSurvivorRestrictedIncidenceAmplitude
    (A B p : ℕ) (sig : Finset ℕ) : ℝ :=
  vfMidSurvivorClippedBaseAmplitude A B p sig +
    vfMidSurvivorChildAmplitude A B p sig

/-- Positive energy obtained only after the exact #887 signed cell has been
kept intact. -/
def vfMidSurvivorRestrictedIncidenceEnergy
    (A B : ℕ) : ℝ :=
  ∑ p ∈ vfMidDyadicPrefixSurvivorLiveFirstOwners A B,
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet B p,
      vfMidSurvivorRestrictedIncidenceAmplitude A B p sig ^ 2

/-- **Restricted half-square gate.**

This is the sharp elementary polarization inequality on the exact #887
amplitudes.  Crucially, the right side is not the full physical incidence
square; the survivor restriction remains inside the square. -/
theorem vfMidSurvivor_liveClippedCell_le_half_restrictedIncidenceSq
    (A B p : ℕ) (sig : Finset ℕ) :
    2 *
        (vfMidSurvivorClippedBaseAmplitude A B p sig *
          vfMidSurvivorChildAmplitude A B p sig) ≤
      (1 / 2 : ℝ) *
        vfMidSurvivorRestrictedIncidenceAmplitude A B p sig ^ 2 := by
  unfold vfMidSurvivorRestrictedIncidenceAmplitude
  nlinarith [sq_nonneg
    (vfMidSurvivorClippedBaseAmplitude A B p sig -
      vfMidSurvivorChildAmplitude A B p sig)]

/-- **Global restricted incidence gate.**

Every live #887 clipped cell is passed through the half-square gate before any
carrier enlargement.  This is the exact legal replacement for the invalid
`restricted sum <= full signed cell` step. -/
theorem vfMidSurvivor_liveClippedCells_le_half_restrictedIncidenceEnergy
    (A B : ℕ) :
    (∑ p ∈ vfMidDyadicPrefixSurvivorLiveFirstOwners A B,
      2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet B p,
        (vfMidSurvivorClippedBaseAmplitude A B p sig *
          vfMidSurvivorChildAmplitude A B p sig)) ≤
      (1 / 2 : ℝ) * vfMidSurvivorRestrictedIncidenceEnergy A B := by
  unfold vfMidSurvivorRestrictedIncidenceEnergy
  calc
    (∑ p ∈ vfMidDyadicPrefixSurvivorLiveFirstOwners A B,
      2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet B p,
        (vfMidSurvivorClippedBaseAmplitude A B p sig *
          vfMidSurvivorChildAmplitude A B p sig)) ≤
      ∑ p ∈ vfMidDyadicPrefixSurvivorLiveFirstOwners A B,
        (1 / 2 : ℝ) *
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet B p,
            vfMidSurvivorRestrictedIncidenceAmplitude A B p sig ^ 2 := by
      apply Finset.sum_le_sum
      intro p _hp
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro sig _hsig
      exact
        vfMidSurvivor_liveClippedCell_le_half_restrictedIncidenceSq
          A B p sig
    _ =
      (1 / 2 : ℝ) *
        ∑ p ∈ vfMidDyadicPrefixSurvivorLiveFirstOwners A B,
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet B p,
            vfMidSurvivorRestrictedIncidenceAmplitude A B p sig ^ 2 := by
      rw [Finset.mul_sum]

/-- The exact #887 survivor square is bounded by its literal diagonal plus one
half of the still-restricted incidence energy.  No absolute value has been
taken on an owner sum. -/
theorem vfMidDyadicPrefixSurvivorMobiusMass_sq_le_diagonal_add_half_restrictedIncidence
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSurvivorMobiusMassReal A B ^ 2 ≤
      lowOwnerGlobalDiagonalPairMassWith B
          (vfMidDyadicPrefixSurvivorSignedSite A B) +
        (1 / 2 : ℝ) * vfMidSurvivorRestrictedIncidenceEnergy A B := by
  rw [vfMidDyadicPrefixSurvivorMobiusMass_sq_eq_diagonal_add_liveClippedCells
    hA hAB hBA]
  exact add_le_add_left
    (vfMidSurvivor_liveClippedCells_le_half_restrictedIncidenceEnergy A B)
    _

/-- Selected-parent clipped outgoing energy with an arbitrary retained scalar
coefficient.  A `0/1` coefficient is the literal survivor indicator after
parent Fubini, but no Boolean assumption is needed. -/
def vfMidSelectedClippedOutgoingEnergy
    (R first : ℕ) (parents : Finset (ℕ × ℕ))
    (coefficient : (ℕ × ℕ) → ℝ) : ℝ :=
  ∑ parent ∈ parents,
    coefficient parent ^ 2 *
      lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy R first parent

/-- Matching selected reciprocal parent energy. -/
def vfMidSelectedReciprocalParentEnergy
    (parents : Finset (ℕ × ℕ))
    (coefficient : (ℕ × ℕ) → ℝ) : ℝ :=
  ∑ parent ∈ parents,
    coefficient parent ^ 2 *
      postRootCovarianceReciprocalPairEnergy parent

/-- **Selection-stable quarter contraction.**

The existing clipped chronology is parentwise.  Therefore an arbitrary
restricted parent set and an arbitrary retained coefficient may be threaded
through it without comparing the restricted energy to a larger signed cell. -/
theorem vfMidSelectedClippedOutgoingEnergy_le_quarter
    {R first : ℕ} (hfirst : first.Prime)
    (parents : Finset (ℕ × ℕ))
    (coefficient : (ℕ × ℕ) → ℝ) :
    vfMidSelectedClippedOutgoingEnergy R first parents coefficient ≤
      (1 / 4 : ℝ) *
        vfMidSelectedReciprocalParentEnergy parents coefficient := by
  unfold vfMidSelectedClippedOutgoingEnergy
    vfMidSelectedReciprocalParentEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro parent _hparent
  have hquarter :=
    lowOwnerGreatestOwnerAboveFirstClippedOutgoingEnergy_le_quarter
      (R := R) hfirst parent
  have hcoeff : 0 ≤ coefficient parent ^ 2 :=
    sq_nonneg (coefficient parent)
  have hscaled :=
    mul_le_mul_of_nonneg_left hquarter hcoeff
  simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

end RHLean.Analysis
