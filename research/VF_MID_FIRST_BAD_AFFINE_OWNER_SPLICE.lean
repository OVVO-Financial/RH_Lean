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


/-! ## Exact affine seat mass = already-processed least-owner sector -/

/-- Least-prime owners which have already acted when the square run is frozen
through \`A\`.  The fixed parity owner 2 is excluded by the ambient late-owner
set; the additional filter keeps exactly \`2 < p <= A\`. -/
def vfMidFrozenProcessedOwnerPrimes (A R : ℕ) : Finset ℕ :=
  (vfMidSquareBandLateOwnerPrimes 2 R).filter fun p => p ≤ A

/-- The complement of the already-processed owners inside the full odd-owner
set is exactly the live owner set strictly above the frozen cutoff. -/
theorem vfMidLateOwnerPrimes_two_filter_not_processed_eq_live
    {A R : ℕ} (hA : 2 ≤ A) :
    (vfMidSquareBandLateOwnerPrimes 2 R).filter (fun p => ¬ p ≤ A) =
      vfMidSquareBandLateOwnerPrimes A R := by
  ext p
  simp only [Finset.mem_filter, mem_vfMidSquareBandLateOwnerPrimes]
  constructor
  · rintro ⟨⟨hpOwner, h2p⟩, hpNot⟩
    exact ⟨hpOwner, lt_of_not_ge hpNot⟩
  · rintro ⟨hpOwner, hAp⟩
    refine ⟨⟨hpOwner, ?_⟩, Nat.not_le_of_gt hAp⟩
    omega

/-- **Owner partition at the frozen cutoff.**

The complete odd least-owner census is the disjoint sum of the owners already
processed by the frozen wheel and the owners which remain live above it. -/
theorem vfMidLateOwnerCards_two_eq_processed_add_live
    {A R : ℕ} (hA : 2 ≤ A) :
    (∑ p ∈ vfMidSquareBandLateOwnerPrimes 2 R,
        (vfMidSquareBandCompositeOwner R p).card) =
      (∑ p ∈ vfMidFrozenProcessedOwnerPrimes A R,
        (vfMidSquareBandCompositeOwner R p).card) +
      ∑ p ∈ vfMidSquareBandLateOwnerPrimes A R,
        (vfMidSquareBandCompositeOwner R p).card := by
  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not
      (s := vfMidSquareBandLateOwnerPrimes 2 R)
      (p := fun p : ℕ => p ≤ A)
      (f := fun p => (vfMidSquareBandCompositeOwner R p).card)).symm
  have hcomp :=
    vfMidLateOwnerPrimes_two_filter_not_processed_eq_live
      (A := A) (R := R) hA
  unfold vfMidFrozenProcessedOwnerPrimes
  rw [hcomp] at hsplit
  exact hsplit

/-- **The apparent removed-seat population is exactly the processed-owner
population.**

Prime seats survive every prefix.  Thus the seats lost when the parity wheel
is refined from owner 2 through owner A are precisely the composite seats whose
unique least-prime owner lies in \`2 < p <= A\`. -/
theorem vfMidSquarePrefixWheelSurvivors_card_add_processedOwnerCards_eq_root
    {A R : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R) :
    (vfMidSquarePrefixWheelSurvivors A R).card +
        (∑ p ∈ vfMidFrozenProcessedOwnerPrimes A R,
          (vfMidSquareBandCompositeOwner R p).card) =
      R := by
  have hR : 2 ≤ R := by omega
  have hparity :=
    vfMidOddActualComposite_card_add_primeSupply R hR
  have hfrozen :=
    vfMidSquarePrefixWheelSurvivors_card_eq_prime_add_prefixComposite
      A R hR hAR
  have hall :=
    vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards
      2 R hR
  have hlive :=
    vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards
      A R hR
  have hsplit :=
    vfMidLateOwnerCards_two_eq_processed_add_live
      (A := A) (R := R) (by omega : 2 ≤ A)
  omega

/-- Real-valued form of the processed-owner population identity. -/
theorem vfMid_root_sub_prefixSurvivorCard_eq_processedOwnerCards
    {A R : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R) :
    (R : ℝ) - ((vfMidSquarePrefixWheelSurvivors A R).card : ℝ) =
      ∑ p ∈ vfMidFrozenProcessedOwnerPrimes A R,
        ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
  have hcount :=
    vfMidSquarePrefixWheelSurvivors_card_add_processedOwnerCards_eq_root
      hA hAR
  have hcountR :
      ((vfMidSquarePrefixWheelSurvivors A R).card : ℝ) +
          (∑ p ∈ vfMidFrozenProcessedOwnerPrimes A R,
            ((vfMidSquareBandCompositeOwner R p).card : ℝ)) =
        (R : ℝ) := by
    exact_mod_cast hcount
  linarith

/-- **Affine-to-owner weld for one square block.**

The nonnegative "removed-seat" term from the #885 packet is not an external
deterministic remainder.  It is exactly the VF seat weight carried by the
least-prime owner fibres which have already been processed before the frozen
post-A survivor sector begins. -/
theorem vfMidPrefixRemovedSeatMass_eq_processedOwnerCharges
    {A R : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R) :
    vfMidOddFractionalPrimeSeatWeight R *
        ((R : ℝ) - ((vfMidSquarePrefixWheelSurvivors A R).card : ℝ)) =
      ∑ p ∈ vfMidFrozenProcessedOwnerPrimes A R,
        vfMidOddFractionalPrimeSeatWeight R *
          ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
  rw [← Finset.mul_sum]
  rw [vfMid_root_sub_prefixSurvivorCard_eq_processedOwnerCards hA hAR]

/-- Signed survivor part of the frozen run, still before any absolute value. -/
def vfMidDyadicFrozenSurvivorSeatCharge (A B : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    vfMidSubdoublingPrefixSurvivorChargeSum A R

/-- The affine seat population which was removed by freezing the wheel through
A, now written on its exact already-processed least-owner fibres. -/
def vfMidDyadicProcessedOwnerSeatCharge (A B : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ p ∈ vfMidFrozenProcessedOwnerPrimes A R,
      vfMidOddFractionalPrimeSeatWeight R *
        ((vfMidSquareBandCompositeOwner R p).card : ℝ)

/-- **Exact two-sector affine/owner reassembly of the full VF seat run.**

This is the missing affine bookkeeping identity.  The complete #885 signed
run is *not* survivor charge plus an opaque positive correction: it is the
signed post-A survivor sector plus the literal least-owner sector \`2 < p <= A\`.
No estimate, norm, or triangle inequality occurs. -/
theorem vfMidOddRunSeatMass_eq_frozenSurvivor_add_processedOwnerCharge
    {A B : ℕ} (hA : 3 ≤ A) (hBA : B ≤ 2 * A) :
    vfMidOddRunSeatMass A B =
      vfMidDyadicFrozenSurvivorSeatCharge A B +
        vfMidDyadicProcessedOwnerSeatCharge A B := by
  unfold vfMidOddRunSeatMass
    vfMidDyadicFrozenSurvivorSeatCharge
    vfMidDyadicProcessedOwnerSeatCharge
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R hR
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hRB : R < B := (Finset.mem_Ico.mp hR).2
  have hRlt : R < 2 * A := hRB.trans_le hBA
  rw [vfMidOddBlockSeatMass_eq_trackingDefect R (by omega : 2 ≤ R)]
  rw [vfMidOddCompositeTrackingDefect_eq_prefixSurvivorCharge_add_removedSeats
    hA hAR hRlt]
  rw [vfMidPrefixRemovedSeatMass_eq_processedOwnerCharges hA hAR]

/-- **First-bad trigger in exact low-owner + high-survivor currency.**

Both signs of a first escape now enter one literal owner decomposition.  The
positive affine contribution is no longer external to the owner graph. -/
theorem vfMidActualPrimeFirstBadAt_forces_twoSectorOwnerTrigger
    {K : ℝ} {A B : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 3 ≤ A) (hABlt : A < B) (hBA : B ≤ 2 * A) :
    (K * vfMidSyntheticRadialScale B -
          K * vfMidSyntheticRadialScale A <
        vfMidDyadicFrozenSurvivorSeatCharge A B +
          vfMidDyadicProcessedOwnerSeatCharge A B) ∨
    (vfMidDyadicFrozenSurvivorSeatCharge A B +
          vfMidDyadicProcessedOwnerSeatCharge A B <
        K * vfMidSyntheticRadialScale A -
          K * vfMidSyntheticRadialScale B) := by
  have htrigger :=
    vfMidActualPrimeFirstBadAt_forces_signedSeatRunTrigger
      hfirst hA hABlt hBA
  rw [vfMidOddRunSeatMass_eq_frozenSurvivor_add_processedOwnerCharge
    hA hBA] at htrigger
  exact htrigger


/-! ## Processed-owner children land below a fixed prior anchor -/

/-- **Processed-owner reciprocal children are prior-anchor states.**

Fix a run ending before \`B\` and an anchor \`A\` with \`B^2 <= 3*A^2\`.
Every owner in the already-processed sector satisfies \`3 <= p\`.  Hence
stripping that owner from any composite in any block \`R < B\` sends the child
strictly below \`A^2\`.

This is the low-owner companion to #887's post-frozen theorem that every live
survivor child has square-root scale below \`A\`. -/
theorem vfMidProcessedOwnerChild_lt_anchorSquare
    {A B R p m : ℕ}
    (hRB : R < B)
    (hBsq : B ^ 2 ≤ 3 * A ^ 2)
    (hp : p ∈ vfMidFrozenProcessedOwnerPrimes A R)
    (hm : m ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    m < A ^ 2 := by
  rcases Finset.mem_filter.mp hp with ⟨hpLate, _hpA⟩
  have hpGt2 : 2 < p :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hpLate).2
  have hp3 : 3 ≤ p := by omega
  rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
  rcases vfMidSquareBandCompositeOwner_mem hn with ⟨hnComp, _hmin⟩
  rcases Finset.mem_filter.mp hnComp with ⟨hnBand, _hnNotPrime⟩
  have hnHigh : n < (R + 1) ^ 2 :=
    (Finset.mem_Ioo.mp hnBand).2
  have hRB' : R + 1 ≤ B := by omega
  have hsq : (R + 1) ^ 2 ≤ B ^ 2 :=
    Nat.pow_le_pow_left hRB' 2
  have hmul : p * (n / p) = n :=
    vfMidSquareBandCompositeOwner_mul_div hn
  have h3m : 3 * (n / p) ≤ n := by
    calc
      3 * (n / p) ≤ p * (n / p) :=
        Nat.mul_le_mul_right (n / p) hp3
      _ = n := hmul
  omega

end RHLean.Analysis
