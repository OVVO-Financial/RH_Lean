import Mathlib
import «research.GLOBAL_RETURNED_CORE_TOP_TWO_COMPLETED_BRANCH_ASSEMBLY»

/-!
# Top-two Stokes clip composed with the completed branch energy

This file composes two exact statements:

* the post-#791 collapse of the diagonal-retaining signed ledger to the global
  two-toggle Stokes clip plus the zero/one-owner terminal
  (`lowOwnerGlobalPolarizationSignedLedger_eq_topTwoStokesClip_add_terminal`);
* the post-#794 completion of the Dirichlet-incidence branch energy by the
  endpoint correction
  (`lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_branchThresholdEnergy_add_endpointCorrection`).

It asks whether the assembled two-toggle clip is now literally a q² daughter
contraction plus the closed terminal sector.  The answer is **no**, and the
obstruction is exact.

1. **The two-toggle clip removes nothing below the top two owners.**  For every
   first owner other than the two largest primes of the clock, the canonical
   Stokes residual is zero and the top-two normal form *is* the whole signed
   cell telescope `2 * Base * Child`.  Globally,
   `TopTwoClip = FinalStokes - Terminal`.

2. **Exact global normal form.**  The #796 assembly module already proves
   `TopTwoClip = Q^2 + Remainder789 - Terminal`
   (`lowOwnerTopTwoStokesClip_eq_q2Sq_add_signedRemainder_sub_terminal`).
   Writing the post-#789 remainder out,

     TopTwoClip = Q^2 + (G^2 + 2 Q G - D) - Terminal,

   where `Q` is the reciprocal q² Mertens column, `D` the Möbius diagonal and
   `G = M(X_R) - M(R-1)` the top endpoint gap.  Only `Q^2 <= E/4` is a q²
   daughter contraction.  `G` is the top-scale Mertens value itself.

3. **The q²-aware top-two target is a top-endpoint Mertens bound.**  Any
   estimate `TopTwoClip <= B E + C R^2 K` forces
   `G^2 <= (2B + 1/2) E + (2C + 7) R^2 K`.  So the target cannot be
   discharged by q² daughter bookkeeping alone: it contains a quantitative bound
   on the top endpoint gap.

4. **Branch-energy composition at the top coordinate.**  The branch gate is an
   exact identity once its slack is named:

     SignedPolarization(above r)
       = 1/2 (ThresholdEnergy_r + EndpointCorrection_r) - 1/2 Slack_r,
     Slack_r = sum_tau (B_tau + J_tau)^2.

   At the top prime the revealed set is empty, so the left side is the whole
   cell telescope.  There is exactly one revealed fibre: the completed energy
   is the square of one scalar amplitude and the slack is the square of
   another, so the gate reduces to the scalar inequality
   `-2 B J <= 1/2 (B - J)^2`.  For the first owner `2` the completed
   top-coordinate energy is literally `(Q + G)^2`.

No inequality is used except in item 3, and there only after the exact normal
form has been reached.  A finite numerical filter
(`experiments/top_two_branch_gate_composition.py`) reproduces every identity
below and measures the discarded gate slack: summed over first owners it is
several thousand times `R^2` for `56 <= R <= 72`.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open StokesTerminalFrame

attribute [local instance] Classical.propDecidable

/-! ## 1. The two-toggle clip is the whole cell below the top two owners -/

/-- A clock prime other than the top prime lies strictly below it. -/
theorem lowOwner_lt_topPrime_of_ne
    {R p : ℕ} (hR : 56 ≤ R)
    (hpMem : p ∈ primesUpTo (squareRootEndpoint R))
    (hpTop : p ≠ topPrime R hR) :
    p < topPrime R hR := by
  have hle : p ≤ topPrime R hR := Finset.le_max' _ p hpMem
  omega

/-- **Per-cell top-two identity.**  Every signed cell telescope is its
top-two clip plus its own zero/one-owner terminal. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_topTwoStokesClip_add_topTerminal
    {R p : ℕ} (hR : 56 ≤ R)
    (hpMem : p ∈ primesUpTo (squareRootEndpoint R))
    (sig : Finset ℕ) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      lowOwnerFirstOwnerTopTwoStokesClipNormalForm R hR p sig +
        lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig := by
  have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
  rw [lowOwnerFirstOwnerSignedCellTelescope_eq_canonicalStokesBoundary_add_residual hp,
    lowOwnerFirstOwnerCanonicalStokesBoundary_eq_clipBoundary,
    lowOwnerFirstOwnerCanonicalStokesClipBoundary_eq_topTwoNormalForm hR hpMem sig,
    lowOwnerFirstOwnerCanonicalStokesResidual_eq_topTerminalBoundary
      (by omega : 2 ≤ R)]

/-- **The two-toggle clip is not a decrement.**  Below the two largest clock
primes the canonical residual vanishes, so the top-two normal form is the
entire signed cell telescope. -/
theorem lowOwnerFirstOwnerTopTwoStokesClipNormalForm_eq_signedCellTelescope_of_lower
    {R p : ℕ} (hR : 56 ≤ R)
    (hpMem : p ∈ primesUpTo (squareRootEndpoint R))
    (hpTop : p ≠ topPrime R hR) (hpSecond : p ≠ secondPrime R hR)
    (sig : Finset ℕ) :
    lowOwnerFirstOwnerTopTwoStokesClipNormalForm R hR p sig =
      lowOwnerFirstOwnerSignedCellTelescope R p sig := by
  have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
  obtain ⟨rest, hrest⟩ :=
    lowOwnerCanonicalStokesSchedule_eq_top_second_cons_of_lower_owner
      hR hpMem hpTop hpSecond
  have hres :=
    lowOwnerFirstOwnerCanonicalStokesResidual_eq_zero_of_twoOwners
      (sig := sig) (by omega : 2 ≤ R) hrest
  rw [lowOwnerFirstOwnerSignedCellTelescope_eq_canonicalStokesBoundary_add_residual hp,
    hres, add_zero,
    lowOwnerFirstOwnerCanonicalStokesBoundary_eq_clipBoundary,
    lowOwnerFirstOwnerCanonicalStokesClipBoundary_eq_topTwoNormalForm hR hpMem sig]

/-! ## 2. Exact global normal form of the two-toggle clip -/

/-- The #796 normal form with the remainder written out: the only term that is
not a q² column square, the diagonal, or the terminal is the top endpoint gap
`G = M(X_R) - M(R-1)` together with its cross term against the column. -/
theorem lowOwnerCanonicalTopTwoStokesClipNormalForm_eq_q2Sq_add_endpointGap_sub_diagonal_sub_terminal
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalTopTwoStokesClipNormalForm R hR =
      lowOwnerReciprocalMertensColumnReal R ^ 2 +
        (lowOwnerPost789EndpointGapReal R ^ 2 +
          2 * lowOwnerReciprocalMertensColumnReal R *
            lowOwnerPost789EndpointGapReal R) -
        lowOwnerZeroFrequencyMobiusDiagonal R -
          lowOwnerCanonicalSignedStokesTopTerminalBoundary R := by
  rw [lowOwnerTopTwoStokesClip_eq_q2Sq_add_signedRemainder_sub_terminal hR]
  unfold lowOwnerPost789SignedCrossDiagonalRemainder
  ring

/-! ## 3. The q²-aware top-two target is a top-endpoint Mertens bound -/

/-- Quantitative control of the top endpoint gap in the recursive q² currency. -/
def LowOwnerTopEndpointGapQ2EnergyBound (B C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerPost789EndpointGapReal R ^ 2 ≤
      B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- **Necessity.**  Any q²-aware top-two clip estimate already bounds the top
endpoint gap `M(X_R) - M(R-1)` by the recursive q² energy.  Hence the #792
target is not a q² daughter contraction plus the terminal: it contains the
top-scale Mertens estimate.  Only the compiled quarter frame, the diagonal
bound `D <= 3 R^2`, and the terminal bound `<= 4` are used. -/
theorem topEndpointGapQ2EnergyBound_of_topTwoStokesClipQ2EnergyBound
    {B C : ℝ} (hClip : LowOwnerTopTwoStokesClipQ2EnergyBound B C) :
    LowOwnerTopEndpointGapQ2EnergyBound (2 * B + 1 / 2) (2 * C + 7) := by
  intro R K hR hK
  have hclip := hClip R K hR hK
  rw [lowOwnerTopTwoStokesClip_eq_q2Sq_add_signedRemainder_sub_terminal hR] at hclip
  unfold lowOwnerPost789SignedCrossDiagonalRemainder at hclip
  have hterm := lowOwnerCanonicalSignedStokesTopTerminalBoundary_le_four hR
  have hdiag := lowOwnerZeroFrequencyMobiusDiagonal_le_three_root_sq R
  have hQ := lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy R
  have hKone : 1 ≤ K := lowerMertensCriticalEnvelope_one_le (by omega) hK
  have hRreal : (56 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hR2 : (8 : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
  have hR2K : (R : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 * K := by
    have h0 : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hyoung :=
    sq_nonneg
      (lowOwnerPost789EndpointGapReal R +
        2 * lowOwnerReciprocalMertensColumnReal R)
  linarith

/-! ## 4. The branch gate as an exact identity, and its top coordinate -/

/-- The exact amount discarded by the branch gate `-2 B J <= 1/2 (B - J)^2`,
fibre by fibre. -/
def lowOwnerFirstOwnerBranchGateSlack
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
    (lowOwnerFirstOwnerBranchBaseDifferenceAmplitude R p sig tau r +
      lowOwnerFirstOwnerBranchReturnedDifferenceAmplitude R p sig tau r) ^ 2

theorem lowOwnerFirstOwnerBranchGateSlack_nonneg
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    0 ≤ lowOwnerFirstOwnerBranchGateSlack R p sig r := by
  unfold lowOwnerFirstOwnerBranchGateSlack
  apply Finset.sum_nonneg
  intro tau _htau
  exact sq_nonneg _

/-- **Exact branch gate.**  The descending signed polarization is half the
assembled Dirichlet-incidence energy minus half the named slack. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_half_dirichletIncidenceEnergy_sub_half_slack
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) =
      (1 / 2 : ℝ) *
          lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy R p sig r -
        (1 / 2 : ℝ) * lowOwnerFirstOwnerBranchGateSlack R p sig r := by
  rw [lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_neg_two_sum_base_mul_returned
    hp hr hpr]
  unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy
    lowOwnerFirstOwnerBranchGateSlack
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro tau _htau
  rw [lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude_eq_base_sub_returned]
  ring

/-- **Exact completed branch gate.**  The same identity in the post-#794
threshold-plus-endpoint currency. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_half_completedBranchEnergy_sub_half_slack
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) =
      (1 / 2 : ℝ) *
          (lowOwnerFirstOwnerRawParentBranchThresholdEnergy R p sig r +
            lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass R p sig r) -
        (1 / 2 : ℝ) * lowOwnerFirstOwnerBranchGateSlack R p sig r := by
  rw [lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_half_dirichletIncidenceEnergy_sub_half_slack
      hp hr hpr,
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_branchThresholdEnergy_add_endpointCorrection
      hR hp hr]

/-- **Top-coordinate composition.**  For every first owner below the top prime,
the signed cell telescope is exactly half the completed top-coordinate branch
energy minus half the gate slack. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_eq_half_topBranchCompletedEnergy_sub_half_slack
    {R p : ℕ} {sig : Finset ℕ} (hR : 56 ≤ R)
    (hpMem : p ∈ primesUpTo (squareRootEndpoint R))
    (hpTop : p ≠ topPrime R hR) :
    lowOwnerFirstOwnerSignedCellTelescope R p sig =
      (1 / 2 : ℝ) *
          (lowOwnerFirstOwnerRawParentBranchThresholdEnergy
              R p sig (topPrime R hR) +
            lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass
              R p sig (topPrime R hR)) -
        (1 / 2 : ℝ) *
          lowOwnerFirstOwnerBranchGateSlack R p sig (topPrime R hR) := by
  have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
  have ht : (topPrime R hR).Prime := topPrime_prime hR
  have hpt : p < topPrime R hR := lowOwner_lt_topPrime_of_ne hR hpMem hpTop
  have h :=
    lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_half_completedBranchEnergy_sub_half_slack
      (sig := sig) (by omega : 2 ≤ R) hp ht hpt
  rw [lowOwnerRevealedPrimesAbove_topPrime_eq_empty hR,
    lowOwnerFirstOwnerRevealedPolarizationEnergy_empty_eq_signedCellTelescope hp] at h
  exact h

/-- On lower owners the two-toggle clip is the same exact half-energy-minus-
half-slack expression. -/
theorem lowOwnerFirstOwnerTopTwoStokesClipNormalForm_eq_half_topBranchCompletedEnergy_sub_half_slack
    {R p : ℕ} {sig : Finset ℕ} (hR : 56 ≤ R)
    (hpMem : p ∈ primesUpTo (squareRootEndpoint R))
    (hpTop : p ≠ topPrime R hR) (hpSecond : p ≠ secondPrime R hR) :
    lowOwnerFirstOwnerTopTwoStokesClipNormalForm R hR p sig =
      (1 / 2 : ℝ) *
          (lowOwnerFirstOwnerRawParentBranchThresholdEnergy
              R p sig (topPrime R hR) +
            lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass
              R p sig (topPrime R hR)) -
        (1 / 2 : ℝ) *
          lowOwnerFirstOwnerBranchGateSlack R p sig (topPrime R hR) := by
  rw [lowOwnerFirstOwnerTopTwoStokesClipNormalForm_eq_signedCellTelescope_of_lower
    hR hpMem hpTop hpSecond sig]
  exact
    lowOwnerFirstOwnerSignedCellTelescope_eq_half_topBranchCompletedEnergy_sub_half_slack
      hR hpMem hpTop

/-- **Fully assembled composition.**  The final Stokes boundary is the top-prime
row plus, over every other first owner, half the completed top-coordinate branch
energy minus half the gate slack. -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_topRow_add_topBranchGate
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R (topPrime R hR),
        lowOwnerFirstOwnerSignedCellTelescope R (topPrime R hR) sig) +
      ∑ p ∈ (primesUpTo (squareRootEndpoint R)).erase (topPrime R hR),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          ((1 / 2 : ℝ) *
              (lowOwnerFirstOwnerRawParentBranchThresholdEnergy
                  R p sig (topPrime R hR) +
                lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass
                  R p sig (topPrime R hR)) -
            (1 / 2 : ℝ) *
              lowOwnerFirstOwnerBranchGateSlack R p sig (topPrime R hR)) := by
  have hsplit :=
    Finset.add_sum_erase (primesUpTo (squareRootEndpoint R))
      (fun p =>
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerSignedCellTelescope R p sig)
      (topPrime_mem hR)
  have hrest :
      (∑ p ∈ (primesUpTo (squareRootEndpoint R)).erase (topPrime R hR),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerSignedCellTelescope R p sig) =
        ∑ p ∈ (primesUpTo (squareRootEndpoint R)).erase (topPrime R hR),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            ((1 / 2 : ℝ) *
                (lowOwnerFirstOwnerRawParentBranchThresholdEnergy
                    R p sig (topPrime R hR) +
                  lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass
                    R p sig (topPrime R hR)) -
              (1 / 2 : ℝ) *
                lowOwnerFirstOwnerBranchGateSlack R p sig (topPrime R hR)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpTop : p ≠ topPrime R hR := (Finset.mem_erase.mp hp).1
    have hpMem : p ∈ primesUpTo (squareRootEndpoint R) :=
      (Finset.mem_erase.mp hp).2
    apply Finset.sum_congr rfl
    intro sig _hsig
    exact
      lowOwnerFirstOwnerSignedCellTelescope_eq_half_topBranchCompletedEnergy_sub_half_slack
        hR hpMem hpTop
  rw [← sum_lowOwnerFirstOwnerSignedCellTelescope_eq_finalStokesBoundary
      (R := R) (by omega : 2 ≤ R),
    ← hsplit, hrest]

/-! ## 5. At the top coordinate there is exactly one revealed fibre -/

theorem lowOwnerRawParentRevealedKey_topPrime_eq_empty
    {R : ℕ} (hR : 56 ≤ R) (n : ℕ) :
    lowOwnerRawParentRevealedKey R (topPrime R hR) n = ∅ := by
  unfold lowOwnerRawParentRevealedKey lowOwnerRevealedPrimeSignature
  rw [lowOwnerRevealedPrimesAbove_topPrime_eq_empty hR, Finset.inter_empty]

theorem lowOwnerFirstOwnerRawParentBranchSignatureSet_topPrime_subset
    {R : ℕ} (hR : 56 ≤ R) (p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig (topPrime R hR) ⊆
      {∅} := by
  intro tau htau
  unfold lowOwnerFirstOwnerRawParentBranchSignatureSet at htau
  rcases Finset.mem_image.mp htau with ⟨n, _hn, hkey⟩
  rw [Finset.mem_singleton, ← hkey]
  exact lowOwnerRawParentRevealedKey_topPrime_eq_empty hR n

/-- One-fibre collapse of a revealed-signature square sum at the top prime. -/
private theorem sum_topBranchSignatureFibers_sq_eq
    {R : ℕ} (hR : 56 ≤ R) (p : ℕ) (sig : Finset ℕ) (f : ℕ → ℝ) :
    (∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet
        R p sig (topPrime R hR),
      (∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber
          R p sig tau (topPrime R hR),
        f n) ^ 2) =
      (∑ n ∈ lowOwnerFirstOwnerRawParentBranchSiteCarrier
          R p sig (topPrime R hR),
        f n) ^ 2 := by
  have hfib :
      lowOwnerFirstOwnerRawParentBranchSignatureFiber
          R p sig ∅ (topPrime R hR) =
        lowOwnerFirstOwnerRawParentBranchSiteCarrier
          R p sig (topPrime R hR) := by
    ext n
    simp [lowOwnerFirstOwnerRawParentBranchSignatureFiber,
      lowOwnerRawParentRevealedKey_topPrime_eq_empty hR]
  rcases Finset.subset_singleton_iff.mp
      (lowOwnerFirstOwnerRawParentBranchSignatureSet_topPrime_subset
        hR p sig) with hempty | hsingle
  · have hsite :
        lowOwnerFirstOwnerRawParentBranchSiteCarrier
            R p sig (topPrime R hR) = ∅ := by
      unfold lowOwnerFirstOwnerRawParentBranchSignatureSet at hempty
      exact Finset.image_eq_empty.mp hempty
    rw [hempty, hsite]
    simp
  · rw [hsingle, Finset.sum_singleton, hfib]

/-- The completed top-coordinate branch energy is the square of the single
branch amplitude. -/
theorem lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_topPrime_eq_totalAmplitude_sq
    {R : ℕ} (hR : 56 ≤ R) (p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy
        R p sig (topPrime R hR) =
      lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude
        R p sig (topPrime R hR) ^ 2 := by
  unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude
  exact sum_topBranchSignatureFibers_sq_eq hR p sig
    (lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p (topPrime R hR))

/-- The top-coordinate gate slack is the square of one scalar amplitude. -/
theorem lowOwnerFirstOwnerBranchGateSlack_topPrime_eq_sq
    {R : ℕ} (hR : 56 ≤ R) (p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerBranchGateSlack R p sig (topPrime R hR) =
      (∑ n ∈ lowOwnerFirstOwnerRawParentBranchSiteCarrier
          R p sig (topPrime R hR),
        (lowOwnerBranchBaseDifferenceSignedSite R (topPrime R hR) n +
          lowOwnerBranchReturnedDifferenceSignedSite
            R p (topPrime R hR) n)) ^ 2 := by
  have h := sum_topBranchSignatureFibers_sq_eq hR p sig
    (fun n =>
      lowOwnerBranchBaseDifferenceSignedSite R (topPrime R hR) n +
        lowOwnerBranchReturnedDifferenceSignedSite R p (topPrime R hR) n)
  unfold lowOwnerFirstOwnerBranchGateSlack
    lowOwnerFirstOwnerBranchBaseDifferenceAmplitude
    lowOwnerFirstOwnerBranchReturnedDifferenceAmplitude
  rw [← h]
  apply Finset.sum_congr rfl
  intro tau _htau
  rw [Finset.sum_add_distrib]

/-- The first owner `2` has a single lower-signature cell. -/
theorem lowOwnerFirstOwnerSignatureSet_two_eq
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerFirstOwnerSignatureSet R 2 = {∅} := by
  apply Finset.Subset.antisymm
  · intro sig hsig
    unfold lowOwnerFirstOwnerSignatureSet at hsig
    rcases Finset.mem_image.mp hsig with ⟨n, _hn, hsigEq⟩
    rw [Finset.mem_singleton, ← hsigEq]
    ext q
    constructor
    · intro hq
      unfold squarefreeLowerPrimeSignature squarefreePrimeFace at hq
      rcases Finset.mem_filter.mp hq with ⟨hqFace, hqLt⟩
      have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hqFace
      exact absurd hqLt (Nat.not_lt.mpr hqPrime.two_le)
    · intro hq
      simp at hq
  · intro sig hsig
    rw [Finset.mem_singleton] at hsig
    subst sig
    unfold lowOwnerFirstOwnerSignatureSet
    have hX : 1 ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      have hsq : 2 ≤ R ^ 2 := by nlinarith
      omega
    have h1 : 1 ∈ lowOwnerNonzeroMobiusCarrier R := by
      unfold lowOwnerNonzeroMobiusCarrier
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hX⟩, ?_⟩
      simp [realMoebiusStep]
    refine Finset.mem_image.mpr ⟨1, h1, ?_⟩
    simp [squarefreeLowerPrimeSignature, squarefreePrimeFace]

/-- `2` lies strictly below the top clock prime. -/
theorem two_lt_topPrime {R : ℕ} (hR : 56 ≤ R) :
    2 < topPrime R hR := by
  have hhalf := endpoint_half_lt_topPrime hR
  have hX : 6 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : 7 ≤ R ^ 2 := by nlinarith
    omega
  omega

/-- **The first-owner top-coordinate amplitude is the whole global
amplitude.**  It is the reciprocal q² column plus the top endpoint gap. -/
theorem lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude_two_topPrime_eq
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude
        R 2 ∅ (topPrime R hR) =
      lowOwnerReciprocalMertensColumnReal R +
        lowOwnerPost789EndpointGapReal R := by
  have h :=
    lowOwnerGlobalBranchIncidenceDifferenceAmplitude_eq_reciprocal_add_endpointGap
      (R := R) (p := 2) (r := topPrime R hR)
      (by omega) Nat.prime_two (topPrime_prime hR) (two_lt_topPrime hR)
  unfold lowOwnerGlobalBranchIncidenceDifferenceAmplitude at h
  rw [lowOwnerFirstOwnerSignatureSet_two_eq hR, Finset.sum_singleton] at h
  exact h

/-- **The completed branch energy of the first owner at the top coordinate is
literally `(Q + G)^2`.**  The post-#794 threshold/endpoint split of this energy
therefore carries the top endpoint gap with coefficient one. -/
theorem lowOwnerFirstOwnerCompletedTopBranchEnergy_two_eq_globalAmplitude_sq
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerFirstOwnerRawParentBranchThresholdEnergy R 2 ∅ (topPrime R hR) +
        lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass
          R 2 ∅ (topPrime R hR) =
      (lowOwnerReciprocalMertensColumnReal R +
        lowOwnerPost789EndpointGapReal R) ^ 2 := by
  rw [← lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_branchThresholdEnergy_add_endpointCorrection
      (by omega : 2 ≤ R) Nat.prime_two (topPrime_prime hR),
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_topPrime_eq_totalAmplitude_sq
      hR 2 ∅,
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude_two_topPrime_eq
      hR]

/-- **First-owner cell in closed form.**  The signed cell of the first owner is
half the full global amplitude square minus half its top-coordinate gate
slack. -/
theorem lowOwnerFirstOwnerSignedCellTelescope_two_eq_half_globalAmplitudeSq_sub_half_slack
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerFirstOwnerSignedCellTelescope R 2 ∅ =
      (1 / 2 : ℝ) *
          (lowOwnerReciprocalMertensColumnReal R +
            lowOwnerPost789EndpointGapReal R) ^ 2 -
        (1 / 2 : ℝ) *
          lowOwnerFirstOwnerBranchGateSlack R 2 ∅ (topPrime R hR) := by
  have h2Mem : 2 ∈ primesUpTo (squareRootEndpoint R) := by
    apply mem_primesUpTo.mpr
    refine ⟨Nat.prime_two, ?_⟩
    unfold squareRootEndpoint
    have hsq : 3 ≤ R ^ 2 := by nlinarith
    omega
  have h2Top : 2 ≠ topPrime R hR := by
    have := two_lt_topPrime hR
    omega
  rw [lowOwnerFirstOwnerSignedCellTelescope_eq_half_topBranchCompletedEnergy_sub_half_slack
      hR h2Mem h2Top,
    lowOwnerFirstOwnerCompletedTopBranchEnergy_two_eq_globalAmplitude_sq hR]

end RHLean.Proof
