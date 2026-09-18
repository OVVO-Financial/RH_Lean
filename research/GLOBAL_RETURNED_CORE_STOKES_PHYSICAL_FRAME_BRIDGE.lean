import Mathlib
import «research.GLOBAL_RETURNED_CORE_FINAL_STOKES_RH_BRIDGE»
import «research.GLOBAL_RETURNED_CORE_STOKES_NATURAL_PERIOD_WHEEL»
import «research.STOKES_ENDPOINT_MAX_ALIGNMENT_FRAME»
import «research.STABLE_FAR_PERRON_QUARTER_FRAME_BOUND»
import «research.GLOBAL_RETURNED_CORE_STOKES_CROSS_AMPLITUDE_NORMAL_FORM»

/-!
# Physical Stokes boundary -> natural prime-period frame interface

This file fixes the exact natural frame carrier and eliminates every auxiliary
frame side condition in the RH-consumer regime.

Let
  S_R = primesUpTo (sqrt X_R) \ {2}
on the natural square-sensitive Stokes torus, with endpoint length X_R.
Then:
* every p in S_R is prime;
* p divides the natural torus modulus (indeed p^2 does);
* reciprocal-square mass is at most 1/4;
* X_R <= R^2;
* |S_R| <= R.

Hence the compiled frame majorant is at most (5/4) R^2.

The only remaining analytic/arithmetic step is intentionally explicit:
dominate the exact signed final Stokes boundary by a fixed multiple of this
physical prime-period frame. No such domination is manufactured here by
triangle inequality or by dropping mixed corrected-conductor channels.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Actual odd prime-period coordinates of the natural Stokes wheel. -/
def lowOwnerStokesOddPrimePeriodSet (R : ℕ) : Finset ℕ :=
  (lowOwnerStokesWheelPrimes R).erase 2

theorem lowOwnerStokesOddPrimePeriodSet_prime
    {R p : ℕ} (hp : p ∈ lowOwnerStokesOddPrimePeriodSet R) :
    p.Prime := by
  exact lowOwnerStokesWheelPrimes_prime (Finset.mem_erase.mp hp).2

theorem lowOwnerStokesOddPrimePeriodSet_dvd_naturalModulus
    {R p : ℕ} (hR : 56 ≤ R)
    (hp : p ∈ lowOwnerStokesOddPrimePeriodSet R) :
    p ∣ (lowOwnerStokesNaturalWheelSystem R hR).modulus := by
  have hpWheel : p ∈ lowOwnerStokesWheelPrimes R :=
    (Finset.mem_erase.mp hp).2
  exact dvd_trans (dvd_pow_self p (by norm_num))
    (prime_sq_dvd_lowOwnerStokesNaturalWheelModulus hR hpWheel)

theorem lowOwnerStokesOddPrimePeriodSet_reciprocalSquareBudget_le_quarter
    (R : ℕ) :
    (∑ p ∈ lowOwnerStokesOddPrimePeriodSet R,
      ((1 : ℝ) / (p : ℝ)) ^ 2) ≤ 1 / 4 := by
  unfold lowOwnerStokesOddPrimePeriodSet lowOwnerStokesWheelPrimes
  simpa [div_pow] using
    (oddPrimeOwnerReciprocalSquareBudgetReal_le_quarter
      (Nat.sqrt (squareRootEndpoint R)))

theorem lowOwnerStokesOddPrimePeriodSet_card_le_root
    {R : ℕ} (hR : 1 ≤ R) :
    (lowOwnerStokesOddPrimePeriodSet R).card ≤ R := by
  have hroot : Nat.sqrt (squareRootEndpoint R) < R := by
    apply (Nat.sqrt_lt').2
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  have hsub :
      lowOwnerStokesOddPrimePeriodSet R ⊆ Finset.range R := by
    intro p hp
    have hpWheel : p ∈ lowOwnerStokesWheelPrimes R :=
      (Finset.mem_erase.mp hp).2
    have hpCut : p ≤ Nat.sqrt (squareRootEndpoint R) := by
      unfold lowOwnerStokesWheelPrimes at hpWheel
      exact (mem_primesUpTo.mp hpWheel).2
    exact Finset.mem_range.mpr (hpCut.trans_lt hroot)
  simpa using Finset.card_le_card hsub

/-- The compiled reciprocal prime-period frame on the literal physical odd
Stokes coordinates and the natural square-sensitive torus. -/
def lowOwnerStokesOddPrimePeriodFrameMajorant
    (R : ℕ) (hR : 56 ≤ R) : ℝ :=
  primePeriodReciprocalFrameMajorant
    (lowOwnerStokesNaturalWheelSystem R hR)
    (squareRootEndpoint R)
    (lowOwnerStokesOddPrimePeriodSet R)

/-- All side conditions of the existing maximum-alignment theorem hold on the
actual Stokes wheel. -/
theorem lowOwnerStokesOddPrimePeriodFrameMajorant_le_five_fourths_root_sq
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesOddPrimePeriodFrameMajorant R hR ≤
      (5 / 4 : ℝ) * (R : ℝ) ^ 2 := by
  unfold lowOwnerStokesOddPrimePeriodFrameMajorant
  apply primePeriodReciprocalFrameMajorant_le_five_fourths_root_sq
  · intro p hp
    exact lowOwnerStokesOddPrimePeriodSet_prime hp
  · intro p hp
    exact lowOwnerStokesOddPrimePeriodSet_dvd_naturalModulus hR hp
  · exact lowOwnerStokesOddPrimePeriodSet_reciprocalSquareBudget_le_quarter R
  · unfold squareRootEndpoint
    exact Nat.sub_le _ _
  · exact lowOwnerStokesOddPrimePeriodSet_card_le_root (by omega)

/-- Every admissible lower critical envelope is at least one.  This lets a
root-scale frame estimate feed the existing R^2*K terminal interface without
changing the arithmetic constant. -/
theorem lowerMertensCriticalEnvelope_one_le
    {R : ℕ} {K : ℝ} (hR : 1 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    1 ≤ K := by
  have h0 := hK.2 0 (by omega)
  norm_num [mertensSummatoryInt] at h0
  exact h0

/-- Exact remaining physical bridge.  The source is the already-identified
final signed Stokes boundary; the target is the actual natural odd-prime frame.
No surrogate boundary or hidden frame hypothesis occurs in the statement. -/
def LowOwnerStokesPrimePeriodFrameDomination (C : ℝ) : Prop :=
  ∀ (R : ℕ) (hR : 56 ≤ R),
    lowOwnerCanonicalSignedStokesFinalBoundary R ≤
      C * lowOwnerStokesOddPrimePeriodFrameMajorant R hR

/-- Any fixed physical domination constant now yields the exact final Stokes
boundary bound consumed by the RH chain. -/
theorem finalStokesBoundaryBound_of_primePeriodFrameDomination
    {C : ℝ} (hC : 0 ≤ C)
    (hBridge : LowOwnerStokesPrimePeriodFrameDomination C) :
    LowOwnerFinalStokesBoundaryBound ((5 / 4 : ℝ) * C) := by
  intro R K hR hK
  have hphysical := hBridge R hR
  have hframe :=
    lowOwnerStokesOddPrimePeriodFrameMajorant_le_five_fourths_root_sq hR
  have hscaled :
      C * lowOwnerStokesOddPrimePeriodFrameMajorant R hR ≤
        C * ((5 / 4 : ℝ) * (R : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hframe hC
  have hKone : 1 ≤ K :=
    lowerMertensCriticalEnvelope_one_le (by omega) hK
  have hcoef :
      0 ≤ ((5 / 4 : ℝ) * C) * (R : ℝ) ^ 2 := by
    positivity
  have hKmul :=
    mul_le_mul_of_nonneg_left hKone hcoef
  calc
    lowOwnerCanonicalSignedStokesFinalBoundary R ≤
        C * lowOwnerStokesOddPrimePeriodFrameMajorant R hR := hphysical
    _ ≤ C * ((5 / 4 : ℝ) * (R : ℝ) ^ 2) := hscaled
    _ = ((5 / 4 : ℝ) * C) * (R : ℝ) ^ 2 := by ring
    _ ≤ ((5 / 4 : ℝ) * C) * (R : ℝ) ^ 2 * K := by
      simpa [mul_assoc] using hKmul

/-- Once the exact physical payload-to-frame domination is supplied, no further
Stokes, frame, envelope, or terminal plumbing remains before RH. -/
theorem riemannHypothesis_of_primePeriodFrameDomination
    {C : ℝ} (hC : 0 ≤ C)
    (hBridge : LowOwnerStokesPrimePeriodFrameDomination C) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_finalStokesBoundaryBound
    (by positivity)
    (finalStokesBoundaryBound_of_primePeriodFrameDomination hC hBridge)

/-- Unit-constant version of the remaining physical bridge. -/
def LowOwnerStokesPrimePeriodFrameBridge : Prop :=
  LowOwnerStokesPrimePeriodFrameDomination 1

theorem riemannHypothesis_of_primePeriodFrameBridge
    (hBridge : LowOwnerStokesPrimePeriodFrameBridge) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_primePeriodFrameDomination
    (C := (1 : ℝ)) (by norm_num) hBridge


/-! ## Split the physical bridge at the already-classified Stokes boundary

The terminal classification proves that a cell with at least two remaining
prime coordinates has zero terminal residual.  The only first-owner levels
which can contribute to the terminal ledger are therefore those whose
canonical schedule has length zero or one.  We record that support exactly
before asking for any frame estimate.
-/

/-- First-owner coordinates on which the canonical Stokes terminal residual
can survive.  Equivalently, there are at most one larger prime coordinates left
in the descending schedule. -/
def lowOwnerStokesTopTerminalOwnerSet (R : ℕ) : Finset ℕ :=
  (primesUpTo (squareRootEndpoint R)).filter fun p =>
    (lowOwnerFirstOwnerCanonicalStokesSchedule R p).length ≤ 1

/-- Outside the zero/one-owner terminal strata the local terminal contribution
is literally zero. -/
theorem lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary_eq_zero_of_not_mem_terminalOwners
    {R p : ℕ} {sig : Finset ℕ}
    (hp : p ∈ primesUpTo (squareRootEndpoint R))
    (hnot : p ∉ lowOwnerStokesTopTerminalOwnerSet R) :
    lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig = 0 := by
  have hlenNot :
      ¬ (lowOwnerFirstOwnerCanonicalStokesSchedule R p).length ≤ 1 := by
    intro hlen
    exact hnot (Finset.mem_filter.mpr ⟨hp, hlen⟩)
  have htwo :
      2 ≤ (lowOwnerFirstOwnerCanonicalStokesSchedule R p).length := by
    omega
  cases hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p with
  | nil =>
      simp [hps] at htwo
  | cons q qs =>
      cases qs with
      | nil =>
          simp [hps] at htwo
      | cons s rest =>
          exact
            lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary_eq_zero_of_twoOwners
              (R := R) (p := p) (q := q) (s := s) (sig := sig)
              (rest := rest) hps

/-- The global top-terminal ledger is supported only on the zero/one-owner
levels.  This removes every deeper first-owner level exactly, before any
absolute value or norm is introduced. -/
theorem lowOwnerCanonicalSignedStokesTopTerminalBoundary_eq_terminalOwnerSum
    (R : ℕ) :
    lowOwnerCanonicalSignedStokesTopTerminalBoundary R =
      ∑ p ∈ lowOwnerStokesTopTerminalOwnerSet R,
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig := by
  unfold lowOwnerCanonicalSignedStokesTopTerminalBoundary
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  apply Finset.sum_eq_zero
  intro sig hsig
  exact
    lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary_eq_zero_of_not_mem_terminalOwners
      hp hnot

/-- Frame domination for the literal physical clip ledger only. -/
def LowOwnerStokesClipPrimePeriodFrameDomination (C : ℝ) : Prop :=
  ∀ (R : ℕ) (hR : 56 ≤ R),
    lowOwnerCanonicalSignedStokesClipBoundary R ≤
      C * lowOwnerStokesOddPrimePeriodFrameMajorant R hR

/-- Frame domination for the already-classified terminal correction only. -/
def LowOwnerStokesTopTerminalPrimePeriodFrameDomination (C : ℝ) : Prop :=
  ∀ (R : ℕ) (hR : 56 ≤ R),
    lowOwnerCanonicalSignedStokesTopTerminalBoundary R ≤
      C * lowOwnerStokesOddPrimePeriodFrameMajorant R hR

/-- Equivalent terminal target with all identically-zero owner levels removed
from the statement. -/
def LowOwnerStokesExceptionalTerminalFrameDomination (C : ℝ) : Prop :=
  ∀ (R : ℕ) (hR : 56 ≤ R),
    (∑ p ∈ lowOwnerStokesTopTerminalOwnerSet R,
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig) ≤
      C * lowOwnerStokesOddPrimePeriodFrameMajorant R hR

theorem topTerminalPrimePeriodFrameDomination_of_exceptional
    {C : ℝ}
    (hTerminal : LowOwnerStokesExceptionalTerminalFrameDomination C) :
    LowOwnerStokesTopTerminalPrimePeriodFrameDomination C := by
  intro R hR
  rw [lowOwnerCanonicalSignedStokesTopTerminalBoundary_eq_terminalOwnerSum]
  exact hTerminal R hR

/-- The exact final payload-to-frame bridge splits into the physical clip
estimate plus the terminal correction.  Constants add and no sign is discarded. -/
theorem primePeriodFrameDomination_of_clip_add_topTerminal
    {Cclip Cterminal : ℝ}
    (hClip : LowOwnerStokesClipPrimePeriodFrameDomination Cclip)
    (hTerminal : LowOwnerStokesTopTerminalPrimePeriodFrameDomination Cterminal) :
    LowOwnerStokesPrimePeriodFrameDomination (Cclip + Cterminal) := by
  intro R hR
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_clip_add_topTerminal]
  calc
    lowOwnerCanonicalSignedStokesClipBoundary R +
        lowOwnerCanonicalSignedStokesTopTerminalBoundary R ≤
      Cclip * lowOwnerStokesOddPrimePeriodFrameMajorant R hR +
        Cterminal * lowOwnerStokesOddPrimePeriodFrameMajorant R hR :=
      add_le_add (hClip R hR) (hTerminal R hR)
    _ = (Cclip + Cterminal) *
        lowOwnerStokesOddPrimePeriodFrameMajorant R hR := by ring

/-- Consumer with the terminal support collapse already built in.  The only
remaining estimates are the literal clip ledger and the zero/one-owner terminal
correction. -/
theorem riemannHypothesis_of_clip_and_exceptionalTerminalFrameDomination
    {Cclip Cterminal : ℝ}
    (hC : 0 ≤ Cclip + Cterminal)
    (hClip : LowOwnerStokesClipPrimePeriodFrameDomination Cclip)
    (hTerminal : LowOwnerStokesExceptionalTerminalFrameDomination Cterminal) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_primePeriodFrameDomination hC
    (primePeriodFrameDomination_of_clip_add_topTerminal
      hClip (topTerminalPrimePeriodFrameDomination_of_exceptional hTerminal))


/-! ## Exact exceptional-terminal normal forms

The terminal support from #758 is now separated according to whether no larger
owner remains or exactly one larger owner remains. These are algebraic normal
forms only; they deliberately preserve the signature assembly.
-/

/-- Terminal first-owner levels with no larger canonical owner remaining. -/
def lowOwnerStokesEmptyScheduleOwnerSet (R : ℕ) : Finset ℕ :=
  (primesUpTo (squareRootEndpoint R)).filter fun p =>
    lowOwnerFirstOwnerCanonicalStokesSchedule R p = []

/-- Terminal first-owner levels with exactly one larger canonical owner
remaining. -/
def lowOwnerStokesOneScheduleOwnerSet (R : ℕ) : Finset ℕ :=
  (primesUpTo (squareRootEndpoint R)).filter fun p =>
    (lowOwnerFirstOwnerCanonicalStokesSchedule R p).length = 1

/-- On an empty schedule the top-terminal cell is exactly the original signed
cell telescope, hence the already-compiled cross-amplitude product. -/
theorem lowOwnerFirstOwnerTopTerminal_eq_neg_two_base_mul_returned_of_emptySchedule
    {R p : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = []) :
    lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig =
      -2 * lowOwnerFirstOwnerBaseAmplitude R p sig *
        lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := by
  have hmass :=
    lowOwnerFirstOwnerSignedCellTelescope_eq_pairWeightedStokesMass
      (R := R) (p := p) (sig := sig) hp
  have hcross :=
    lowOwnerFirstOwnerSignedCellTelescope_eq_neg_two_base_mul_returned
      (R := R) (p := p) (sig := sig) hp
  calc
    lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig =
        pairWeightedStokesMass
          (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
          (lowOwnerFirstOwnerDirichletPolarizationScalar R p) := by
            simp [lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary, hps]
    _ = lowOwnerFirstOwnerSignedCellTelescope R p sig := hmass.symm
    _ = -2 * lowOwnerFirstOwnerBaseAmplitude R p sig *
          lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig := hcross

/-- Empty-schedule signature assembly. The full signature sum remains assembled
as one signed base/returned pairing. -/
theorem sum_lowOwnerFirstOwnerTopTerminal_eq_neg_two_sum_base_mul_returned_of_emptySchedule
    {R p : ℕ}
    (hp : p.Prime)
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = []) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig) =
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        (-2 * lowOwnerFirstOwnerBaseAmplitude R p sig *
          lowOwnerFirstOwnerReturnedChildParentAmplitude R p sig) := by
  apply Finset.sum_congr rfl
  intro sig _hsig
  exact
    lowOwnerFirstOwnerTopTerminal_eq_neg_two_base_mul_returned_of_emptySchedule
      hp hps

/-- One-owner terminal normal form with exact quarter multiplicity and mixed
difference. -/
theorem lowOwnerFirstOwnerTopTerminal_eq_quarter_mixed_of_oneSchedule
    {R p q : ℕ} {sig : Finset ℕ}
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = [q]) :
    lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig =
      (1 / 4 : ℝ) *
        pairWeightedStokesMass
          (pairPrimeTwoCoordinateInterior q
            (lowOwnerFirstOwnerSignedCellPairCarrier R p sig))
          (pairPrimeMixedDifference q
            (lowOwnerFirstOwnerDirichletPolarizationScalar R p)) := by
  simp [lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary, hps]

/-- The same one-owner normal form after summing over signatures. -/
theorem sum_lowOwnerFirstOwnerTopTerminal_eq_quarter_mixed_of_oneSchedule
    {R p q : ℕ}
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = [q]) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig) =
      (1 / 4 : ℝ) *
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          pairWeightedStokesMass
            (pairPrimeTwoCoordinateInterior q
              (lowOwnerFirstOwnerSignedCellPairCarrier R p sig))
            (pairPrimeMixedDifference q
              (lowOwnerFirstOwnerDirichletPolarizationScalar R p)) := by
  calc
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig) =
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ((1 / 4 : ℝ) *
          pairWeightedStokesMass
            (pairPrimeTwoCoordinateInterior q
              (lowOwnerFirstOwnerSignedCellPairCarrier R p sig))
            (pairPrimeMixedDifference q
              (lowOwnerFirstOwnerDirichletPolarizationScalar R p))) := by
        apply Finset.sum_congr rfl
        intro sig _hsig
        exact lowOwnerFirstOwnerTopTerminal_eq_quarter_mixed_of_oneSchedule hps
    _ = (1 / 4 : ℝ) *
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          pairWeightedStokesMass
            (pairPrimeTwoCoordinateInterior q
              (lowOwnerFirstOwnerSignedCellPairCarrier R p sig))
            (pairPrimeMixedDifference q
              (lowOwnerFirstOwnerDirichletPolarizationScalar R p)) := by
          rw [Finset.mul_sum]

/-- The two exceptional schedule classes cover the #758 terminal owner set. -/
theorem lowOwnerStokesTopTerminalOwnerSet_eq_empty_union_one
    (R : ℕ) :
    lowOwnerStokesTopTerminalOwnerSet R =
      lowOwnerStokesEmptyScheduleOwnerSet R ∪
        lowOwnerStokesOneScheduleOwnerSet R := by
  ext p
  simp only [lowOwnerStokesTopTerminalOwnerSet,
    lowOwnerStokesEmptyScheduleOwnerSet, lowOwnerStokesOneScheduleOwnerSet,
    Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hp, hlen⟩
    rcases Nat.eq_zero_or_pos
        (lowOwnerFirstOwnerCanonicalStokesSchedule R p).length with hzero | hpos
    · left
      refine ⟨hp, ?_⟩
      exact List.length_eq_zero.mp hzero
    · right
      refine ⟨hp, ?_⟩
      omega
  · rintro (⟨hp, hnil⟩ | ⟨hp, hone⟩)
    · refine ⟨hp, ?_⟩
      rw [hnil]
      simp
    · exact ⟨hp, by omega⟩

/-- Empty- and one-owner levels are disjoint. -/
theorem lowOwnerStokesEmptyScheduleOwnerSet_disjoint_oneScheduleOwnerSet
    (R : ℕ) :
    Disjoint (lowOwnerStokesEmptyScheduleOwnerSet R)
      (lowOwnerStokesOneScheduleOwnerSet R) := by
  apply Finset.disjoint_left.mpr
  intro p hempty hone
  have hnil := (Finset.mem_filter.mp hempty).2
  have hlen := (Finset.mem_filter.mp hone).2
  rw [hnil] at hlen
  simp at hlen

/-- Exact global terminal split in the requested attack order. -/
theorem lowOwnerCanonicalSignedStokesTopTerminalBoundary_eq_empty_add_oneSchedule
    (R : ℕ) :
    lowOwnerCanonicalSignedStokesTopTerminalBoundary R =
      (∑ p ∈ lowOwnerStokesEmptyScheduleOwnerSet R,
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig) +
      (∑ p ∈ lowOwnerStokesOneScheduleOwnerSet R,
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig) := by
  rw [lowOwnerCanonicalSignedStokesTopTerminalBoundary_eq_terminalOwnerSum,
    lowOwnerStokesTopTerminalOwnerSet_eq_empty_union_one]
  exact Finset.sum_union
    (lowOwnerStokesEmptyScheduleOwnerSet_disjoint_oneScheduleOwnerSet R)

/-- Three-piece final Stokes normal form: physical clip, empty-schedule
assembled cross amplitude, and one-owner quarter-mixed correction. -/
theorem lowOwnerCanonicalSignedStokesFinalBoundary_eq_clip_add_empty_add_one
    (R : ℕ) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      lowOwnerCanonicalSignedStokesClipBoundary R +
      (∑ p ∈ lowOwnerStokesEmptyScheduleOwnerSet R,
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig) +
      (∑ p ∈ lowOwnerStokesOneScheduleOwnerSet R,
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary R p sig) := by
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_clip_add_topTerminal,
    lowOwnerCanonicalSignedStokesTopTerminalBoundary_eq_empty_add_oneSchedule]
  ring

end RHLean.Proof
