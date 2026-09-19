import Mathlib
import «research.GLOBAL_RETURNED_CORE_FINAL_STOKES_RH_BRIDGE»
import «research.GLOBAL_RETURNED_CORE_STOKES_NATURAL_PERIOD_WHEEL»
import «research.STOKES_ENDPOINT_MAX_ALIGNMENT_FRAME»
import «research.STABLE_FAR_PERRON_QUARTER_FRAME_BOUND»
import «research.GLOBAL_RETURNED_CORE_STOKES_CROSS_AMPLITUDE_NORMAL_FORM»
import «research.GLOBAL_RETURNED_CORE_DOUBLE_CORNER_POLARIZATION_FUBINI»

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


/-! ## Maximum-alignment envelope for the clip attack

The frame majorant really is a maximum-alignment majorant once a physical
quantity has been assembled into reciprocal prime-period coordinates.  The
remaining arithmetic issue is therefore representation, not a further harmonic
inequality.
-/

/-- Reciprocal prime-period Gram envelope with an arbitrary bounded coefficient
on each prime mode.  The diagonal and off-diagonal pieces are kept in exactly
the currency of `primePeriodReciprocalFrameMajorant`. -/
def primePeriodReciprocalCoefficientEnvelope
    (W : PrimeWheelFiniteSystem) (N : ℕ) (S : Finset ℕ)
    (a : ℕ → ℂ) : ℝ :=
  (N : ℝ) *
      ∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2 * ‖a p‖ ^ 2 +
    ∑ p ∈ S,
      ∑ q ∈ S.erase p,
        (((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
            ‖primeWheelDirichletKernel W N
              (primePeriodFrequency W p - primePeriodFrequency W q)‖) *
          (‖a p‖ * ‖a q‖)

/-- **Maximum-alignment theorem with coefficients.**  Any family whose mode
coefficients have norm at most one is dominated by the coefficient-free frame
majorant. -/
theorem primePeriodReciprocalCoefficientEnvelope_le_frameMajorant
    (W : PrimeWheelFiniteSystem) (N : ℕ) (S : Finset ℕ)
    (a : ℕ → ℂ)
    (ha : ∀ p ∈ S, ‖a p‖ ≤ 1) :
    primePeriodReciprocalCoefficientEnvelope W N S a ≤
      primePeriodReciprocalFrameMajorant W N S := by
  have hdiagSum :
      (∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2 * ‖a p‖ ^ 2) ≤
        ∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2 := by
    apply Finset.sum_le_sum
    intro p hp
    have hap := ha p hp
    have hsq : ‖a p‖ ^ 2 ≤ (1 : ℝ) := by
      nlinarith [norm_nonneg (a p)]
    calc
      ((1 : ℝ) / (p : ℝ)) ^ 2 * ‖a p‖ ^ 2 ≤
          ((1 : ℝ) / (p : ℝ)) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = ((1 : ℝ) / (p : ℝ)) ^ 2 := by ring
  have hdiag :
      (N : ℝ) *
          (∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2 * ‖a p‖ ^ 2) ≤
        primePeriodReciprocalDiagonalMajorant N S := by
    unfold primePeriodReciprocalDiagonalMajorant
    exact mul_le_mul_of_nonneg_left hdiagSum (by positivity)
  have hoff :
      (∑ p ∈ S,
        ∑ q ∈ S.erase p,
          (((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
              ‖primeWheelDirichletKernel W N
                (primePeriodFrequency W p - primePeriodFrequency W q)‖) *
            (‖a p‖ * ‖a q‖)) ≤
        primePeriodReciprocalOffDiagonalMajorant W N S := by
    unfold primePeriodReciprocalOffDiagonalMajorant
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro q hq
    have hqS : q ∈ S := (Finset.mem_erase.mp hq).2
    have hpqNorm :
        ‖a p‖ * ‖a q‖ ≤ (1 : ℝ) := by
      calc
        ‖a p‖ * ‖a q‖ ≤ 1 * 1 :=
          mul_le_mul (ha p hp) (ha q hqS) (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    have hw :
        0 ≤
          ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
            ‖primeWheelDirichletKernel W N
              (primePeriodFrequency W p - primePeriodFrequency W q)‖ := by
      positivity
    calc
      (((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
          ‖primeWheelDirichletKernel W N
            (primePeriodFrequency W p - primePeriodFrequency W q)‖) *
          (‖a p‖ * ‖a q‖) ≤
        (((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
          ‖primeWheelDirichletKernel W N
            (primePeriodFrequency W p - primePeriodFrequency W q)‖) * 1 :=
          mul_le_mul_of_nonneg_left hpqNorm hw
      _ =
        ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
          ‖primeWheelDirichletKernel W N
            (primePeriodFrequency W p - primePeriodFrequency W q)‖ := by ring
  unfold primePeriodReciprocalCoefficientEnvelope
    primePeriodReciprocalFrameMajorant
  linarith

/-- Exact physical representation target for the clip.  It asks only that the
assembled clip lie under one reciprocal prime-period coefficient envelope with
unit-bounded mode coefficients. -/
def LowOwnerStokesClipReciprocalCoefficientEnvelope : Prop :=
  ∀ (R : ℕ) (hR : 56 ≤ R),
    ∃ a : ℕ → ℂ,
      (∀ p ∈ lowOwnerStokesOddPrimePeriodSet R, ‖a p‖ ≤ 1) ∧
      lowOwnerCanonicalSignedStokesClipBoundary R ≤
        primePeriodReciprocalCoefficientEnvelope
          (lowOwnerStokesNaturalWheelSystem R hR)
          (squareRootEndpoint R)
          (lowOwnerStokesOddPrimePeriodSet R) a

/-- Once the physical clip has the reciprocal coefficient envelope, it cannot
exceed the existing frame majorant: `Cclip = 1`. -/
theorem clipPrimePeriodFrameDomination_one_of_coefficientEnvelope
    (hClip : LowOwnerStokesClipReciprocalCoefficientEnvelope) :
    LowOwnerStokesClipPrimePeriodFrameDomination 1 := by
  intro R hR
  rcases hClip R hR with ⟨a, ha, hphysical⟩
  calc
    lowOwnerCanonicalSignedStokesClipBoundary R ≤
        primePeriodReciprocalCoefficientEnvelope
          (lowOwnerStokesNaturalWheelSystem R hR)
          (squareRootEndpoint R)
          (lowOwnerStokesOddPrimePeriodSet R) a := hphysical
    _ ≤ primePeriodReciprocalFrameMajorant
          (lowOwnerStokesNaturalWheelSystem R hR)
          (squareRootEndpoint R)
          (lowOwnerStokesOddPrimePeriodSet R) :=
      primePeriodReciprocalCoefficientEnvelope_le_frameMajorant
        (lowOwnerStokesNaturalWheelSystem R hR)
        (squareRootEndpoint R)
        (lowOwnerStokesOddPrimePeriodSet R) a ha
    _ = 1 * lowOwnerStokesOddPrimePeriodFrameMajorant R hR := by
      simp [lowOwnerStokesOddPrimePeriodFrameMajorant]


/-! ## Audit of the existential coefficient interface

The preceding existential envelope is intentionally audited here.  If the
coefficient family is allowed to be chosen with no physical representation
constraint, the constant family `a_p = 1` makes its envelope exactly the
coefficient-free frame.  Thus the existential proposition is *equivalent* to
the clip/frame inequality and must not be treated as an admissibility proof.
-/

/-- Unit coefficients saturate the coefficient envelope exactly at the
coefficient-free reciprocal prime-period frame. -/
theorem primePeriodReciprocalCoefficientEnvelope_one_eq_frameMajorant
    (W : PrimeWheelFiniteSystem) (N : ℕ) (S : Finset ℕ) :
    primePeriodReciprocalCoefficientEnvelope W N S (fun _ => (1 : ℂ)) =
      primePeriodReciprocalFrameMajorant W N S := by
  unfold primePeriodReciprocalCoefficientEnvelope
    primePeriodReciprocalFrameMajorant
    primePeriodReciprocalDiagonalMajorant
    primePeriodReciprocalOffDiagonalMajorant
  simp

/-- **No-progress audit.**  The unconstrained existential coefficient envelope
is exactly equivalent to the desired unit clip/frame domination.  Therefore a
real admissibility theorem must construct coefficients from the physical Stokes
payload (or prove an exact physical synthesis identity); mere existence is
circular. -/
theorem lowOwnerStokesClipReciprocalCoefficientEnvelope_iff_frameDomination_one :
    LowOwnerStokesClipReciprocalCoefficientEnvelope ↔
      LowOwnerStokesClipPrimePeriodFrameDomination 1 := by
  constructor
  · exact clipPrimePeriodFrameDomination_one_of_coefficientEnvelope
  · intro hFrame R hR
    refine ⟨fun _ => (1 : ℂ), ?_, ?_⟩
    · intro p hp
      simp
    · rw [primePeriodReciprocalCoefficientEnvelope_one_eq_frameMajorant]
      have h := hFrame R hR
      simpa [lowOwnerStokesOddPrimePeriodFrameMajorant] using h

/-- One actual reciprocal prime-period mode on the natural Stokes torus.  The
coefficient field in a genuine admissibility theorem must be supplied before
this synthesis is formed. -/
def lowOwnerStokesPrimePeriodMode
    (R : ℕ) (hR : 56 ≤ R) (p j : ℕ) : ℂ :=
  ((1 : ℂ) / (p : ℂ)) *
    ZMod.stdAddChar
      (((j : ℕ) : ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus) *
        primePeriodFrequency (lowOwnerStokesNaturalWheelSystem R hR) p)

/-- Samplewise reciprocal prime-period synthesis from a *specified*
coefficient field. -/
def lowOwnerStokesPrimePeriodSynthesis
    (R : ℕ) (hR : 56 ≤ R) (a : ℕ → ℂ) (j : ℕ) : ℂ :=
  ∑ p ∈ lowOwnerStokesOddPrimePeriodSet R,
    a p * lowOwnerStokesPrimePeriodMode R hR p j

/-- Physical prefix energy of a specified reciprocal prime-period synthesis. -/
def lowOwnerStokesPrimePeriodSynthesisEnergy
    (R : ℕ) (hR : 56 ≤ R) (a : ℕ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range (squareRootEndpoint R),
    ‖lowOwnerStokesPrimePeriodSynthesis R hR a j‖ ^ 2

/-- A non-circular admissibility datum packages a *named coefficient
construction* together with its unit bound and the physical clip comparison.
Unlike the earlier existential proposition, the coefficient constructor is an
argument of the structure and can therefore be audited independently. -/
structure LowOwnerStokesClipPrimePeriodSynthesisDatum where
  coefficient :
    (R : ℕ) → (hR : 56 ≤ R) → ℕ → ℂ
  coefficient_unit :
    ∀ (R : ℕ) (hR : 56 ≤ R) p,
      p ∈ lowOwnerStokesOddPrimePeriodSet R →
        ‖coefficient R hR p‖ ≤ 1
  clip_le_synthesis_energy :
    ∀ (R : ℕ) (hR : 56 ≤ R),
      lowOwnerCanonicalSignedStokesClipBoundary R ≤
        lowOwnerStokesPrimePeriodSynthesisEnergy
          R hR (coefficient R hR)


/-! ## Lower-envelope scaled coefficient frame

The RH consumer does not require unit coefficients.  Its native scale is the
lower Mertens envelope `K`.  The same maximum-alignment argument therefore
extends to any specified coefficient family whose squared norms are bounded by
`K`.
-/

/-- If every reciprocal prime-period coefficient has squared norm at most
`K`, its complete diagonal/off-diagonal envelope is at most `K` times the
coefficient-free frame majorant. -/
theorem primePeriodReciprocalCoefficientEnvelope_le_mul_frameMajorant
    (W : PrimeWheelFiniteSystem) (N : ℕ) (S : Finset ℕ)
    (a : ℕ → ℂ) (K : ℝ)
    (hK : 0 ≤ K)
    (ha : ∀ p ∈ S, ‖a p‖ ^ 2 ≤ K) :
    primePeriodReciprocalCoefficientEnvelope W N S a ≤
      K * primePeriodReciprocalFrameMajorant W N S := by
  have hdiagSum :
      (∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2 * ‖a p‖ ^ 2) ≤
        K * ∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpw : 0 ≤ ((1 : ℝ) / (p : ℝ)) ^ 2 := sq_nonneg _
    calc
      ((1 : ℝ) / (p : ℝ)) ^ 2 * ‖a p‖ ^ 2 ≤
          ((1 : ℝ) / (p : ℝ)) ^ 2 * K :=
        mul_le_mul_of_nonneg_left (ha p hp) hpw
      _ = K * ((1 : ℝ) / (p : ℝ)) ^ 2 := by ring
  have hdiag :
      (N : ℝ) *
          (∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2 * ‖a p‖ ^ 2) ≤
        K * primePeriodReciprocalDiagonalMajorant N S := by
    unfold primePeriodReciprocalDiagonalMajorant
    have hN : 0 ≤ (N : ℝ) := by positivity
    calc
      (N : ℝ) *
          (∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2 * ‖a p‖ ^ 2) ≤
        (N : ℝ) * (K * ∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hdiagSum hN
      _ = K * ((N : ℝ) *
          ∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2) := by ring
  have hnormMul :
      ∀ p ∈ S, ∀ q ∈ S, ‖a p‖ * ‖a q‖ ≤ K := by
    intro p hp q hq
    have hp0 : 0 ≤ ‖a p‖ := norm_nonneg _
    have hq0 : 0 ≤ ‖a q‖ := norm_nonneg _
    have hprod0 : 0 ≤ ‖a p‖ * ‖a q‖ := mul_nonneg hp0 hq0
    have hsquare :
        (‖a p‖ * ‖a q‖) ^ 2 ≤ K ^ 2 := by
      calc
        (‖a p‖ * ‖a q‖) ^ 2 =
            ‖a p‖ ^ 2 * ‖a q‖ ^ 2 := by ring
        _ ≤ K * K :=
          mul_le_mul (ha p hp) (ha q hq) (sq_nonneg _) hK
        _ = K ^ 2 := by ring
    nlinarith [sq_nonneg (‖a p‖ * ‖a q‖ - K)]
  have hoff :
      (∑ p ∈ S,
        ∑ q ∈ S.erase p,
          (((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
              ‖primeWheelDirichletKernel W N
                (primePeriodFrequency W p - primePeriodFrequency W q)‖) *
            (‖a p‖ * ‖a q‖)) ≤
        K * primePeriodReciprocalOffDiagonalMajorant W N S := by
    unfold primePeriodReciprocalOffDiagonalMajorant
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hqS : q ∈ S := (Finset.mem_erase.mp hq).2
    have hw :
        0 ≤
          ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
            ‖primeWheelDirichletKernel W N
              (primePeriodFrequency W p - primePeriodFrequency W q)‖ := by
      positivity
    calc
      (((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
          ‖primeWheelDirichletKernel W N
            (primePeriodFrequency W p - primePeriodFrequency W q)‖) *
          (‖a p‖ * ‖a q‖) ≤
        (((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
          ‖primeWheelDirichletKernel W N
            (primePeriodFrequency W p - primePeriodFrequency W q)‖) * K :=
          mul_le_mul_of_nonneg_left (hnormMul p hp q hqS) hw
      _ = K *
        (((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
          ‖primeWheelDirichletKernel W N
            (primePeriodFrequency W p - primePeriodFrequency W q)‖) := by ring
  unfold primePeriodReciprocalCoefficientEnvelope
    primePeriodReciprocalFrameMajorant
  nlinarith

/-- Lower-envelope-scaled physical coefficient interface.  Unlike the earlier
unit interface, this is stated at exactly the `R^2*K` scale consumed by the
returned-core induction.  A useful instantiation must still supply an
arithmetically fixed coefficient constructor. -/
def LowOwnerStokesClipPrimePeriodCoefficientBounded
    (coefficient : (R : ℕ) → (hR : 56 ≤ R) → ℕ → ℂ) : Prop :=
  ∀ (R : ℕ) (K : ℝ) (hR : 56 ≤ R),
    LowerMertensCriticalEnvelope R K →
      (∀ p ∈ lowOwnerStokesOddPrimePeriodSet R,
        ‖coefficient R hR p‖ ^ 2 ≤ K) ∧
      lowOwnerCanonicalSignedStokesClipBoundary R ≤
        primePeriodReciprocalCoefficientEnvelope
          (lowOwnerStokesNaturalWheelSystem R hR)
          (squareRootEndpoint R)
          (lowOwnerStokesOddPrimePeriodSet R)
          (coefficient R hR)

/-- Any *fixed physical* coefficient constructor satisfying the preceding
lower-envelope interface yields the native `R^2*K` clip estimate immediately. -/
theorem clip_le_five_fourths_root_sq_mul_lowerEnvelope_of_coefficientBounded
    (coefficient : (R : ℕ) → (hR : 56 ≤ R) → ℕ → ℂ)
    (hCoeff : LowOwnerStokesClipPrimePeriodCoefficientBounded coefficient) :
    ∀ (R : ℕ) (K : ℝ) (hR : 56 ≤ R),
      LowerMertensCriticalEnvelope R K →
      lowOwnerCanonicalSignedStokesClipBoundary R ≤
        (5 / 4 : ℝ) * (R : ℝ) ^ 2 * K := by
  intro R K hR hK
  rcases hCoeff R K hR hK with ⟨hcoeff, hclip⟩
  have henv :=
    primePeriodReciprocalCoefficientEnvelope_le_mul_frameMajorant
      (lowOwnerStokesNaturalWheelSystem R hR)
      (squareRootEndpoint R)
      (lowOwnerStokesOddPrimePeriodSet R)
      (coefficient R hR) K hK.1 hcoeff
  have hframe :=
    lowOwnerStokesOddPrimePeriodFrameMajorant_le_five_fourths_root_sq R hR
  calc
    lowOwnerCanonicalSignedStokesClipBoundary R ≤
        primePeriodReciprocalCoefficientEnvelope
          (lowOwnerStokesNaturalWheelSystem R hR)
          (squareRootEndpoint R)
          (lowOwnerStokesOddPrimePeriodSet R)
          (coefficient R hR) := hclip
    _ ≤ K * lowOwnerStokesOddPrimePeriodFrameMajorant R hR := by
      simpa [lowOwnerStokesOddPrimePeriodFrameMajorant] using henv
    _ ≤ K * ((5 / 4 : ℝ) * (R : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hframe hK.1
    _ = (5 / 4 : ℝ) * (R : ℝ) ^ 2 * K := by ring


/-! ## Double-corner Fubini is the moved threshold incidence

The signed double-corner Fubini introduced by the clipped-threshold descent is
not an additional analytic coordinate.  It is exactly the current threshold
incidence evaluated at the moved `r`-child.
-/

/-- **Exact child-incidence identification.** -/
theorem lowOwnerThresholdDoubleCornerFubini_eq_movedIncidence
    {R p r n : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime)
    (hpr : p < r) (hn : 0 < n) :
    lowOwnerThresholdDoubleCornerFubini R p r n =
      lowOwnerThresholdOwnerIncidenceWeight R p (r * n) := by
  have h :=
    lowOwnerThresholdSecondOwnerDifference_eq_current_sub_doubleCornerFubini
      (R := R) (p := p) (r := r) (n := n)
      hR hp hr hpr hn
  unfold lowOwnerThresholdSecondOwnerDifference at h
  linarith

/-- The signed left double-corner descent can therefore be written without the
auxiliary Fubini object: the residual is the literal moved-child incidence. -/
theorem lowOwnerThresholdIncidencePairMass_eq_neg_leftMovedIncidence
    {R p r a b : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (haSq : Squarefree a) (hbSq : Squarefree b)
    (ha : 0 < a) (hb : 0 < b)
    (hra : r ∣ a) (hrb : ¬ r ∣ b) :
    let u := squarefreePrimeFamilyParent r a
    let v := squarefreePrimeFamilyParent r b
    lowOwnerThresholdIncidencePairMass R p (a, b) =
      -postRootZeroTargetPairExcess (u, v) *
        lowOwnerThresholdOwnerIncidenceWeight R p (r * u) *
        lowOwnerThresholdOwnerIncidenceWeight R p v := by
  dsimp only
  have h :=
    lowOwnerThresholdIncidencePairMass_eq_neg_leftDoubleCornerFubini
      (R := R) (p := p) (r := r) (a := a) (b := b)
      hR hp hr hpr haSq hbSq ha hb hra hrb
  dsimp only at h
  rw [lowOwnerThresholdDoubleCornerFubini_eq_movedIncidence
      hR hp hr hpr
      (squarefreePrimeFamilyParent_pos_public hr ha)] at h
  exact h

/-- Symmetric moved-child form. -/
theorem lowOwnerThresholdIncidencePairMass_eq_neg_rightMovedIncidence
    {R p r a b : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (haSq : Squarefree a) (hbSq : Squarefree b)
    (ha : 0 < a) (hb : 0 < b)
    (hra : ¬ r ∣ a) (hrb : r ∣ b) :
    let u := squarefreePrimeFamilyParent r a
    let v := squarefreePrimeFamilyParent r b
    lowOwnerThresholdIncidencePairMass R p (a, b) =
      -postRootZeroTargetPairExcess (u, v) *
        lowOwnerThresholdOwnerIncidenceWeight R p u *
        lowOwnerThresholdOwnerIncidenceWeight R p (r * v) := by
  dsimp only
  have h :=
    lowOwnerThresholdIncidencePairMass_eq_neg_rightDoubleCornerFubini
      (R := R) (p := p) (r := r) (a := a) (b := b)
      hR hp hr hpr haSq hbSq ha hb hra hrb
  dsimp only at h
  rw [lowOwnerThresholdDoubleCornerFubini_eq_movedIncidence
      hR hp hr hpr
      (squarefreePrimeFamilyParent_pos_public hr hb)] at h
  exact h


/-! ## Direct owner-to-frame identification is impossible

A genuine admissibility proof must collapse the physical large-owner escape
payload into the sub-root natural-wheel coordinates.  The canonical Stokes
schedule itself cannot be reused as the prime-period frame schedule: its first
remaining owner lies above half the physical clock, whereas every frame period
prime lies strictly below R.
-/

/-- Every active natural prime-period coordinate lies strictly below the root
parameter in the RH-consumer regime. -/
theorem lowOwnerStokesOddPrimePeriodSet_lt_root
    {R p : ℕ} (hR : 56 ≤ R)
    (hp : p ∈ lowOwnerStokesOddPrimePeriodSet R) :
    p < R := by
  have hpWheel : p ∈ lowOwnerStokesWheelPrimes R :=
    (Finset.mem_erase.mp hp).2
  have hpCut : p ≤ Nat.sqrt (squareRootEndpoint R) := by
    unfold lowOwnerStokesWheelPrimes at hpWheel
    exact (mem_primesUpTo.mp hpWheel).2
  have hroot : Nat.sqrt (squareRootEndpoint R) < R := by
    apply (Nat.sqrt_lt').2
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  exact hpCut.trans_lt hroot

/-- In the RH-consumer regime the physical half-clock already lies at or above
the root parameter. -/
theorem root_le_half_squareRootEndpoint
    {R : ℕ} (hR : 56 ≤ R) :
    R ≤ squareRootEndpoint R / 2 := by
  unfold squareRootEndpoint
  omega

/-- **Support no-go for a direct admissibility map.**  The head of every
nonempty canonical Stokes schedule is outside the natural odd prime-period
frame.  Thus the physical escape owner cannot simply be relabelled as a frame
mode; a real proof must first perform the signed large-owner -> sub-root
collapse. -/
theorem lowOwnerFirstOwnerCanonicalStokesSchedule_head_not_mem_primePeriodFrame
    {R p q : ℕ} {qs : List ℕ}
    (hR : 56 ≤ R)
    (hps : lowOwnerFirstOwnerCanonicalStokesSchedule R p = q :: qs) :
    q ∉ lowOwnerStokesOddPrimePeriodSet R := by
  intro hqFrame
  have hqRoot : q < R :=
    lowOwnerStokesOddPrimePeriodSet_lt_root hR hqFrame
  have hqTop :=
    lowOwnerFirstOwnerCanonicalStokesSchedule_head_gt_half
      (R := R) (p := p) (q := q) (qs := qs) (by omega) hps
  have hRhalf : R ≤ squareRootEndpoint R / 2 :=
    root_le_half_squareRootEndpoint hR
  omega


/-! ## One-step physical clip factorization before energy

The pair Stokes escape is a Gram boundary of one-dimensional signed amplitudes.
This is the correct algebraic surface for a physical admissibility theorem:
large-owner escape amplitudes must be transported to sub-root reciprocal
coordinates before any square or norm is taken.
-/

/-- Signed scalar amplitude on a finite physical carrier. -/
def lowOwnerStokesSignedScalarAmplitude
    (S : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, othelloRealMoebius n * g n

/-- Fresh-owner finite-difference amplitude on a finite carrier. -/
def lowOwnerStokesSignedOwnerDifferenceAmplitude
    (r : ℕ) (S : Finset ℕ) (g : ℕ → ℝ) : ℝ :=
  lowOwnerStokesSignedScalarAmplitude S
    (fun n => g n - g (primeCarrierToggle r n))

private theorem sum_product_othello_separable
    (S T : Finset ℕ) (g h : ℕ → ℝ) :
    (∑ mn ∈ S.product T,
      othelloRealMoebiusPair mn * (g mn.1 * h mn.2)) =
      lowOwnerStokesSignedScalarAmplitude S g *
        lowOwnerStokesSignedScalarAmplitude T h := by
  unfold lowOwnerStokesSignedScalarAmplitude
    othelloRealMoebiusPair
  rw [Finset.sum_product]
  calc
    (∑ a ∈ S, ∑ b ∈ T,
      (othelloRealMoebius a * othelloRealMoebius b) * (g a * h b)) =
      ∑ a ∈ S,
        (othelloRealMoebius a * g a) *
          (∑ b ∈ T, othelloRealMoebius b * h b) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _hb
        ring
    _ = (∑ a ∈ S, othelloRealMoebius a * g a) *
        (∑ b ∈ T, othelloRealMoebius b * h b) := by
      rw [Finset.sum_mul]

private theorem sum_product_othello_polarization
    (S T : Finset ℕ) (i b j : ℕ → ℝ) :
    (∑ mn ∈ S.product T,
      othelloRealMoebiusPair mn *
        (i mn.1 * i mn.2 -
          b mn.1 * b mn.2 -
          j mn.1 * j mn.2)) =
      lowOwnerStokesSignedScalarAmplitude S i *
          lowOwnerStokesSignedScalarAmplitude T i -
        lowOwnerStokesSignedScalarAmplitude S b *
          lowOwnerStokesSignedScalarAmplitude T b -
        lowOwnerStokesSignedScalarAmplitude S j *
          lowOwnerStokesSignedScalarAmplitude T j := by
  calc
    (∑ mn ∈ S.product T,
      othelloRealMoebiusPair mn *
        (i mn.1 * i mn.2 -
          b mn.1 * b mn.2 -
          j mn.1 * j mn.2)) =
      (∑ mn ∈ S.product T,
        othelloRealMoebiusPair mn * (i mn.1 * i mn.2)) -
      (∑ mn ∈ S.product T,
        othelloRealMoebiusPair mn * (b mn.1 * b mn.2)) -
      (∑ mn ∈ S.product T,
        othelloRealMoebiusPair mn * (j mn.1 * j mn.2)) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro mn _hmn
          ring
    _ = _ := by
      rw [sum_product_othello_separable,
        sum_product_othello_separable,
        sum_product_othello_separable]

private theorem polarization_leftDifference
    (r : ℕ) (i b j : ℕ → ℝ) (mn : ℕ × ℕ) :
    (i mn.1 * i mn.2 -
        b mn.1 * b mn.2 -
        j mn.1 * j mn.2) -
      (i (primeCarrierToggle r mn.1) * i mn.2 -
        b (primeCarrierToggle r mn.1) * b mn.2 -
        j (primeCarrierToggle r mn.1) * j mn.2) =
      (i mn.1 - i (primeCarrierToggle r mn.1)) * i mn.2 -
        (b mn.1 - b (primeCarrierToggle r mn.1)) * b mn.2 -
        (j mn.1 - j (primeCarrierToggle r mn.1)) * j mn.2 := by
  ring

/-- **Exact one-step clip Gram factorization.**

For a genuine larger owner r, the physical pair escape step is a bilinear
pairing of the signed escape amplitudes with the full surviving amplitudes,
plus one half of the owner-difference/interior pairing.  In particular, no
pointwise absolute value or cellwise square is needed to expose the scalar
boundary amplitudes. -/
theorem lowOwnerFirstOwner_pairBoundaryStep_eq_signedAmplitudeProducts
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    let A := lowOwnerFirstOwnerBaseFiber R p sig
    let E := lowOwnerFirstOwnerStokesDirichletClipFace R p sig r
    let I := primeInteriorPart r A
    let inc := lowOwnerDirichletIncidenceCoefficient R p
    let base := lowOwnerDirichletBaseCoefficient R
    let ret := lowOwnerDirichletReturnedCoefficient R p
    pairWeightedStokesBoundaryStep r
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
        (lowOwnerFirstOwnerDirichletPolarizationScalar R p) =
      (lowOwnerStokesSignedScalarAmplitude E inc *
          lowOwnerStokesSignedScalarAmplitude A inc -
        lowOwnerStokesSignedScalarAmplitude E base *
          lowOwnerStokesSignedScalarAmplitude A base -
        lowOwnerStokesSignedScalarAmplitude E ret *
          lowOwnerStokesSignedScalarAmplitude A ret) +
      (1 / 2 : ℝ) *
        (lowOwnerStokesSignedOwnerDifferenceAmplitude r I inc *
            lowOwnerStokesSignedScalarAmplitude E inc -
          lowOwnerStokesSignedOwnerDifferenceAmplitude r I base *
            lowOwnerStokesSignedScalarAmplitude E base -
          lowOwnerStokesSignedOwnerDifferenceAmplitude r I ret *
            lowOwnerStokesSignedScalarAmplitude E ret) := by
  dsimp only
  rw [lowOwnerFirstOwner_pairBoundaryStep_eq_dirichletClipFaces hp hr hpr]
  unfold lowOwnerFirstOwnerDirichletPolarizationScalar
  have hleft :=
    sum_product_othello_polarization
      (lowOwnerFirstOwnerStokesDirichletClipFace R p sig r)
      (lowOwnerFirstOwnerBaseFiber R p sig)
      (lowOwnerDirichletIncidenceCoefficient R p)
      (lowOwnerDirichletBaseCoefficient R)
      (lowOwnerDirichletReturnedCoefficient R p)
  have hright :
      (∑ mn ∈
        (primeInteriorPart r (lowOwnerFirstOwnerBaseFiber R p sig)).product
          (lowOwnerFirstOwnerStokesDirichletClipFace R p sig r),
        othelloRealMoebiusPair mn *
          ((lowOwnerDirichletIncidenceCoefficient R p mn.1 *
              lowOwnerDirichletIncidenceCoefficient R p mn.2 -
            lowOwnerDirichletBaseCoefficient R mn.1 *
              lowOwnerDirichletBaseCoefficient R mn.2 -
            lowOwnerDirichletReturnedCoefficient R p mn.1 *
              lowOwnerDirichletReturnedCoefficient R p mn.2) -
           (lowOwnerDirichletIncidenceCoefficient R p
                (primeCarrierToggle r mn.1) *
              lowOwnerDirichletIncidenceCoefficient R p mn.2 -
            lowOwnerDirichletBaseCoefficient R
                (primeCarrierToggle r mn.1) *
              lowOwnerDirichletBaseCoefficient R mn.2 -
            lowOwnerDirichletReturnedCoefficient R p
                (primeCarrierToggle r mn.1) *
              lowOwnerDirichletReturnedCoefficient R p mn.2))) =
        lowOwnerStokesSignedOwnerDifferenceAmplitude r
            (primeInteriorPart r (lowOwnerFirstOwnerBaseFiber R p sig))
            (lowOwnerDirichletIncidenceCoefficient R p) *
          lowOwnerStokesSignedScalarAmplitude
            (lowOwnerFirstOwnerStokesDirichletClipFace R p sig r)
            (lowOwnerDirichletIncidenceCoefficient R p) -
        lowOwnerStokesSignedOwnerDifferenceAmplitude r
            (primeInteriorPart r (lowOwnerFirstOwnerBaseFiber R p sig))
            (lowOwnerDirichletBaseCoefficient R) *
          lowOwnerStokesSignedScalarAmplitude
            (lowOwnerFirstOwnerStokesDirichletClipFace R p sig r)
            (lowOwnerDirichletBaseCoefficient R) -
        lowOwnerStokesSignedOwnerDifferenceAmplitude r
            (primeInteriorPart r (lowOwnerFirstOwnerBaseFiber R p sig))
            (lowOwnerDirichletReturnedCoefficient R p) *
          lowOwnerStokesSignedScalarAmplitude
            (lowOwnerFirstOwnerStokesDirichletClipFace R p sig r)
            (lowOwnerDirichletReturnedCoefficient R p) := by
    calc
      _ =
        (∑ mn ∈
          (primeInteriorPart r (lowOwnerFirstOwnerBaseFiber R p sig)).product
            (lowOwnerFirstOwnerStokesDirichletClipFace R p sig r),
          othelloRealMoebiusPair mn *
            ((lowOwnerDirichletIncidenceCoefficient R p mn.1 -
                lowOwnerDirichletIncidenceCoefficient R p
                  (primeCarrierToggle r mn.1)) *
                lowOwnerDirichletIncidenceCoefficient R p mn.2 -
              (lowOwnerDirichletBaseCoefficient R mn.1 -
                lowOwnerDirichletBaseCoefficient R
                  (primeCarrierToggle r mn.1)) *
                lowOwnerDirichletBaseCoefficient R mn.2 -
              (lowOwnerDirichletReturnedCoefficient R p mn.1 -
                lowOwnerDirichletReturnedCoefficient R p
                  (primeCarrierToggle r mn.1)) *
                lowOwnerDirichletReturnedCoefficient R p mn.2)) := by
            apply Finset.sum_congr rfl
            intro mn _hmn
            rw [polarization_leftDifference]
      _ = _ := by
        unfold lowOwnerStokesSignedOwnerDifferenceAmplitude
        exact sum_product_othello_polarization
          (primeInteriorPart r (lowOwnerFirstOwnerBaseFiber R p sig))
          (lowOwnerFirstOwnerStokesDirichletClipFace R p sig r)
          (fun n => lowOwnerDirichletIncidenceCoefficient R p n -
            lowOwnerDirichletIncidenceCoefficient R p
              (primeCarrierToggle r n))
          (fun n => lowOwnerDirichletBaseCoefficient R n -
            lowOwnerDirichletBaseCoefficient R
              (primeCarrierToggle r n))
          (fun n => lowOwnerDirichletReturnedCoefficient R p n -
            lowOwnerDirichletReturnedCoefficient R p
              (primeCarrierToggle r n))
  rw [hleft, hright]


/-! ## Literal clip amplitudes are owner differences

On the Stokes escape face the fresh r-child lies outside the physical
Dirichlet clock.  Hence the child value of every Dirichlet coordinate is zero,
and the escape-side value is literally its fresh-owner finite difference.
-/

/-- The base Dirichlet coefficient of the escaped r-child is zero. -/
theorem lowOwnerFirstOwnerStokesClip_base_child_eq_zero
    {R p r n : ℕ} {sig : Finset ℕ}
    (hn : n ∈ lowOwnerFirstOwnerStokesDirichletClipFace R p sig r) :
    lowOwnerDirichletBaseCoefficient R (r * n) = 0 := by
  rcases mem_lowOwnerFirstOwnerStokesDirichletClipFace.mp hn with
    ⟨_hbase, _hrn, hclip⟩
  unfold lowOwnerDirichletBaseCoefficient
  exact lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hclip

/-- The returned p-coordinate of the escaped r-child is also zero. -/
theorem lowOwnerFirstOwnerStokesClip_returned_child_eq_zero
    {R p r n : ℕ} {sig : Finset ℕ}
    (hp : 1 ≤ p)
    (hn : n ∈ lowOwnerFirstOwnerStokesDirichletClipFace R p sig r) :
    lowOwnerDirichletReturnedCoefficient R p (r * n) = 0 := by
  rcases mem_lowOwnerFirstOwnerStokesDirichletClipFace.mp hn with
    ⟨_hbase, _hrn, hclip⟩
  have hle : r * n ≤ p * (r * n) := by
    calc
      r * n = 1 * (r * n) := by simp
      _ ≤ p * (r * n) := Nat.mul_le_mul_right (r * n) hp
  unfold lowOwnerDirichletReturnedCoefficient
  exact lowOwnerPhysicalDirichletWeight_eq_zero_of_lt (hclip.trans_le hle)

/-- Therefore the incidence coefficient itself vanishes at the escaped child. -/
theorem lowOwnerFirstOwnerStokesClip_incidence_child_eq_zero
    {R p r n : ℕ} {sig : Finset ℕ}
    (hp : 1 ≤ p)
    (hn : n ∈ lowOwnerFirstOwnerStokesDirichletClipFace R p sig r) :
    lowOwnerDirichletIncidenceCoefficient R p (r * n) = 0 := by
  unfold lowOwnerDirichletIncidenceCoefficient
  rw [lowOwnerFirstOwnerStokesClip_base_child_eq_zero hn,
    lowOwnerFirstOwnerStokesClip_returned_child_eq_zero hp hn]
  ring

/-- On a literal clip, the physical incidence is exactly its r-owner
difference. -/
theorem lowOwnerFirstOwnerStokesClip_incidence_eq_ownerDifference
    {R p r n : ℕ} {sig : Finset ℕ}
    (hrn : ¬ r ∣ n) (hp : 1 ≤ p)
    (hn : n ∈ lowOwnerFirstOwnerStokesDirichletClipFace R p sig r) :
    lowOwnerDirichletIncidenceCoefficient R p n =
      lowOwnerDirichletOwnerDifference r
        (lowOwnerDirichletIncidenceCoefficient R p) n := by
  unfold lowOwnerDirichletOwnerDifference
  rw [primeCarrierToggle_of_not_dvd hrn]
  change lowOwnerDirichletIncidenceCoefficient R p n =
    lowOwnerDirichletIncidenceCoefficient R p n -
      lowOwnerDirichletIncidenceCoefficient R p (n * r)
  have hzero :=
    lowOwnerFirstOwnerStokesClip_incidence_child_eq_zero hp hn
  rw [Nat.mul_comm] at hzero
  rw [hzero]
  ring

/-- **Exact clip currency decomposition.**

A literal physical Stokes escape coefficient is the reciprocal-Euler threshold
second difference plus the endpoint clipped-difference.  Thus the endpoint
piece is not removed merely by changing to reciprocal currency; it remains as
an explicit signed term which must be globally reassembled. -/
theorem lowOwnerFirstOwnerStokesClip_incidence_eq_thresholdSecond_add_endpointClip
    {R p r n : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime)
    (hn : n ∈ lowOwnerFirstOwnerStokesDirichletClipFace R p sig r) :
    lowOwnerDirichletIncidenceCoefficient R p n =
      lowOwnerThresholdSecondOwnerDifference R p r n +
        lowOwnerThresholdClippedDifference
          p r n (squareRootEndpoint R) := by
  have hrn : ¬ r ∣ n :=
    (mem_lowOwnerFirstOwnerStokesDirichletClipFace.mp hn).2.1
  rw [lowOwnerFirstOwnerStokesClip_incidence_eq_ownerDifference
      hrn hp.one_le hn]
  exact
    lowOwnerDirichletIncidence_ownerDifference_eq_threshold_add_endpointClippedDifference
      hR hp.one_le hr.one_le


/-! ## The endpoint clip carries the top-scale Mertens amplitude

The reciprocal-Euler conversion above leaves one literal endpoint clipped
difference.  After the already-compiled signed signature reassembly, that term
is not lower-scale: it is exactly M(X_R).
-/

/-- Fully assembled endpoint clipped-difference amplitude on one auxiliary
p<r lens. -/
def lowOwnerStokesEndpointClippedDifferenceAmplitude
    (R p r : ℕ) : ℝ :=
  ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
    lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
      R p sig r (squareRootEndpoint R)

/-- **Endpoint clip = top-scale Mertens.**

The auxiliary owner labels disappear before any norm: the physical endpoint
clipped-difference is exactly the Mertens prefix at X_R. -/
theorem lowOwnerStokesEndpointClippedDifferenceAmplitude_eq_mertensEndpoint
    {R p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerStokesEndpointClippedDifferenceAmplitude R p r =
      (mertensSummatoryInt (squareRootEndpoint R) : ℝ) := by
  unfold lowOwnerStokesEndpointClippedDifferenceAmplitude
  exact
    sum_signature_branchClippedDifferenceTotalAmplitude_eq_mertens
      hp hr hpr (le_refl (squareRootEndpoint R))

/-- The endpoint carried by the clip lies outside the strict lower-envelope
range as soon as R is nontrivial. -/
theorem root_le_squareRootEndpoint
    {R : ℕ} (hR : 2 ≤ R) :
    R ≤ squareRootEndpoint R := by
  unfold squareRootEndpoint
  have h : R + 1 ≤ R ^ 2 := by nlinarith
  omega


/-! ## One-step clip as an exact difference of scalar squares

Weighted Othello turns the interior finite-difference amplitude into the
difference between the total scalar amplitude and its literal escape
amplitude.  Substituting this into the preceding product factorization makes
each scalar Stokes boundary a difference of two squares.
-/

/-- Half of the signed interior owner-difference amplitude is exactly total
amplitude minus escape amplitude. -/
theorem half_lowOwnerStokesSignedOwnerDifferenceAmplitude_eq_total_sub_escape
    {r : ℕ} (hr : r.Prime) (S : Finset ℕ) (g : ℕ → ℝ) :
    (1 / 2 : ℝ) *
        lowOwnerStokesSignedOwnerDifferenceAmplitude r
          (primeInteriorPart r S) g =
      lowOwnerStokesSignedScalarAmplitude S g -
        lowOwnerStokesSignedScalarAmplitude (primeEscapePart r S) g := by
  have h :=
    sum_weightedMoebius_eq_escape_add_half_interiorDifference
      hr S g
  unfold lowOwnerStokesSignedScalarAmplitude
    lowOwnerStokesSignedOwnerDifferenceAmplitude at *
  linarith

/-- On one returned-core first-owner cell, the fresh-r escape amplitude is the
literal physical Dirichlet clip amplitude. -/
theorem half_lowOwnerStokesSignedOwnerDifferenceAmplitude_eq_total_sub_dirichletClip
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (g : ℕ → ℝ) :
    (1 / 2 : ℝ) *
        lowOwnerStokesSignedOwnerDifferenceAmplitude r
          (primeInteriorPart r (lowOwnerFirstOwnerBaseFiber R p sig)) g =
      lowOwnerStokesSignedScalarAmplitude
          (lowOwnerFirstOwnerBaseFiber R p sig) g -
        lowOwnerStokesSignedScalarAmplitude
          (lowOwnerFirstOwnerStokesDirichletClipFace R p sig r) g := by
  have h :=
    half_lowOwnerStokesSignedOwnerDifferenceAmplitude_eq_total_sub_escape
      hr (lowOwnerFirstOwnerBaseFiber R p sig) g
  rw [lowOwnerFirstOwner_primeEscapePart_eq_dirichletClipFace hp hr hpr] at h
  exact h

/-- **Exact one-step square-decrement normal form.**

For each of the three scalar coordinates (incidence/base/returned), the Stokes
escape contribution is the decrease of its signed scalar square under removal
of the escape amplitude.  The polarization boundary is their signed
combination. -/
theorem lowOwnerFirstOwner_pairBoundaryStep_eq_signedSquareDecrements
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    let A := lowOwnerFirstOwnerBaseFiber R p sig
    let E := lowOwnerFirstOwnerStokesDirichletClipFace R p sig r
    let inc := lowOwnerDirichletIncidenceCoefficient R p
    let base := lowOwnerDirichletBaseCoefficient R
    let ret := lowOwnerDirichletReturnedCoefficient R p
    pairWeightedStokesBoundaryStep r
        (lowOwnerFirstOwnerSignedCellPairCarrier R p sig)
        (lowOwnerFirstOwnerDirichletPolarizationScalar R p) =
      (lowOwnerStokesSignedScalarAmplitude A inc ^ 2 -
        (lowOwnerStokesSignedScalarAmplitude A inc -
          lowOwnerStokesSignedScalarAmplitude E inc) ^ 2) -
      (lowOwnerStokesSignedScalarAmplitude A base ^ 2 -
        (lowOwnerStokesSignedScalarAmplitude A base -
          lowOwnerStokesSignedScalarAmplitude E base) ^ 2) -
      (lowOwnerStokesSignedScalarAmplitude A ret ^ 2 -
        (lowOwnerStokesSignedScalarAmplitude A ret -
          lowOwnerStokesSignedScalarAmplitude E ret) ^ 2) := by
  dsimp only
  rw [lowOwnerFirstOwner_pairBoundaryStep_eq_signedAmplitudeProducts
      hp hr hpr]
  have hi :=
    half_lowOwnerStokesSignedOwnerDifferenceAmplitude_eq_total_sub_dirichletClip
      (R := R) (p := p) (r := r) (sig := sig) hp hr hpr
      (lowOwnerDirichletIncidenceCoefficient R p)
  have hb :=
    half_lowOwnerStokesSignedOwnerDifferenceAmplitude_eq_total_sub_dirichletClip
      (R := R) (p := p) (r := r) (sig := sig) hp hr hpr
      (lowOwnerDirichletBaseCoefficient R)
  have hj :=
    half_lowOwnerStokesSignedOwnerDifferenceAmplitude_eq_total_sub_dirichletClip
      (R := R) (p := p) (r := r) (sig := sig) hp hr hpr
      (lowOwnerDirichletReturnedCoefficient R p)
  nlinarith

end RHLean.Proof
