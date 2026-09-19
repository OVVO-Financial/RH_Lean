import Mathlib
import «research.GLOBAL_RETURNED_CORE_FINAL_STOKES_RH_BRIDGE»
import «research.GLOBAL_RETURNED_CORE_STOKES_NATURAL_PERIOD_WHEEL»
import «research.GLOBAL_RETURNED_CORE_STOKES_CLIP_AMPLITUDE_FACTOR»
import «research.STOKES_ENDPOINT_MAX_ALIGNMENT_FRAME»
import «research.STABLE_FAR_PERRON_QUARTER_FRAME_BOUND»

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


/-- Prime 3 is always an active odd Stokes period in the RH-consumer regime. -/
theorem three_mem_lowOwnerStokesOddPrimePeriodSet
    {R : ℕ} (hR : 56 ≤ R) :
    3 ∈ lowOwnerStokesOddPrimePeriodSet R := by
  have hcut : 3 ≤ Nat.sqrt (squareRootEndpoint R) := by
    have h5 := five_le_lowOwnerStokesWheelCutoff hR
    omega
  have h3wheel : 3 ∈ lowOwnerStokesWheelPrimes R := by
    unfold lowOwnerStokesWheelPrimes
    exact mem_primesUpTo.mpr ⟨by norm_num, hcut⟩
  unfold lowOwnerStokesOddPrimePeriodSet
  exact Finset.mem_erase.mpr ⟨by norm_num, h3wheel⟩

/-- The reciprocal-square diagonal contains at least the prime-3 contribution. -/
theorem one_ninth_le_lowOwnerStokesOddPrimePeriodSet_reciprocalSquareMass
    {R : ℕ} (hR : 56 ≤ R) :
    (1 / 9 : ℝ) ≤
      ∑ p ∈ lowOwnerStokesOddPrimePeriodSet R,
        ((1 : ℝ) / (p : ℝ)) ^ 2 := by
  have h3 := three_mem_lowOwnerStokesOddPrimePeriodSet hR
  have hsplit := Finset.sum_erase_add
    (s := lowOwnerStokesOddPrimePeriodSet R)
    (f := fun p => ((1 : ℝ) / (p : ℝ)) ^ 2) h3
  have hrest :
      0 ≤ ∑ p ∈ (lowOwnerStokesOddPrimePeriodSet R).erase 3,
        ((1 : ℝ) / (p : ℝ)) ^ 2 := by
    positivity
  norm_num at hsplit ⊢
  nlinarith

/-- The natural prime-period frame is itself root-scale from below.  No
off-diagonal alignment is needed: the prime-3 diagonal alone gives
Frame_R >= R^2/18 for every R >= 56. -/
theorem root_sq_over_eighteen_le_lowOwnerStokesOddPrimePeriodFrameMajorant
    {R : ℕ} (hR : 56 ≤ R) :
    (R : ℝ) ^ 2 / 18 ≤
      lowOwnerStokesOddPrimePeriodFrameMajorant R hR := by
  let W := lowOwnerStokesNaturalWheelSystem R hR
  let X := squareRootEndpoint R
  let S := lowOwnerStokesOddPrimePeriodSet R
  have hmass :
      (1 / 9 : ℝ) ≤
        ∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2 := by
    simpa [S] using
      one_ninth_le_lowOwnerStokesOddPrimePeriodSet_reciprocalSquareMass hR
  have hoff :
      0 ≤ primePeriodReciprocalOffDiagonalMajorant W X S := by
    unfold primePeriodReciprocalOffDiagonalMajorant
    apply Finset.sum_nonneg
    intro p hp
    apply Finset.sum_nonneg
    intro q hq
    positivity
  have hdiag :
      (X : ℝ) / 9 ≤ primePeriodReciprocalDiagonalMajorant X S := by
    unfold primePeriodReciprocalDiagonalMajorant
    have hX0 : 0 ≤ (X : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hmass hX0
    nlinarith
  have hframeX :
      (X : ℝ) / 9 ≤
        primePeriodReciprocalFrameMajorant W X S := by
    unfold primePeriodReciprocalFrameMajorant
    linarith
  have hnat : R ^ 2 ≤ 2 * squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : 2 ≤ R ^ 2 := by nlinarith
    omega
  have hreal :
      (R : ℝ) ^ 2 ≤ 2 * (squareRootEndpoint R : ℝ) := by
    exact_mod_cast hnat
  change (R : ℝ) ^ 2 / 18 ≤
    primePeriodReciprocalFrameMajorant W X S
  have hXreal : (X : ℝ) = (squareRootEndpoint R : ℝ) := by rfl
  rw [hXreal] at hframeX
  nlinarith

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


private theorem lowOwnerStokesFullPrimeSet_nonempty
    {R : ℕ} (hR : 56 ≤ R) :
    (primesUpTo (squareRootEndpoint R)).Nonempty := by
  refine ⟨2, mem_primesUpTo.mpr ⟨Nat.prime_two, ?_⟩⟩
  unfold squareRootEndpoint
  have hsq : 3 ≤ R ^ 2 := by nlinarith
  omega

/-- Largest physical first-owner prime on the square clock. -/
def lowOwnerStokesTopPrime (R : ℕ) (hR : 56 ≤ R) : ℕ :=
  (primesUpTo (squareRootEndpoint R)).max'
    (lowOwnerStokesFullPrimeSet_nonempty hR)

theorem lowOwnerStokesTopPrime_mem
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesTopPrime R hR ∈ primesUpTo (squareRootEndpoint R) := by
  exact Finset.max'_mem _ _

private theorem lowOwnerStokesEraseTop_nonempty
    {R : ℕ} (hR : 56 ≤ R) :
    ((primesUpTo (squareRootEndpoint R)).erase
      (lowOwnerStokesTopPrime R hR)).Nonempty := by
  have h5 : 5 ∈ primesUpTo (squareRootEndpoint R) := by
    apply mem_primesUpTo.mpr
    constructor
    · norm_num
    · unfold squareRootEndpoint
      have hsq : 6 ≤ R ^ 2 := by nlinarith
      omega
  have htop5 :
      5 ≤ lowOwnerStokesTopPrime R hR :=
    Finset.le_max' _ 5 h5
  have h2 : 2 ∈ primesUpTo (squareRootEndpoint R) := by
    exact mem_primesUpTo.mpr ⟨Nat.prime_two, by
      unfold squareRootEndpoint
      have hsq : 3 ≤ R ^ 2 := by nlinarith
      omega⟩
  have hne : 2 ≠ lowOwnerStokesTopPrime R hR := by omega
  exact ⟨2, Finset.mem_erase.mpr ⟨hne, h2⟩⟩

/-- Second-largest physical first-owner prime. -/
def lowOwnerStokesSecondPrime (R : ℕ) (hR : 56 ≤ R) : ℕ :=
  ((primesUpTo (squareRootEndpoint R)).erase
      (lowOwnerStokesTopPrime R hR)).max'
    (lowOwnerStokesEraseTop_nonempty hR)

theorem lowOwnerStokesSecondPrime_mem_erase
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesSecondPrime R hR ∈
      (primesUpTo (squareRootEndpoint R)).erase
        (lowOwnerStokesTopPrime R hR) := by
  exact Finset.max'_mem _ _


theorem lowOwnerStokesSecondPrime_prime
    {R : ℕ} (hR : 56 ≤ R) :
    (lowOwnerStokesSecondPrime R hR).Prime := by
  have hmem := (Finset.mem_erase.mp
    (lowOwnerStokesSecondPrime_mem_erase hR)).2
  exact (mem_primesUpTo.mp hmem).1

theorem lowOwnerStokesSecondPrime_lt_topPrime
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesSecondPrime R hR <
      lowOwnerStokesTopPrime R hR := by
  have hsErase := lowOwnerStokesSecondPrime_mem_erase hR
  have hsNe :
      lowOwnerStokesSecondPrime R hR ≠
        lowOwnerStokesTopPrime R hR :=
    (Finset.mem_erase.mp hsErase).1
  have hsMem := (Finset.mem_erase.mp hsErase).2
  have hsLe :
      lowOwnerStokesSecondPrime R hR ≤
        lowOwnerStokesTopPrime R hR :=
    Finset.le_max' _ _ hsMem
  omega

/-- The second-largest physical owner has exactly one remaining Stokes
coordinate, namely the largest physical prime. -/
theorem lowOwnerStokesSecondPrime_schedule_eq_single_top
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerFirstOwnerCanonicalStokesSchedule
        R (lowOwnerStokesSecondPrime R hR) =
      [lowOwnerStokesTopPrime R hR] := by
  let s := lowOwnerStokesSecondPrime R hR
  let t := lowOwnerStokesTopPrime R hR
  have hst : s < t := by
    simpa [s, t] using lowOwnerStokesSecondPrime_lt_topPrime hR
  have htMem : t ∈ primesUpTo (squareRootEndpoint R) := by
    simpa [t] using lowOwnerStokesTopPrime_mem hR
  have htFull : t ∈ squareRootCanonicalRoughDescendingPrimeSchedule R := by
    unfold squareRootCanonicalRoughDescendingPrimeSchedule
    exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).2 htMem
  have htSched :
      t ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R s := by
    simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using
      (show t ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ s < t
        from ⟨htFull, hst⟩)
  have huniq :
      ∀ q ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R s, q = t := by
    intro q hq
    have hqData :
        q ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ s < q := by
      simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using hq
    have hqMem : q ∈ primesUpTo (squareRootEndpoint R) := by
      unfold squareRootCanonicalRoughDescendingPrimeSchedule at hqData
      exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).1 hqData.1
    by_contra hqt
    have hqErase :
        q ∈ (primesUpTo (squareRootEndpoint R)).erase t :=
      Finset.mem_erase.mpr ⟨hqt, hqMem⟩
    have hqLeS : q ≤ s := by
      simpa [s, t] using
        Finset.le_max'
          ((primesUpTo (squareRootEndpoint R)).erase t) q hqErase
    omega
  have hnodup :=
    lowOwnerFirstOwnerCanonicalStokesSchedule_nodup R s
  generalize hsched : lowOwnerFirstOwnerCanonicalStokesSchedule R s = ps at htSched huniq hnodup
  cases ps with
  | nil =>
      simp at htSched
  | cons a tail =>
      have ha : a = t := huniq a (by simp)
      subst a
      cases tail with
      | nil =>
          rfl
      | cons b rest =>
          have hb : b = t := huniq b (by simp)
          subst b
          simp at hnodup

/-- The actual second-owner terminal packet is the exact quarter-weighted
top-prime mixed difference, already assembled over signatures. -/
theorem sum_lowOwnerStokesSecondPrimeTerminal_eq_neg_half_topDifferenceProduct
    {R : ℕ} (hR : 56 ≤ R) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet
        R (lowOwnerStokesSecondPrime R hR),
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary
        R (lowOwnerStokesSecondPrime R hR) sig) =
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet
        R (lowOwnerStokesSecondPrime R hR),
        (-(1 / 2 : ℝ) *
          lowOwnerStokesSignedAmplitude
            (primeInteriorPart (lowOwnerStokesTopPrime R hR)
              (lowOwnerFirstOwnerBaseFiber
                R (lowOwnerStokesSecondPrime R hR) sig))
            (lowOwnerStokesToggleDifference
              (lowOwnerStokesTopPrime R hR)
              (lowOwnerDirichletBaseCoefficient R)) *
          lowOwnerStokesSignedAmplitude
            (primeInteriorPart (lowOwnerStokesTopPrime R hR)
              (lowOwnerFirstOwnerBaseFiber
                R (lowOwnerStokesSecondPrime R hR) sig))
            (lowOwnerStokesToggleDifference
              (lowOwnerStokesTopPrime R hR)
              (lowOwnerDirichletReturnedCoefficient
                R (lowOwnerStokesSecondPrime R hR)))) := by
  exact
    sum_lowOwnerFirstOwnerTopTerminal_eq_neg_half_interiorDifferenceProduct_of_schedule_single
      (lowOwnerStokesSecondPrime_schedule_eq_single_top hR)


theorem lowOwnerStokesTopPrime_prime
    {R : ℕ} (hR : 56 ≤ R) :
    (lowOwnerStokesTopPrime R hR).Prime := by
  exact (mem_primesUpTo.mp (lowOwnerStokesTopPrime_mem hR)).1

/-- The largest physical owner lies in the top reciprocal band. -/
theorem squareRootEndpoint_half_lt_lowOwnerStokesTopPrime
    {R : ℕ} (hR : 56 ≤ R) :
    squareRootEndpoint R / 2 < lowOwnerStokesTopPrime R hR := by
  have hX : 3 ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsq : 4 ≤ R ^ 2 := by nlinarith
    omega
  have hhalf : squareRootEndpoint R / 2 ≠ 0 := by omega
  obtain ⟨q, hqPrime, hqLow, hqHigh⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (squareRootEndpoint R / 2) hhalf
  have hqX : q ≤ squareRootEndpoint R := by omega
  have hqMem : q ∈ primesUpTo (squareRootEndpoint R) :=
    mem_primesUpTo.mpr ⟨hqPrime, hqX⟩
  have hqTop :
      q ≤ lowOwnerStokesTopPrime R hR :=
    Finset.le_max' _ q hqMem
  omega

/-- The actual top owner has no remaining larger prime coordinate. -/
theorem lowOwnerStokesTopPrime_schedule_eq_nil
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerFirstOwnerCanonicalStokesSchedule
        R (lowOwnerStokesTopPrime R hR) = [] := by
  unfold lowOwnerFirstOwnerCanonicalStokesSchedule
  apply List.filter_eq_nil_iff.2
  intro q hq
  have hqMem : q ∈ primesUpTo (squareRootEndpoint R) := by
    unfold squareRootCanonicalRoughDescendingPrimeSchedule at hq
    exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).1 hq
  have hqLe :
      q ≤ lowOwnerStokesTopPrime R hR :=
    Finset.le_max' _ q hqMem
  simpa only [decide_eq_true_eq] using (Nat.not_lt_of_ge hqLe)

/-- A top-owner admitted cofactor is forced to one. -/
theorem lowOwnerStokesTopPrime_admittedBase_eq_one
    {R : ℕ} (hR : 56 ≤ R) {sig : Finset ℕ} {a : ℕ}
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber
      R (lowOwnerStokesTopPrime R hR) sig) :
    a = 1 := by
  rcases Finset.mem_filter.mp ha with ⟨haBase, hpaX⟩
  have haCar := (Finset.mem_filter.mp haBase).1
  have haPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar).2
  have htop :=
    squareRootEndpoint_half_lt_lowOwnerStokesTopPrime hR
  have hXlt :
      squareRootEndpoint R <
        2 * lowOwnerStokesTopPrime R hR := by
    omega
  by_contra hne
  have ha2 : 2 ≤ a := by omega
  have hmul :
      2 * lowOwnerStokesTopPrime R hR ≤
        lowOwnerStokesTopPrime R hR * a := by
    simpa [Nat.mul_comm] using
      Nat.mul_le_mul_right (lowOwnerStokesTopPrime R hR) ha2
  omega


/-- At the maximal owner, the empty lower-signature base cell contains only the
unit site. -/
theorem lowOwnerStokesTopPrime_emptyBase_eq_one
    {R : ℕ} (hR : 56 ≤ R) {a : ℕ}
    (ha : a ∈ lowOwnerFirstOwnerBaseFiber
      R (lowOwnerStokesTopPrime R hR) ∅) :
    a = 1 := by
  rcases Finset.mem_filter.mp ha with ⟨haCar, hdata⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar with
    ⟨_haSq, haPos⟩
  by_contra hane
  obtain ⟨q, hqPrime, hqDvd⟩ :=
    Nat.exists_prime_and_dvd (by omega : a ≠ 1)
  have haIcc := (Finset.mem_filter.mp haCar).1
  have haX := (Finset.mem_Icc.mp haIcc).2
  have hqLeA : q ≤ a := Nat.le_of_dvd haPos hqDvd
  have hqX : q ≤ squareRootEndpoint R := hqLeA.trans haX
  have hqMem : q ∈ primesUpTo (squareRootEndpoint R) :=
    mem_primesUpTo.mpr ⟨hqPrime, hqX⟩
  have hqTop :
      q ≤ lowOwnerStokesTopPrime R hR :=
    Finset.le_max' _ q hqMem
  have hqNeTop : q ≠ lowOwnerStokesTopPrime R hR := by
    intro heq
    subst q
    exact hdata.2 hqDvd
  have hqLtTop : q < lowOwnerStokesTopPrime R hR := by omega
  have hqFace : q ∈ squarefreePrimeFace a := by
    unfold squarefreePrimeFace
    exact Nat.mem_primeFactors.mpr ⟨hqPrime, hqDvd, Nat.ne_of_gt haPos⟩
  have hqSig :
      q ∈ squarefreeLowerPrimeSignature
        (lowOwnerStokesTopPrime R hR) a :=
    Finset.mem_filter.mpr ⟨hqFace, hqLtTop⟩
  rw [hdata.1] at hqSig
  simp at hqSig

theorem lowOwnerStokesTopPrime_emptyBaseAmplitude_nonneg
    {R : ℕ} (hR : 56 ≤ R) :
    0 ≤ lowOwnerFirstOwnerBaseAmplitude
      R (lowOwnerStokesTopPrime R hR) ∅ := by
  unfold lowOwnerFirstOwnerBaseAmplitude
  apply Finset.sum_nonneg
  intro a ha
  have ha1 := lowOwnerStokesTopPrime_emptyBase_eq_one hR ha
  subst a
  unfold lowOwnerZeroFrequencyMobiusSite
  have hw := lowOwnerZeroFrequencyMobiusWeight_nonneg R 1
  norm_num [RHLean.Analysis.realMoebiusStep] at hw ⊢
  exact hw

theorem lowOwnerStokesTopPrime_emptyReturnedAmplitude_nonneg
    {R : ℕ} (hR : 56 ≤ R) :
    0 ≤ lowOwnerFirstOwnerReturnedChildParentAmplitude
      R (lowOwnerStokesTopPrime R hR) ∅ := by
  unfold lowOwnerFirstOwnerReturnedChildParentAmplitude
  apply Finset.sum_nonneg
  intro a ha
  have ha1 := lowOwnerStokesTopPrime_admittedBase_eq_one hR ha
  subst a
  have hw :=
    lowOwnerZeroFrequencyMobiusWeight_nonneg
      R (lowOwnerStokesTopPrime R hR)
  norm_num [RHLean.Analysis.realMoebiusStep] at hw ⊢
  exact hw

theorem lowOwnerStokesTopPrime_returnedAmplitude_eq_zero_of_signature_ne_empty
    {R : ℕ} (hR : 56 ≤ R) {sig : Finset ℕ}
    (hsig : sig ≠ ∅) :
    lowOwnerFirstOwnerReturnedChildParentAmplitude
      R (lowOwnerStokesTopPrime R hR) sig = 0 := by
  unfold lowOwnerFirstOwnerReturnedChildParentAmplitude
  apply Finset.sum_eq_zero
  intro a ha
  have ha1 := lowOwnerStokesTopPrime_admittedBase_eq_one hR ha
  subst a
  have hbase := (Finset.mem_filter.mp ha).1
  have hsigOne := (Finset.mem_filter.mp hbase).2.1
  have hone :
      squarefreeLowerPrimeSignature
        (lowOwnerStokesTopPrime R hR) 1 = ∅ := by
    simp [squarefreeLowerPrimeSignature, squarefreePrimeFace]
  rw [hone] at hsigOne
  exact (hsig hsigOne.symm).elim

/-- The maximal-owner empty-schedule terminal is favorable. It contributes
no positive boundary budget: all nonempty signatures have zero returned
amplitude, while the empty signature has two nonnegative amplitudes multiplied
by the exact coefficient -2. -/
theorem sum_lowOwnerStokesTopPrimeTerminal_nonpos
    {R : ℕ} (hR : 56 ≤ R) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet
        R (lowOwnerStokesTopPrime R hR),
      lowOwnerFirstOwnerCanonicalStokesTopTerminalBoundary
        R (lowOwnerStokesTopPrime R hR) sig) ≤ 0 := by
  have hp := lowOwnerStokesTopPrime_prime hR
  have hsched := lowOwnerStokesTopPrime_schedule_eq_nil hR
  rw [sum_lowOwnerFirstOwnerTopTerminal_eq_neg_two_base_mul_returned_of_schedule_nil
    hp hsched]
  apply Finset.sum_nonpos
  intro sig _hsigMem
  by_cases hsig : sig = ∅
  · subst sig
    have hB := lowOwnerStokesTopPrime_emptyBaseAmplitude_nonneg hR
    have hJ := lowOwnerStokesTopPrime_emptyReturnedAmplitude_nonneg hR
    nlinarith
  · rw [lowOwnerStokesTopPrime_returnedAmplitude_eq_zero_of_signature_ne_empty
      hR hsig]
    norm_num

/-- **Exceptional terminal support is literally the top two first-owner
coordinates.**  Any lower prime has both the top and second-top primes in its
remaining Stokes schedule, contradicting the terminal length bound. -/
theorem lowOwnerStokesTopTerminalOwnerSet_subset_top_two
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesTopTerminalOwnerSet R ⊆
      ({lowOwnerStokesTopPrime R hR,
        lowOwnerStokesSecondPrime R hR} : Finset ℕ) := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpS, hlen⟩
  let t := lowOwnerStokesTopPrime R hR
  let s := lowOwnerStokesSecondPrime R hR
  by_cases hpt : p = t
  · simp [hpt]
  by_cases hps : p = s
  · simp [hps]
  exfalso
  have htS : t ∈ primesUpTo (squareRootEndpoint R) := by
    simpa [t] using lowOwnerStokesTopPrime_mem hR
  have hsErase :
      s ∈ (primesUpTo (squareRootEndpoint R)).erase t := by
    simpa [s, t] using lowOwnerStokesSecondPrime_mem_erase hR
  have hsS : s ∈ primesUpTo (squareRootEndpoint R) :=
    (Finset.mem_erase.mp hsErase).2
  have hst : s ≠ t := (Finset.mem_erase.mp hsErase).1
  have hptLe : p ≤ t := by
    simpa [t] using Finset.le_max'
      (primesUpTo (squareRootEndpoint R)) p hpS
  have hptLt : p < t := by omega
  have hpErase :
      p ∈ (primesUpTo (squareRootEndpoint R)).erase t :=
    Finset.mem_erase.mpr ⟨hpt, hpS⟩
  have hpsLe : p ≤ s := by
    simpa [s, t] using Finset.le_max'
      ((primesUpTo (squareRootEndpoint R)).erase t) p hpErase
  have hpsLt : p < s := by omega
  have htFull :
      t ∈ squareRootCanonicalRoughDescendingPrimeSchedule R := by
    unfold squareRootCanonicalRoughDescendingPrimeSchedule
    exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).2 htS
  have hsFull :
      s ∈ squareRootCanonicalRoughDescendingPrimeSchedule R := by
    unfold squareRootCanonicalRoughDescendingPrimeSchedule
    exact (Finset.mem_sort (fun a b : ℕ => a ≥ b)).2 hsS
  have htSched :
      t ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p := by
    simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using
      (show t ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ p < t
        from ⟨htFull, hptLt⟩)
  have hsSched :
      s ∈ lowOwnerFirstOwnerCanonicalStokesSchedule R p := by
    simpa [lowOwnerFirstOwnerCanonicalStokesSchedule] using
      (show s ∈ squareRootCanonicalRoughDescendingPrimeSchedule R ∧ p < s
        from ⟨hsFull, hpsLt⟩)
  generalize hsched :
      lowOwnerFirstOwnerCanonicalStokesSchedule R p = ps at hlen htSched hsSched
  cases ps with
  | nil =>
      simp at htSched
  | cons a tail =>
      cases tail with
      | nil =>
          simp only [List.mem_singleton] at htSched hsSched
          exact hst (hsSched.trans htSched.symm)
      | cons b rest =>
          simp at hlen

theorem card_lowOwnerStokesTopTerminalOwnerSet_le_two
    {R : ℕ} (hR : 56 ≤ R) :
    (lowOwnerStokesTopTerminalOwnerSet R).card ≤ 2 := by
  have hsub := lowOwnerStokesTopTerminalOwnerSet_subset_top_two hR
  calc
    (lowOwnerStokesTopTerminalOwnerSet R).card ≤
        ({lowOwnerStokesTopPrime R hR,
          lowOwnerStokesSecondPrime R hR} : Finset ℕ).card :=
      Finset.card_le_card hsub
    _ ≤ 2 := by
      have h := Finset.card_insert_le
        (lowOwnerStokesTopPrime R hR)
        ({lowOwnerStokesSecondPrime R hR} : Finset ℕ)
      simpa using h

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

/-- Direct root-scale form of the clip estimate.  Because the natural frame
has a fixed prime-3 diagonal, this apparently weaker target is already
sufficient for prime-period frame domination. -/
def LowOwnerStokesClipRootBound (A : ℝ) : Prop :=
  ∀ (R : ℕ) (_hR : 56 ≤ R),
    lowOwnerCanonicalSignedStokesClipBoundary R ≤
      A * (R : ℝ) ^ 2

/-- Any nonnegative root-scale clip bound feeds the exact #758 frame target.
The explicit factor 18 comes only from the deterministic prime-3 frame
diagonal; no off-diagonal alignment is used. -/
theorem clipPrimePeriodFrameDomination_of_rootBound
    {A : ℝ} (hA : 0 ≤ A)
    (hClip : LowOwnerStokesClipRootBound A) :
    LowOwnerStokesClipPrimePeriodFrameDomination (18 * A) := by
  intro R hR
  have hframe :=
    root_sq_over_eighteen_le_lowOwnerStokesOddPrimePeriodFrameMajorant hR
  have hscaled :
      A * ((R : ℝ) ^ 2 / 18) ≤
        A * lowOwnerStokesOddPrimePeriodFrameMajorant R hR :=
    mul_le_mul_of_nonneg_left hframe hA
  calc
    lowOwnerCanonicalSignedStokesClipBoundary R ≤
        A * (R : ℝ) ^ 2 := hClip R hR
    _ = 18 * (A * ((R : ℝ) ^ 2 / 18)) := by ring
    _ ≤ 18 *
        (A * lowOwnerStokesOddPrimePeriodFrameMajorant R hR) :=
      mul_le_mul_of_nonneg_left hscaled (by norm_num)
    _ = (18 * A) *
        lowOwnerStokesOddPrimePeriodFrameMajorant R hR := by ring


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

end RHLean.Proof
