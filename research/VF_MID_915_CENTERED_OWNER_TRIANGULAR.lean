import Mathlib
import «research.VF_MID_FIRST_BAD_NORMALIZED_PARTIAL_MOMENT»
import «research.VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI»
import «research.VF_MID_FIRST_BAD_HISTORY_COMPRESSION»

/-!
# #915: original-source centered first-prime-owner triangular covariance

This module AVOIDS historical norm decompression. For every original
parity-surviving VF integer site n, define a *predictably centered*
least-prime-owner removal:

  xi_p(n) = S_(p-1)(n) * (1_{p|n} - 1/p),

where S_(p-1) is the genuine survivor indicator of ALL earlier primes.
No equidistribution assumption, PNT replacement, imaginary prime parent,
or new positive/negative capacity is introduced.

The key structural law, for distinct p<q prime, holds POINTWISE:

  xi_p(n) * xi_q(n) = - xi_q(n)/p.

The earlier p has ALREADY removed every p-divisible integer that can enter
the later q-carrier. Therefore the *entire off-diagonal quadratic cross-
owner Gram* becomes a degree-one signed boundary discrepancy of the later
actual owner. This is not a statistical anticorrelation claim:
the sign of the sum of xi_q over a particular square band is unknown.

The per-site exact sieve recurrence telescopes as a finite affine sequence,
so original VF charge, original source, and original squared absolute NNS
denominator are rebuilt using the centered owner field WITHOUT expanding
the earlier signed anchor. Numerical regressions inspect the diagonal
and triangular cross-owner terms independently.

No RH-strength sign estimate, first-bad payment, or use of the unproved
#915 production theorem is made by these identities.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis
open RHLean.Arithmetic RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- Literal earlier-survivor conditional prime removal, centered by 1/p.
Works at ALL integer sites (prime or composite); no probabilistic model. -/
def vfMid915CenteredOwnerDeviation (p n : ℕ) : ℝ :=
  if lowWheelHighSurvivor (p - 1) n then
    (if p ∣ n then (1 : ℝ) else 0) - 1 / (p : ℝ)
  else 0

/-- A genuine integer low-wheel state as a zero-one real field. -/
def vfMid915PrefixState (p n : ℕ) : ℝ :=
  if lowWheelHighSurvivor p n then 1 else 0

/-- A prime is the only new divisibility coordinate between p-1 and p.
This is a set statement; NO prime number theorem is needed. -/
theorem vfMid915PrefixSurvivor_prime_iff
    {p n : ℕ} (hp : p.Prime) :
    lowWheelHighSurvivor p n ↔
      lowWheelHighSurvivor (p - 1) n ∧ ¬ p ∣ n := by
  constructor
  · intro hsurv
    constructor
    · intro q hq
      have hqdata := mem_primesUpTo.mp hq
      apply hsurv q
      exact mem_primesUpTo.mpr ⟨hqdata.1, by omega⟩
    · exact hsurv p (mem_primesUpTo.mpr ⟨hp, le_rfl⟩)
  · rintro ⟨hprev, hnpd⟩ q hq
    have hqdata := mem_primesUpTo.mp hq
    by_cases hqp : q = p
    · simpa [hqp] using hnpd
    · apply hprev q
      exact mem_primesUpTo.mpr ⟨hqdata.1, by omega⟩

/-- A nonprime cutoff adds no prime sieve coordinate. -/
theorem vfMid915PrefixSurvivor_composite_iff
    {p n : ℕ} (hnot : ¬ p.Prime) :
    lowWheelHighSurvivor p n ↔ lowWheelHighSurvivor (p - 1) n := by
  constructor
  · intro hsurv q hq
    have hqdata := mem_primesUpTo.mp hq
    exact hsurv q (mem_primesUpTo.mpr ⟨hqdata.1, by omega⟩)
  · intro hprev q hq
    have hqdata := mem_primesUpTo.mp hq
    have hneq : q ≠ p := by
      intro heq
      exact hnot (heq ▸ hqdata.1)
    exact hprev q (mem_primesUpTo.mpr
      ⟨hqdata.1, by omega⟩)

/-- Add a new prime coordinate with EXACT native 1/p centering. -/
def vfMid915OwnerStepFactor (p : ℕ) : ℝ :=
  if p.Prime then 1 - 1 / (p : ℝ) else 1

def vfMid915OwnerStepShock (p n : ℕ) : ℝ :=
  if p.Prime then vfMid915CenteredOwnerDeviation p n else 0

/-- The only needed sieve recurrence: actual surviving state at p is
t_p times the earlier surviving state, minus the centered owner shock. -/
theorem vfMid915PrefixState_eq_factor_sub_shock
    {p n : ℕ} :
    vfMid915PrefixState p n =
      vfMid915OwnerStepFactor p * vfMid915PrefixState (p - 1) n -
        vfMid915OwnerStepShock p n := by
  by_cases hp : p.Prime
  · have hiff := vfMid915PrefixSurvivor_prime_iff (n := n) hp
    by_cases hs : lowWheelHighSurvivor (p - 1) n
    · by_cases hdiv : p ∣ n
      · have hnot : ¬ lowWheelHighSurvivor p n := by
          intro h
          exact (hiff.mp h).2 hdiv
        simp [vfMid915PrefixState, vfMid915OwnerStepFactor,
          vfMid915OwnerStepShock, vfMid915CenteredOwnerDeviation,
          hp, hs, hdiv, hnot]
      · have hsurv : lowWheelHighSurvivor p n :=
          hiff.mpr ⟨hs, hdiv⟩
        simp [vfMid915PrefixState, vfMid915OwnerStepFactor,
          vfMid915OwnerStepShock, vfMid915CenteredOwnerDeviation,
          hp, hs, hdiv, hsurv]
    · have hnot : ¬ lowWheelHighSurvivor p n := by
        intro h
        exact hs (hiff.mp h).1
      simp [vfMid915PrefixState, vfMid915OwnerStepFactor,
        vfMid915OwnerStepShock, vfMid915CenteredOwnerDeviation,
        hp, hs, hnot]
  · have hiff := vfMid915PrefixSurvivor_composite_iff (n := n) hp
    simp [vfMid915PrefixState, vfMid915OwnerStepFactor,
      vfMid915OwnerStepShock, hp, hiff]

/-- A survivor past q necessarily survived p and is not divisible by p. -/
theorem vfMid915LaterOwner_survivor_excludes_earlier
    {p q n : ℕ} (hp : p.Prime) (hpq : p < q)
    (hs : lowWheelHighSurvivor (q - 1) n) :
    lowWheelHighSurvivor (p - 1) n ∧ ¬ p ∣ n := by
  constructor
  · intro k hk
    have hkd := mem_primesUpTo.mp hk
    apply hs k (mem_primesUpTo.mpr ⟨hkd.1, by omega⟩)
  · exact hs p (mem_primesUpTo.mpr ⟨hp, by omega⟩)

/-- **Key arithmetic triangularization**: cross-owner covariance is
NOT a new quadratic random interaction. At every integer site the earlier
owner shock is exactly -1/p on the later owner's surviving support. -/
theorem vfMid915CenteredOwner_pair_eq_late
    {p q n : ℕ} (hp : p.Prime) (hpq : p < q) :
    vfMid915CenteredOwnerDeviation p n *
        vfMid915CenteredOwnerDeviation q n =
      -(1 / (p : ℝ)) * vfMid915CenteredOwnerDeviation q n := by
  by_cases hs : lowWheelHighSurvivor (q - 1) n
  · obtain ⟨hsp, hnot⟩ :=
      vfMid915LaterOwner_survivor_excludes_earlier hp hpq hs
    simp [vfMid915CenteredOwnerDeviation, hs, hsp, hnot]
  · simp [vfMid915CenteredOwnerDeviation, hs]

/-- The SAME triangular law on the ORIGINAL R-th odd VF carrier.
No source/denominator expansion, no Li replacement. -/
theorem vfMid915CenteredOwner_originalOddGram_eq_late
    (R p q : ℕ) (hp : p.Prime) (hpq : p < q) :
    (∑ n ∈ vfMidOddCandidateSeats R,
      vfMid915CenteredOwnerDeviation p n *
        vfMid915CenteredOwnerDeviation q n) =
      -(1 / (p : ℝ)) *
        ∑ n ∈ vfMidOddCandidateSeats R,
          vfMid915CenteredOwnerDeviation q n := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  exact vfMid915CenteredOwner_pair_eq_late hp hpq

/-- The actual earlier-survivor population is the only diagonal input.
All squared Boolean owner shocks are affine in xi_p and survivor mass. -/
theorem vfMid915CenteredOwner_deviation_sq
    (p n : ℕ) :
    vfMid915CenteredOwnerDeviation p n ^ 2 =
      (1 - 2 / (p : ℝ)) * vfMid915CenteredOwnerDeviation p n +
      (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) *
        vfMid915PrefixState (p - 1) n := by
  by_cases hs : lowWheelHighSurvivor (p - 1) n <;>
    by_cases hd : p ∣ n <;>
    simp [vfMid915CenteredOwnerDeviation, vfMid915PrefixState,
      hs, hd] <;> ring

theorem vfMid915CenteredOwner_originalOddDiagonal_eq_population
    (R p : ℕ) :
    (∑ n ∈ vfMidOddCandidateSeats R,
      vfMid915CenteredOwnerDeviation p n ^ 2) =
      (1 - 2 / (p : ℝ)) *
        (∑ n ∈ vfMidOddCandidateSeats R,
          vfMid915CenteredOwnerDeviation p n) +
      (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) *
        (∑ n ∈ vfMidOddCandidateSeats R,
          vfMid915PrefixState (p - 1) n) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  exact vfMid915CenteredOwner_deviation_sq p n

/-! ## No-decompression original-source reconstruction -/

/-- Products of actual 1-1/p factors, computed in the genuine chronology
p=3,4,...,R. Non-prime stages contribute factor 1. -/
def vfMid915CenteredAlpha : ℕ → ℝ
  | 0 => 1
  | k + 1 =>
    vfMid915OwnerStepFactor (k + 3) * vfMid915CenteredAlpha k

/-- The exactly propagated centered owner-error shock, **not** a new model
of the primes. All q-indices use the original low-prefix survivor. -/
def vfMid915CenteredAccum (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
    vfMid915OwnerStepFactor (k + 3) * vfMid915CenteredAccum n k +
      vfMid915OwnerStepShock (k + 3) n

/-- Deterministic finite native source telescope: the ORIGINAL completed
prime wheel = product of independent reference factors MINUS the exact
conditioned owner covariance correction. -/
theorem vfMid915Centered_prefix_telescopes
    (n : ℕ) (hbase : lowWheelHighSurvivor 2 n) (k : ℕ) :
    vfMid915PrefixState (k + 2) n =
      vfMid915CenteredAlpha k - vfMid915CenteredAccum n k := by
  induction k with
  | zero =>
      simp [vfMid915PrefixState, vfMid915CenteredAlpha,
        vfMid915CenteredAccum, hbase]
  | succ k ih =>
      have hstep :=
        vfMid915PrefixState_eq_factor_sub_shock
          (p := k + 3) (n := n)
      have hind :
          vfMid915PrefixState (k + 2) n =
            vfMid915CenteredAlpha k -
              vfMid915CenteredAccum n k := ih
      change
        vfMid915PrefixState (k + 3) n =
          vfMid915CenteredAlpha (k + 1) -
            vfMid915CenteredAccum n (k + 1)
      rw [hstep, show k + 3 - 1 = k + 2 by omega, hind]
      simp only [vfMid915CenteredAlpha, vfMid915CenteredAccum]
      ring

/-- **Main original-source weld**: pointwise actual VF-minus-prime charge
equals its exact prime-independent center + the entire correctly-centered
chronological least-prime owner shock. No new historical abs norm. -/
theorem vfMid915ActualOddSignedSeat_eq_centeredOwner
    {R n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ vfMidOddCandidateSeats R) :
    vfMidOddSignedSeatCharge R n =
      vfMidOddFractionalPrimeSeatWeight R -
        vfMid915CenteredAlpha (R - 2) +
        vfMid915CenteredAccum n (R - 2) := by
  have hodd : n ∈ vfMidSquarePrefixWheelSurvivors 2 R := hn
  have hfilter := Finset.mem_filter.mp hodd
  have hbase : lowWheelHighSurvivor 2 n := hfilter.2
  have hprime :=
    vfMidSquareBand_commonWheelSurvivor_iff_prime hR hfilter.1
  have hstate :
      vfMid915PrefixState R n = vfMidActualPrimeSeatMass n := by
    simp [vfMid915PrefixState, vfMidActualPrimeSeatMass, hprime]
  have htel := vfMid915Centered_prefix_telescopes n hbase (R - 2)
  have hRidx : R - 2 + 2 = R := by omega
  rw [hRidx, hstate] at htel
  unfold vfMidOddSignedSeatCharge
  rw [htel]
  ring

/-- Degree-one source is now an EXACT centered-owner ledger on the actual
odd sites. In particular its historical anchor D_R is NOT decompressed. -/
theorem vfMid915ActualOddSignedSource_eq_centeredOwner
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ n ∈ vfMidOddCandidateSeats R,
      vfMidOddSignedSeatCharge R n) =
      (R : ℝ) *
        (vfMidOddFractionalPrimeSeatWeight R -
          vfMid915CenteredAlpha (R - 2)) +
      (∑ n ∈ vfMidOddCandidateSeats R,
        vfMid915CenteredAccum n (R - 2)) := by
  calc
    (∑ n ∈ vfMidOddCandidateSeats R,
      vfMidOddSignedSeatCharge R n) =
    ∑ n ∈ vfMidOddCandidateSeats R,
      (vfMidOddFractionalPrimeSeatWeight R -
        vfMid915CenteredAlpha (R - 2) +
        vfMid915CenteredAccum n (R - 2)) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact vfMid915ActualOddSignedSeat_eq_centeredOwner hR hn
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const]
      rw [vfMidOddCandidateSeats_card]
      simp only [nsmul_eq_mul]

/-- Exact CENTERED actual-prime owner identity on the FULL historical VF
defect. The signed historical anchor is retained as one scalar, with
no history norm expansion and no optional guessed sign cancellation.
This is the exact arithmetic target needed for multiscale first badness. -/
theorem vfMid915ActualHistoricalDefect_eq_centeredOwner
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    vfMidActualPrimeEndpointDefect B =
      vfMidActualPrimeEndpointDefect A -
        (∑ r ∈ Finset.Ico A B,
          ((r : ℝ) *
            (vfMidOddFractionalPrimeSeatWeight r -
              vfMid915CenteredAlpha (r - 2)) +
            ∑ n ∈ vfMidOddCandidateSeats r,
              vfMid915CenteredAccum n (r - 2))) := by
  have hhistory :=
    vfMidActualPrimeEndpointDefect_eq_anchor_sub_oddRunSeatMass hA hAB
  rw [vfMidOddRunSeatMass_eq_sum_physicalSeats] at hhistory
  have hsum :
      (∑ r ∈ Finset.Ico A B,
          ∑ n ∈ vfMidOddCandidateSeats r,
            vfMidOddSignedSeatCharge r n) =
      ∑ r ∈ Finset.Ico A B,
        ((r : ℝ) *
            (vfMidOddFractionalPrimeSeatWeight r -
              vfMid915CenteredAlpha (r - 2)) +
          ∑ n ∈ vfMidOddCandidateSeats r,
            vfMid915CenteredAccum n (r - 2)) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact vfMid915ActualOddSignedSource_eq_centeredOwner
      r (hA.trans (Finset.mem_Ico.mp hr).1)
  rw [hsum] at hhistory
  exact hhistory

/-- #915 canonical half-scale historical source, rewritten solely in the
exact actual centered low-owner shocks and the ORIGINAL half-run anchor.
PNT or Fourier bounds may act on this signed sum only after respecting
its survivor conditioning; no earlier abs denominator is reintroduced. -/
theorem vfMid915ActualHalfScaleDefect_eq_centeredOwner
    (R : ℕ) (hR : 8 ≤ R) :
    vfMidActualPrimeEndpointDefect (R + 1) =
      vfMidActualPrimeEndpointDefect (R / 2 + 1) -
        (∑ r ∈ Finset.Ico (R / 2 + 1) (R + 1),
          ((r : ℝ) *
            (vfMidOddFractionalPrimeSeatWeight r -
              vfMid915CenteredAlpha (r - 2)) +
            ∑ n ∈ vfMidOddCandidateSeats r,
              vfMid915CenteredAccum n (r - 2))) := by
  exact vfMid915ActualHistoricalDefect_eq_centeredOwner
    (by omega : 2 ≤ R / 2 + 1)
    (by omega : R / 2 + 1 ≤ R + 1)

/-- Exact original zero-target absolute denominator: no old individual
historical occurrence is reintroduced after compression to D_R. -/
theorem vfMid915OriginalFirstBadDenominator_eq_centeredOwner
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidFirstBadZeroTargetTotalMass R =
      (|vfMidActualPrimeEndpointDefect R| +
        ∑ n ∈ vfMidOddCandidateSeats R,
          |vfMidOddFractionalPrimeSeatWeight R -
              vfMid915CenteredAlpha (R - 2) +
                vfMid915CenteredAccum n (R - 2)|) ^ 2 := by
  rw [vfMidFirstBadZeroTargetTotalMass_eq]
  have hsum :
      (∑ n ∈ vfMidOddCandidateSeats R,
        |vfMidOddSignedSeatCharge R n|) =
      ∑ n ∈ vfMidOddCandidateSeats R,
        |vfMidOddFractionalPrimeSeatWeight R -
          vfMid915CenteredAlpha (R - 2) +
            vfMid915CenteredAccum n (R - 2)| := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [vfMid915ActualOddSignedSeat_eq_centeredOwner hR hn]
  rw [hsum]

end RHLean.Analysis
