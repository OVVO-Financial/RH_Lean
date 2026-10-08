import Mathlib
import RHLean.Proof.PrimeCombReciprocalBandCancellation
import «research.VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI»

/-!
# #915: inherited Möbius dyadic pairing with literal VF physical weights

PROOF AUDIT: this module starts from the ALREADY-COMPILED lower-prefix and
dyadic replication identities and tests their transport into the #915
original parity-reduced square-block physical source.

The native integer law mu(2*c) = -mu(c) for odd c produces cancellation
ONLY if both actual physical cofactor occurrences survive the relevant
clock and their *literal* weights agree. The exact formula retains:
  (i) the shared-prime-count dyadic overlap weight mismatch, and
  (ii) the exclusive outer shell of the c branch.

No inferred prime-density error, artificial negative stripped parent, or
new RH distribution hypothesis is used here.

The critical square-band finding is a NO-GO for direct one-block dyadic
payment: the physical VF field has only odd seats and, on the unfinished
square interval, doubling an active seat necessarily exits the block.
Therefore the overlap term in the current physical source is exactly zero.
The surviving dyadic packet is the outer shell, requiring *genuine
historical* interaction to become a Co/Div payment.

This file does NOT prove #915 hbalance.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- Actual prime owner q>R within the full square-prefix clock, contributing
the ORIGINAL real signed site weight at c*q. No replacement by Li or Mertens
density occurs. -/
def vfMid915WeightedLatePrimeFiber (R X c : ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc R X,
    if q.Prime ∧ c * q ≤ X then
      (((μ c : ℤ) : ℝ)) * weight (c * q)
    else 0

/-- The physical overlap of an odd cofactor c and its dyadic mate 2*c
across exactly the same ACTUAL prime q. The retained weights can differ. -/
def vfMid915WeightedDyadicOverlap (R X c : ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc R X,
    if q.Prime ∧ (2 * c) * q ≤ X then
      (((μ c : ℤ) : ℝ)) *
        (weight (c * q) - weight ((2 * c) * q))
    else 0

/-- Genuinely unmatched prime-owner shell: c*q fits, (2*c)*q does not. -/
def vfMid915WeightedDyadicOuterShell (R X c : ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc R X,
    if q.Prime ∧ c * q ≤ X ∧ ¬ ((2 * c) * q ≤ X) then
      (((μ c : ℤ) : ℝ)) * weight (c * q)
    else 0

/-- Pointwise exact dyadic Möbius cancellation, with the physical WEIGHT
mismatch explicitly retained, plus the exclusive q cutoff shell. -/
theorem vfMid915WeightedDyadicPrimeAtom_eq_overlap_add_shell
    (c q X : ℕ) (weight : ℕ → ℝ) (hc : Odd c) :
    (if q.Prime ∧ c * q ≤ X then
      (((μ c : ℤ) : ℝ)) * weight (c * q) else 0) +
    (if q.Prime ∧ (2 * c) * q ≤ X then
      (((μ (2 * c) : ℤ) : ℝ)) * weight ((2 * c) * q) else 0) =
    (if q.Prime ∧ (2 * c) * q ≤ X then
      (((μ c : ℤ) : ℝ)) *
        (weight (c * q) - weight ((2 * c) * q)) else 0) +
    (if q.Prime ∧ c * q ≤ X ∧ ¬ ((2 * c) * q ≤ X) then
      (((μ c : ℤ) : ℝ)) * weight (c * q) else 0) := by
  have hmu := RHLean.Arithmetic.moebius_two_mul_of_odd c hc
  rw [hmu]
  by_cases hprime : q.Prime
  · by_cases htwo : (2 * c) * q ≤ X
    · have hone : c * q ≤ X := by
        have hprod : (2 * c) * q = 2 * (c * q) := by ring
        omega
      simp [hprime, htwo, hone]
      ring
    · by_cases hone : c * q ≤ X
      · simp [hprime, htwo, hone]
      · simp [hprime, htwo, hone]
  · simp [hprime]

/-- No hidden uniform VF coefficient is substituted: the exact identity
holds for an arbitrary literal weight attached to EVERY integer site. -/
theorem vfMid915WeightedDyadicPrimeFiber_eq_overlap_add_shell
    (R X c : ℕ) (weight : ℕ → ℝ) (hc : Odd c) :
    vfMid915WeightedLatePrimeFiber R X c weight +
      vfMid915WeightedLatePrimeFiber R X (2 * c) weight =
    vfMid915WeightedDyadicOverlap R X c weight +
      vfMid915WeightedDyadicOuterShell R X c weight := by
  unfold vfMid915WeightedLatePrimeFiber
    vfMid915WeightedDyadicOverlap vfMid915WeightedDyadicOuterShell
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl
    (fun q _ => vfMid915WeightedDyadicPrimeAtom_eq_overlap_add_shell
      c q X weight hc)

/-- The literal parity-reduced VF signed seat weight, extended by zero
off the current OPEN square band. Unlike the Möbius sign, this charges
every odd composite positively (squareful seats included). -/
def vfMid915CurrentOddPhysicalWeight (R n : ℕ) : ℝ :=
  if R ^ 2 < n ∧ n < (R + 1) ^ 2 ∧ Odd n then
    vfMidOddSignedSeatCharge R n
  else 0

/-- On the actual square clock, no active site can have a doubled physical
descendant. This is the same geometric fact compiled in the existing
vfMidOneBlockActivePhysical_two_mul_gt_endpoint, now stated for the whole
odd-seat support including squareful restoring sites. -/
theorem vfMid915CurrentSquare_double_exits
    {R n : ℕ} (hR : 2 ≤ R) (hn : R ^ 2 < n) :
    (R + 1) ^ 2 ≤ 2 * n := by
  have hmul : R * 2 ≤ R * R := Nat.mul_le_mul_left R hR
  nlinarith

theorem vfMid915CurrentOddWeight_zero_of_double_fits
    {R n : ℕ} (hR : 2 ≤ R)
    (hfit : 2 * n < (R + 1) ^ 2) :
    vfMid915CurrentOddPhysicalWeight R n = 0 := by
  have hnot : ¬ R ^ 2 < n := by
    intro hn
    have h := vfMid915CurrentSquare_double_exits hR hn
    omega
  simp [vfMid915CurrentOddPhysicalWeight, hnot]

theorem vfMid915CurrentOddWeight_even_zero (R n : ℕ) :
    vfMid915CurrentOddPhysicalWeight R (2 * n) = 0 := by
  simp [vfMid915CurrentOddPhysicalWeight, Nat.even_two_mul]

/-- Every overlapping dyadic prime owner term is EXACTLY ZERO on the
unchanged one-block parity-reduced VF field. No nonzero --4|z| payment
can be extracted from these overlap terms inside the current band. -/
theorem vfMid915CurrentOddWeight_dyadicOverlap_zero
    (R c : ℕ) (hR : 2 ≤ R) :
    vfMid915WeightedDyadicOverlap R ((R + 1) ^ 2 - 1) c
      (vfMid915CurrentOddPhysicalWeight R) = 0 := by
  unfold vfMid915WeightedDyadicOverlap
  apply Finset.sum_eq_zero
  intro q _hq
  by_cases hfit : q.Prime ∧ (2 * c) * q ≤ (R + 1) ^ 2 - 1
  · have h2 : 2 * (c * q) < (R + 1) ^ 2 := by
      have hprod : (2 * c) * q = 2 * (c * q) := by ring
      omega
    rw [if_pos hfit,
      vfMid915CurrentOddWeight_zero_of_double_fits hR h2,
      show (2 * c) * q = 2 * (c * q) by ring,
      vfMid915CurrentOddWeight_even_zero]
    ring
  · simp [hfit]

/-- Consequence: ALL one-block physical VF dyadic-paired cofactor mass
survives exclusively as a PRIME-OWNER OUTER-SHELL, not an available
local opposite-sign parent. An actual historical match is indispensable. -/
theorem vfMid915CurrentOddWeight_dyadicPair_eq_outerShell
    (R c : ℕ) (hR : 2 ≤ R) (hc : Odd c) :
    vfMid915WeightedLatePrimeFiber R ((R + 1) ^ 2 - 1) c
        (vfMid915CurrentOddPhysicalWeight R) +
      vfMid915WeightedLatePrimeFiber R ((R + 1) ^ 2 - 1) (2 * c)
        (vfMid915CurrentOddPhysicalWeight R) =
    vfMid915WeightedDyadicOuterShell R ((R + 1) ^ 2 - 1) c
      (vfMid915CurrentOddPhysicalWeight R) := by
  rw [vfMid915WeightedDyadicPrimeFiber_eq_overlap_add_shell
    R ((R + 1) ^ 2 - 1) c (vfMid915CurrentOddPhysicalWeight R) hc,
    vfMid915CurrentOddWeight_dyadicOverlap_zero R c hR]
  ring

/-- Genuine **half-scale ancestry bottleneck**. In an unfinished square band,
an odd composite c*q with historical prime q inside [a², (R+1)²), where
a=R/2+1, cannot have cofactor c >= 5. Only c=3 can contribute to
the explicit recent-half-run prime-owner match; c>=5 requires older ancestry
inside the compressed anchor D_a. No primality is assumed for this geometry. -/
theorem vfMid915HalfScaleOddCofactor_eq_three
    {R c q n : ℕ} (hR : 8 ≤ R)
    (hcOdd : Odd c) (hc3 : 3 ≤ c)
    (hq : (R / 2 + 1) ^ 2 ≤ q)
    (hn : n < (R + 1) ^ 2) (hfactor : n = c * q) :
    c = 3 := by
  let a := R / 2 + 1
  have hhalf : R + 1 ≤ 2 * a := by
    dsimp [a]
    omega
  have hsq : (R + 1) ^ 2 ≤ 4 * a ^ 2 := by
    nlinarith
  by_contra hne
  have hc5 : 5 ≤ c := by
    rcases hcOdd with ⟨k, hk⟩
    omega
  have hmul : 5 * a ^ 2 ≤ c * q :=
    Nat.mul_le_mul hc5 (by simpa [a] using hq)
  have ha : 0 < a ^ 2 := by
    dsimp [a]
    positivity
  omega

end RHLean.Analysis
