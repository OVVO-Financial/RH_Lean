import Mathlib
import «research.VF_MID_SEVEN_EIGHTHS_ANALYTIC_BRIDGE»

/-!
# A genuine arithmetic-analytic synthesis: owner-column Abel transport

The first 7/8 bridge only controlled the aggregate pi-VF defect.
Here we re-enter the *original* weighted high-owner prime-pair
incidence: p<q, pq in a square run, with reference weight
VF_mid bandMass(sqrt(p*q))/sqrt(p*q).

For each FIXED owner p, the weighted prime-q source is
an exact discrete Abel transform of the genuine pi-Li error
at the LOWER-SCALE partner coordinate q. This is a signed
endpoint-plus-variation identity, not a blanket assumption
about RH or artificial prime seats. It is the exact analytic
entry point to the existing rank-two cofactor/owner graph.

No claim is made that separate p-column bounds establish the
joint original Co/Div Sector Six or an RH-strength estimate.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- Exact signed Abel transform of any finite difference sequence.
The entire run collapses to two endpoints plus signed weight variation.
This is NOT a per-site absolute-value estimate. -/
theorem vfSevenEighthsWeightedIncrementAbel
    (E w : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ r ∈ Finset.Ico a b,
      w (r + 1) * (E (r + 1) - E r)) =
    w b * E b - w a * E a +
      ∑ r ∈ Finset.Ico a b,
        (w r - w (r + 1)) * E r := by
  induction b, hab using Nat.le_induction with
  | base =>
      simp
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab,
          Finset.sum_Ico_succ_top hab, ih]
      ring

/-- A discrete telescoping identity for the weight variation.
It is the reason the 7/8 error DOES NOT accumulate once
per individual q-site inside each fixed owner's column. -/
theorem vfSevenEighthsWeightVariation_telescope
    (w : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ r ∈ Finset.Ico a b, (w r - w (r + 1))) =
      w a - w b := by
  induction b, hab using Nat.le_induction with
  | base =>
      simp
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab, ih]
      ring

/-- The exact ROOT-WEIGHT of one genuine high-owner semiprime site
n=p*q, where p and q are distinct primes, p<q. It is the
original physical odd candidate's w_R; NO extra physical sites
or newly allocated negative prime-owner charges. -/
def vfSevenEighthsPhysicalOwnerWeight (p q : ℕ) : ℝ :=
  let R := Nat.sqrt (p * q)
  vfMidBandMass R / (R : ℝ)

/-- The real, genuine-prime staircase error at a natural cutoff.
No fantasy surrogate. -/
def vfSevenEighthsPrimeLiErrorAtNat (n : ℕ) : ℝ :=
  (Nat.primeCounting n : ℝ) -
    vfMidLogarithmicIntegralFromTwo (n : ℝ)

theorem vfSevenEighthsPrimeLiErrorAtNat_eq (n : ℕ) :
    vfSevenEighthsPrimeLiErrorAtNat n =
      vfMidPrimeLiError (n : ℝ) := by
  simp [vfSevenEighthsPrimeLiErrorAtNat, vfMidPrimeLiError,
    vfMidPrimeCount]

/-- Original weighted (prime - Li) increment on a p-column.
If q is prime, pi(q)-pi(q-1)=1; otherwise it is 0.
The multiplier is ALWAYS the true square-band VF physical
weight at p*q, including its root quantization. -/
def vfSevenEighthsWeightedOwnerPrimeLiDifference
    (p upper : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico p upper,
    vfSevenEighthsPhysicalOwnerWeight p (r + 1) *
      (((Nat.primeCounting (r + 1) : ℝ) -
        (Nat.primeCounting r : ℝ)) -
       (vfMidLogarithmicIntegralFromTwo ((r + 1 : ℕ) : ℝ) -
        vfMidLogarithmicIntegralFromTwo (r : ℝ)))

/-- Exact Abel synthesis of true prime-pair owner cells with
analytic pi-Li spectral errors at LOWER cofactor arguments.
All p*q weights and signed errors remain attached.
No absolute value is taken before the Fubini/Abel reassembly. -/
theorem vfSevenEighthsWeightedOwnerPrimeLiDifference_eq_abel
    (p upper : ℕ) (hp : p ≤ upper) :
    vfSevenEighthsWeightedOwnerPrimeLiDifference p upper =
      vfSevenEighthsPhysicalOwnerWeight p upper *
        vfSevenEighthsPrimeLiErrorAtNat upper -
      vfSevenEighthsPhysicalOwnerWeight p p *
        vfSevenEighthsPrimeLiErrorAtNat p +
      ∑ r ∈ Finset.Ico p upper,
        (vfSevenEighthsPhysicalOwnerWeight p r -
          vfSevenEighthsPhysicalOwnerWeight p (r + 1)) *
        vfSevenEighthsPrimeLiErrorAtNat r := by
  unfold vfSevenEighthsWeightedOwnerPrimeLiDifference
  calc
    (∑ r ∈ Finset.Ico p upper,
      vfSevenEighthsPhysicalOwnerWeight p (r + 1) *
        (((Nat.primeCounting (r + 1) : ℝ) -
            (Nat.primeCounting r : ℝ)) -
          (vfMidLogarithmicIntegralFromTwo ((r + 1 : ℕ) : ℝ) -
            vfMidLogarithmicIntegralFromTwo (r : ℝ)))) =
      ∑ r ∈ Finset.Ico p upper,
        vfSevenEighthsPhysicalOwnerWeight p (r + 1) *
          (vfSevenEighthsPrimeLiErrorAtNat (r + 1) -
            vfSevenEighthsPrimeLiErrorAtNat r) := by
          apply Finset.sum_congr rfl
          intro r _
          unfold vfSevenEighthsPrimeLiErrorAtNat
          ring
    _ = _ := vfSevenEighthsWeightedIncrementAbel
      vfSevenEighthsPrimeLiErrorAtNat
      (vfSevenEighthsPhysicalOwnerWeight p)
      p upper hp

/-- Each genuine p-column can have a different prime-pair upper
bound. This is the exact finite column-wise sum of signed
historical-cumulative endpoint and variation terms, preserving
all original root weights, with NO repeated historical owner payment.
A later bound on this sum must respect cross-p-column covariance. -/
theorem vfSevenEighthsOwnerPacket_abel
    (owners : Finset ℕ) (upper : ℕ → ℕ)
    (hupper : ∀ p ∈ owners, p ≤ upper p) :
    (∑ p ∈ owners,
      vfSevenEighthsWeightedOwnerPrimeLiDifference p (upper p)) =
    ∑ p ∈ owners,
      (vfSevenEighthsPhysicalOwnerWeight p (upper p) *
        vfSevenEighthsPrimeLiErrorAtNat (upper p) -
       vfSevenEighthsPhysicalOwnerWeight p p *
        vfSevenEighthsPrimeLiErrorAtNat p +
       ∑ r ∈ Finset.Ico p (upper p),
         (vfSevenEighthsPhysicalOwnerWeight p r -
           vfSevenEighthsPhysicalOwnerWeight p (r + 1)) *
          vfSevenEighthsPrimeLiErrorAtNat r) := by
  apply Finset.sum_congr rfl
  intro p hp
  exact vfSevenEighthsWeightedOwnerPrimeLiDifference_eq_abel
    p (upper p) (hupper p hp)

end RHLean.Analysis
