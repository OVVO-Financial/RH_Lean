import Mathlib
import RHLean.Analysis.LargePrimeTTransport
import RHLean.Analysis.NativePNTSignedSecondSelbergWheelFrontier

/-!
# A source-exact integral prime/cofactor minor at square endpoints

An unconditional finite arithmetic identity on the *actual* integer Mobius
source. The selected prime rows and cofactor columns retain the sharp
`p*c <= R^2-1` mask. When the cutoff quotient at a prime is its selected
cofactor, the incidence matrix is the signed lower-prefix matrix.

The unit determinant and uniform l2 inverse bound (<=2) are elementary
consequences explained in `research/ALPOGE_GZ_PHYSICAL_LIFT_ATTACK_20261120.md`.
The asymptotic rank count needs an external prime-gap theorem NOT in Lean;
no RH, new Mertens exponent or automorphic-error inequality is asserted.
-/

open scoped ArithmeticFunction.Moebius

namespace RHLean.Analysis

/-- Physical high-prime Mobius incidence, with the literal square cutoff. -/
def alpogeSelectedHighPrimeSource (R : ℕ) {m : ℕ}
    (p q : Fin m → ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  fun i j =>
    if p i * q j ≤ R ^ 2 - 1 then
      (ArithmeticFunction.moebius (p i * q j) : ℤ)
    else 0

/-- The exact source is a signed lower-prefix matrix whenever the selected
cutoff quotient is `q_i=floor((R^2-1)/p_i)`, expressed by its integer
inequalities. All physical prime/cofactor masks are preserved. -/
theorem alpogeSelectedHighPrimeSource_eq_lowerPrefix
    (R : ℕ) {m : ℕ} (p q : Fin m → ℕ)
    (hp : ∀ i, (p i).Prime ∧ R < p i)
    (hqpos : ∀ j, 1 ≤ q j)
    (hqlt : ∀ j, q j < R)
    (hqmono : StrictMono q)
    (hquot : ∀ i, p i * q i ≤ R ^ 2 - 1 ∧
      R ^ 2 - 1 < p i * (q i + 1))
    (i j : Fin m) :
    alpogeSelectedHighPrimeSource R p q i j =
      if j ≤ i then -(ArithmeticFunction.moebius (q j) : ℤ) else 0 := by
  have ht : LargePrimeTransportData R (q j) (p i) :=
    ⟨hqpos j, hqlt j, (hp i).1, (hp i).2⟩
  by_cases hji : j ≤ i
  · have hqji : q j ≤ q i := hqmono.monotone hji
    have hmul : p i * q j ≤ p i * q i := Nat.mul_le_mul_left (p i) hqji
    have hle : p i * q j ≤ R ^ 2 - 1 := hmul.trans (hquot i).1
    simp [alpogeSelectedHighPrimeSource, hji, hle, ht.moebius_mul_eq_neg]
  · have hij : i < j := lt_of_not_ge hji
    have hqq : q i < q j := hqmono hij
    have hqsucc : q i + 1 ≤ q j := Nat.succ_le_iff.mpr hqq
    have hmul : p i * (q i + 1) ≤ p i * q j :=
      Nat.mul_le_mul_left (p i) hqsucc
    have hnle : ¬p i * q j ≤ R ^ 2 - 1 := by
      exact not_le.mpr ((hquot i).2.trans_le hmul)
    simp [alpogeSelectedHighPrimeSource, hji, hnle]

/-- The signed *second* Selberg source, not the vanishing first von Mangoldt
coefficient. Its nonzero mixed semiprime face retains the physical prefix. -/
noncomputable def alpogeSelectedSecondSelbergSource (R : ℕ) {m : ℕ}
    (p q : Fin m → ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j =>
    if p i * q j ≤ R ^ 2 - 1 then
      nativePNTSignedSecondSelbergKernel (p i * q j)
    else 0

/-- **Exact live semiprime source.** Unlike the first-von-Mangoldt coefficient,
the signed second Selberg kernel on two distinct primes equals
`2 * log(p) * log(q)`, with the source mask unchanged.
All complementary signed Selberg faces must still be returned in any
full-source RH-strength estimate. -/
theorem alpogeSelectedSecondSelbergSource_eq_weightedLowerPrefix
    (R : ℕ) {m : ℕ} (p q : Fin m → ℕ)
    (hp : ∀ i, (p i).Prime ∧ R < p i)
    (hqPrime : ∀ j, (q j).Prime)
    (hqlt : ∀ j, q j < R)
    (hqmono : StrictMono q)
    (hquot : ∀ i, p i * q i ≤ R ^ 2 - 1 ∧
      R ^ 2 - 1 < p i * (q i + 1))
    (i j : Fin m) :
    alpogeSelectedSecondSelbergSource R p q i j =
      if j ≤ i then 2 * Real.log (p i : ℝ) * Real.log (q j : ℝ) else 0 := by
  have hneq : p i ≠ q j :=
    ne_of_gt (lt_trans (hqlt j) (hp i).2)
  by_cases hji : j ≤ i
  · have hqji : q j ≤ q i := hqmono.monotone hji
    have hmul : p i * q j ≤ p i * q i := Nat.mul_le_mul_left (p i) hqji
    have hle : p i * q j ≤ R ^ 2 - 1 := hmul.trans (hquot i).1
    simp [alpogeSelectedSecondSelbergSource, hji, hle,
      nativePNTSignedSecondSelbergKernel_mul_distinct_primes
        (p i) (q j) (hp i).1 (hqPrime j) hneq]
  · have hij : i < j := lt_of_not_ge hji
    have hqq : q i < q j := hqmono hij
    have hqsucc : q i + 1 ≤ q j := Nat.succ_le_iff.mpr hqq
    have hmul : p i * (q i + 1) ≤ p i * q j :=
      Nat.mul_le_mul_left (p i) hqsucc
    have hnle : ¬p i * q j ≤ R ^ 2 - 1 := by
      exact not_le.mpr ((hquot i).2.trans_le hmul)
    simp [alpogeSelectedSecondSelbergSource, hji, hnle]

/-- **Source-aligned reciprocal quotient.** In the dyadic prime-cofactor band
`Q <= q_i < 2Q`, every active selected semiprime `p_i*q_j` with
`j <= i` has the *fixed* reciprocal quotient
`floor((R^2-1)/(p_i*q_j)) = 1`.

This is the critical response-side restriction: high matrix rank alone does
not produce independent values of the lower-scale Chebyshev error. -/
theorem alpogeSelectedDyadicReciprocalQuotient_eq_one
    (R Q : ℕ) {m : ℕ} (p q : Fin m → ℕ)
    (hqmono : StrictMono q)
    (hqband : ∀ i, Q ≤ q i ∧ q i < 2 * Q)
    (hquot : ∀ i, p i * q i ≤ R ^ 2 - 1 ∧
      R ^ 2 - 1 < p i * (q i + 1))
    (i j : Fin m) (hji : j ≤ i) :
    (R ^ 2 - 1) / (p i * q j) = 1 := by
  have hqji : q j ≤ q i := hqmono.monotone hji
  have hstep : q i + 1 ≤ 2 * q j := by
    have hqi := (hqband i).2
    have hqj := (hqband j).1
    omega
  have hlo : 1 * (p i * q j) ≤ R ^ 2 - 1 := by
    simpa using
      (Nat.mul_le_mul_left (p i) hqji).trans (hquot i).1
  have hhi : R ^ 2 - 1 < (1 + 1) * (p i * q j) := by
    calc
      R ^ 2 - 1 < p i * (q i + 1) := (hquot i).2
      _ ≤ p i * (2 * q j) := Nat.mul_le_mul_left (p i) hstep
      _ = (1 + 1) * (p i * q j) := by ring
  exact Nat.div_eq_of_lt_le hlo hhi

/-- Exactly the selected term of the full second-Selberg error convolution,
with its *actual* reciprocal quotient and no surrogate coefficients. -/
noncomputable def alpogeSelectedSecondSelbergErrorResponse (R : ℕ) {m : ℕ}
    (p q : Fin m → ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => alpogeSelectedSecondSelbergSource R p q i j *
    nativePNTError ((R ^ 2 - 1) / (p i * q j))

/-- Each selected active second-Selberg direction has response `E(1)=-1`:
the signed contribution is a fixed **negative credit**, not an independent
error variable. It must be returned together with the full complementary
second-Selberg source before any upper estimate or RH conclusion. -/
theorem alpogeSelectedSecondSelbergErrorResponse_eq_negativePrefix
    (R Q : ℕ) {m : ℕ} (p q : Fin m → ℕ)
    (hp : ∀ i, (p i).Prime ∧ R < p i)
    (hqPrime : ∀ j, (q j).Prime)
    (hqlt : ∀ j, q j < R)
    (hqmono : StrictMono q)
    (hqband : ∀ i, Q ≤ q i ∧ q i < 2 * Q)
    (hquot : ∀ i, p i * q i ≤ R ^ 2 - 1 ∧
      R ^ 2 - 1 < p i * (q i + 1))
    (i j : Fin m) :
    alpogeSelectedSecondSelbergErrorResponse R p q i j =
      if j ≤ i then -(2 * Real.log (p i : ℝ) * Real.log (q j : ℝ))
      else 0 := by
  have hsource := alpogeSelectedSecondSelbergSource_eq_weightedLowerPrefix
    R p q hp hqPrime hqlt hqmono hquot i j
  by_cases hji : j ≤ i
  · have hdiv := alpogeSelectedDyadicReciprocalQuotient_eq_one
      R Q p q hqmono hqband hquot i j hji
    simp [alpogeSelectedSecondSelbergErrorResponse, hsource, hdiv,
      nativePNTError, nativePsi, hji]
  · simp [alpogeSelectedSecondSelbergErrorResponse, hsource, hji]

end RHLean.Analysis
