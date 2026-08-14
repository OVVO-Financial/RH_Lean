import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelbergWheelFrontier
import RHLean.Analysis.NativePNTSignedWheelRemainder

/-!
# Signed second-Selberg charge on the square-root wheel frontier

This file inserts the exact wheel-frontier faces from
`NativePNTSignedSecondSelbergWheelFrontier` into the signed second-Selberg
recurrence from `NativePNTSignedSecondSelberg`.

Below `N < 2 y^2`, every nonzero partial-wheel error site lies strictly above
`y^2`, hence its reciprocal quotient is exactly `N / n = 1`.  Consequently

* its second-kernel error weight is `nativePNTError 1 = -1`;
* its pushed-down signed Selberg remainder is zero; and
* its floor-log defect is explicit.

The resulting effective frontier charge is therefore not an auxiliary positive
mass: it is exactly the quantity subtracted by the true signed second-Selberg
ledger after the frontier pieces are combined before taking norms.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- The actual unresolved partial-wheel sites at cutoff `y` and endpoint `N`. -/
def nativePNTSignedSecondSelbergWheelFrontierSites
    (y N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun n => μ n - partialPrimeWheelSite y N n ≠ 0)

@[simp] theorem mem_nativePNTSignedSecondSelbergWheelFrontierSites
    {y N n : ℕ} :
    n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N ↔
      n ∈ Finset.Icc 1 N ∧
        μ n - partialPrimeWheelSite y N n ≠ 0 := by
  simp [nativePNTSignedSecondSelbergWheelFrontierSites]

/-- Raw signed second-kernel charge on the unresolved wheel frontier. -/
def nativePNTSignedSecondSelbergWheelFrontierCharge
    (y N : ℕ) : ℝ :=
  ∑ n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N,
    nativePNTSignedSecondSelbergKernel n

/-- The same frontier charge with the actual PNT error at the reciprocal
quotient. -/
def nativePNTSignedSecondSelbergWheelFrontierErrorMass
    (y N : ℕ) : ℝ :=
  ∑ n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N,
    nativePNTSignedSecondSelbergKernel n * nativePNTError (N / n)

/-- The pushed-down signed Selberg remainder restricted to the same frontier. -/
def nativePNTSignedSecondSelbergWheelFrontierRemainderMass
    (y N : ℕ) : ℝ :=
  ∑ n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N,
    Λ n * nativePNTSignedSelbergRemainder (N / n)

/-- The exact floor-log defect restricted to the same frontier. -/
def nativePNTSignedSecondSelbergWheelFrontierFloorDefectMass
    (y N : ℕ) : ℝ :=
  ∑ n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N,
    Λ n * nativePNTError (N / n) *
      (Real.log (N : ℝ) - Real.log (n : ℝ) -
        Real.log ((N / n : ℕ) : ℝ))

/-- Pointwise charge after combining the true signed second kernel with the
frontier part of the floor-log defect. -/
def nativePNTSignedSecondSelbergWheelFrontierEffectiveAtom
    (N n : ℕ) : ℝ :=
  nativePNTSignedSecondSelbergKernel n -
    Λ n * (Real.log (N : ℝ) - Real.log (n : ℝ))

/-- Effective charge on the actual unresolved wheel frontier.  This is the
frontier quantity that enters the exact signed second-Selberg ledger. -/
def nativePNTSignedSecondSelbergWheelFrontierEffectiveCharge
    (y N : ℕ) : ℝ :=
  ∑ n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N,
    nativePNTSignedSecondSelbergWheelFrontierEffectiveAtom N n

/-- Below twice the square of the wheel cutoff, every frontier site has
reciprocal quotient exactly one. -/
theorem nativePNTSignedSecondSelbergWheelFrontier_div_eq_one
    {y N n : ℕ} (hscale : N < 2 * y ^ 2)
    (hn : n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N) :
    N / n = 1 := by
  have hnData := mem_nativePNTSignedSecondSelbergWheelFrontierSites.mp hn
  have hnI := Finset.mem_Icc.mp hnData.1
  have hnpos : 0 < n := by omega
  rcases partialPrimeWheel_nonzero_error_factorization_of_two_mul_sq
      y N hscale hnpos hnI.2 hnData.2 with
    ⟨q, r, _hqPrime, _hrPrime, hyq, hyr, _hresolved, hnqr⟩
  have hyq1 : y + 1 ≤ q := by omega
  have hyr1 : y + 1 ≤ r := by omega
  have hsqStep : (y + 1) ^ 2 ≤ q * r := by
    simpa [pow_two] using Nat.mul_le_mul hyq1 hyr1
  have hySqLtSuccSq : y ^ 2 < (y + 1) ^ 2 :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  have hySqLtN : y ^ 2 < n := by
    rw [hnqr]
    exact hySqLtSuccSq.trans_le hsqStep
  have hNltTwoN : N < 2 * n := by omega
  have hlo : 1 * n ≤ N := by simpa using hnI.2
  have hhi : N < (1 + 1) * n := by simpa using hNltTwoN
  exact Nat.div_eq_of_lt_le hlo hhi

@[simp] theorem nativePNTError_one : nativePNTError 1 = -1 := by
  simp [nativePNTError, nativePsi]

@[simp] theorem nativePNTSignedSelbergRemainder_one :
    nativePNTSignedSelbergRemainder 1 = 0 := by
  simp [nativePNTSignedSelbergRemainder, nativeSelbergPair, nativePsi]

/-- On the frontier, the actual second-kernel error mass is exactly the
negative raw charge. -/
theorem nativePNTSignedSecondSelbergWheelFrontierErrorMass_eq_neg_charge
    {y N : ℕ} (hscale : N < 2 * y ^ 2) :
    nativePNTSignedSecondSelbergWheelFrontierErrorMass y N =
      -nativePNTSignedSecondSelbergWheelFrontierCharge y N := by
  unfold nativePNTSignedSecondSelbergWheelFrontierErrorMass
    nativePNTSignedSecondSelbergWheelFrontierCharge
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hdiv := nativePNTSignedSecondSelbergWheelFrontier_div_eq_one hscale hn
  rw [hdiv, nativePNTError_one]
  ring

/-- The pushed-down signed Selberg remainder vanishes identically on the
frontier because every lower quotient is one. -/
theorem nativePNTSignedSecondSelbergWheelFrontierRemainderMass_eq_zero
    {y N : ℕ} (hscale : N < 2 * y ^ 2) :
    nativePNTSignedSecondSelbergWheelFrontierRemainderMass y N = 0 := by
  unfold nativePNTSignedSecondSelbergWheelFrontierRemainderMass
  apply Finset.sum_eq_zero
  intro n hn
  have hdiv := nativePNTSignedSecondSelbergWheelFrontier_div_eq_one hscale hn
  rw [hdiv, nativePNTSignedSelbergRemainder_one]
  ring

/-- The frontier floor-log defect is the negative logarithmic correction that
must be combined with the raw second-kernel charge. -/
theorem nativePNTSignedSecondSelbergWheelFrontierFloorDefectMass_eq
    {y N : ℕ} (hscale : N < 2 * y ^ 2) :
    nativePNTSignedSecondSelbergWheelFrontierFloorDefectMass y N =
      -∑ n ∈ nativePNTSignedSecondSelbergWheelFrontierSites y N,
        Λ n * (Real.log (N : ℝ) - Real.log (n : ℝ)) := by
  unfold nativePNTSignedSecondSelbergWheelFrontierFloorDefectMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hdiv := nativePNTSignedSecondSelbergWheelFrontier_div_eq_one hscale hn
  rw [hdiv, nativePNTError_one]
  simp
  ring

/-- Combining the frontier second-kernel and floor-defect pieces gives exactly
the negative effective frontier charge. -/
theorem nativePNTSignedSecondSelbergWheelFrontierError_sub_floor_eq_neg_effectiveCharge
    {y N : ℕ} (hscale : N < 2 * y ^ 2) :
    nativePNTSignedSecondSelbergWheelFrontierErrorMass y N -
        nativePNTSignedSecondSelbergWheelFrontierFloorDefectMass y N =
      -nativePNTSignedSecondSelbergWheelFrontierEffectiveCharge y N := by
  rw [nativePNTSignedSecondSelbergWheelFrontierErrorMass_eq_neg_charge hscale,
    nativePNTSignedSecondSelbergWheelFrontierFloorDefectMass_eq hscale]
  unfold nativePNTSignedSecondSelbergWheelFrontierCharge
    nativePNTSignedSecondSelbergWheelFrontierEffectiveCharge
    nativePNTSignedSecondSelbergWheelFrontierEffectiveAtom
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- On a prime square, the effective frontier atom is the negative diagonal
with the floor-log correction already absorbed. -/
theorem nativePNTSignedSecondSelbergWheelFrontierEffectiveAtom_prime_sq
    (N q : ℕ) (hq : q.Prime) :
    nativePNTSignedSecondSelbergWheelFrontierEffectiveAtom N (q ^ 2) =
      -Real.log (q : ℝ) *
        (Real.log (N : ℝ) - Real.log (q : ℝ)) := by
  unfold nativePNTSignedSecondSelbergWheelFrontierEffectiveAtom
  rw [nativePNTSignedSecondSelbergKernel_prime_sq q hq]
  have hlam : Λ (q ^ 2) = Real.log (q : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime hq]
  rw [hlam, Nat.cast_pow, Real.log_pow]
  norm_num
  ring

/-- On two distinct primes, the floor-log correction vanishes because the
von Mangoldt weight of their product is zero; the positive mixed face survives
unchanged. -/
theorem nativePNTSignedSecondSelbergWheelFrontierEffectiveAtom_mul_distinct_primes
    (N q r : ℕ) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) :
    nativePNTSignedSecondSelbergWheelFrontierEffectiveAtom N (q * r) =
      2 * Real.log (q : ℝ) * Real.log (r : ℝ) := by
  unfold nativePNTSignedSecondSelbergWheelFrontierEffectiveAtom
  rw [nativePNTSignedSecondSelbergKernel_mul_distinct_primes q r hq hr hqr]
  have hnotPow : ¬ IsPrimePow (q * r) := by
    intro hpow
    rcases (isPrimePow_nat_iff (q * r)).1 hpow with ⟨p, k, hp, hk, hEq⟩
    have hqDvd : q ∣ p ^ k := by
      rw [hEq]
      exact dvd_mul_right q r
    have hrDvd : r ∣ p ^ k := by
      rw [hEq]
      exact dvd_mul_left r q
    have hqp : q = p := by
      exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqDvd)
    have hrp : r = p := by
      exact (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hrDvd)
    exact hqr (hqp.trans hrp.symm)
  have hlam : Λ (q * r) = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnotPow
  rw [hlam]
  ring

/-- The full signed second-kernel mass away from the wheel frontier. -/
def nativePNTSignedSecondSelbergOffFrontierKernelErrorMass
    (y N : ℕ) : ℝ :=
  nativePNTSignedSecondSelbergKernelErrorMass N -
    nativePNTSignedSecondSelbergWheelFrontierErrorMass y N

/-- The pushed signed Selberg remainder away from the wheel frontier. -/
def nativePNTSignedSecondSelbergOffFrontierRemainderMass
    (y N : ℕ) : ℝ :=
  nativePNTLambdaSignedSelbergRemainderMass N -
    nativePNTSignedSecondSelbergWheelFrontierRemainderMass y N

/-- The floor-log defect away from the wheel frontier. -/
def nativePNTSignedSecondSelbergOffFrontierFloorDefectMass
    (y N : ℕ) : ℝ :=
  nativePNTLambdaFloorLogSignedDefectMass N -
    nativePNTSignedSecondSelbergWheelFrontierFloorDefectMass y N

/-- **Exact frontier-extracted signed second-Selberg ledger.**  The actual
wheel-frontier contribution appears as `- effectiveCharge`; no frontier
remainder or floor defect is estimated separately. -/
theorem nativePNTError_mul_log_sq_eq_offFrontier_sub_effectiveCharge
    (y N : ℕ) (hscale : N < 2 * y ^ 2) :
    nativePNTError N * (Real.log (N : ℝ)) ^ 2 =
      nativePNTSignedSelbergRemainder N * Real.log (N : ℝ) -
        nativePNTSignedSecondSelbergOffFrontierRemainderMass y N +
        nativePNTSignedSecondSelbergOffFrontierKernelErrorMass y N -
        nativePNTSignedSecondSelbergOffFrontierFloorDefectMass y N -
        nativePNTSignedSecondSelbergWheelFrontierEffectiveCharge y N := by
  rw [nativePNTError_mul_log_sq_eq_signedSecondSelberg]
  unfold nativePNTSignedSecondSelbergOffFrontierRemainderMass
    nativePNTSignedSecondSelbergOffFrontierKernelErrorMass
    nativePNTSignedSecondSelbergOffFrontierFloorDefectMass
  have hrem :=
    nativePNTSignedSecondSelbergWheelFrontierRemainderMass_eq_zero hscale
  have hcharge :=
    nativePNTSignedSecondSelbergWheelFrontierError_sub_floor_eq_neg_effectiveCharge
      hscale
  rw [hrem]
  ring_nf at hcharge ⊢
  linarith

end RHLean.Analysis
