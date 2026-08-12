import Mathlib
import RHLean.Analysis.NativePNTErdosContraction
import RHLean.Analysis.SquarePrefixMertensBridge

/-!
# Native square-prefix Möbius contraction for PNT

This module isolates the finite arithmetic operation that is allowed to improve
an elementary PNT envelope: adjoin one fresh prime and record the resulting
Möbius sign reversal.  The geometry is expressed at the native square-prefix
endpoints

`X_n = (n + 1)^2 - 1`.

No endpoint PNT theorem is changed here.  In particular this file does not
replace `nativePrimeNumberTheorem`, the Axer bridge, or the `theta -> pi`
transfer.  It supplies a square-prefix reciprocal-fibre layer and a thin rate
bridge to the already-proved cubic recurrence.

The key exact identity is pointwise.  If `p` is fresh for `m`, then

`mu(m*p) = -mu(m)`

and therefore the paired reciprocal fibre contracts by the exact factor

`1 - 1/p`.

There is no analytic estimate in this step: the improvement is the finite
Möbius identity itself.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators Topology

namespace RHLean.Analysis

/-! ## Square-prefix geometry -/

/-- The integer block between two consecutive native square-prefix endpoints. -/
def nativePNTSquarePrefixBlock (n : ℕ) : Finset ℕ :=
  Finset.Ioc (squarePrefixEndpoint n) (squarePrefixEndpoint (n + 1))

/-- A generic reciprocal Möbius fibre on a finite cofactor set. -/
def nativeMobiusReciprocalFiber
    (s : Finset ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ m ∈ s, (((μ m : ℤ) : ℝ) / (m : ℝ)) * F m

/-- The same fibre after adjoining one prime coordinate.  Both terms retain the
same frozen fibre value `F m`; all quantitative change is therefore carried by
the exact Möbius sign reversal and the reciprocal denominator. -/
def nativeMobiusAdjoinedPrimeReciprocalFiber
    (s : Finset ℕ) (p : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ m ∈ s,
    ((((μ m : ℤ) : ℝ) / (m : ℝ)) * F m +
      (((μ (m * p) : ℤ) : ℝ) / ((m * p : ℕ) : ℝ)) * F m)

/-- Reciprocal Möbius mass on the full positive square prefix. -/
def nativePNTSquarePrefixMobiusReciprocalFiber
    (n : ℕ) (F : ℕ → ℝ) : ℝ :=
  nativeMobiusReciprocalFiber (Finset.Icc 1 (squarePrefixEndpoint n)) F

/-- Reciprocal Möbius mass on one square-prefix block. -/
def nativePNTSquarePrefixBlockMobiusReciprocalFiber
    (n : ℕ) (F : ℕ → ℝ) : ℝ :=
  nativeMobiusReciprocalFiber (nativePNTSquarePrefixBlock n) F

/-! ## The only improvement step: adjoin one fresh prime -/

/-- Adjoining a prime coprime to the cofactor reverses its Möbius sign. -/
theorem nativeMobius_adjoin_prime
    (m p : ℕ) (hp : p.Prime) (hcop : Nat.Coprime m p) :
    μ (m * p) = -μ m := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
  rw [ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- Exact reciprocal-fibre contraction for one cofactor after adjoining a fresh
prime.  Nothing is majorized: this is an equality. -/
theorem nativeMobius_reciprocal_pair_eq
    (m p : ℕ) (F : ℕ → ℝ)
    (hm : 1 ≤ m) (hp : p.Prime) (hcop : Nat.Coprime m p) :
    ((((μ m : ℤ) : ℝ) / (m : ℝ)) * F m +
      (((μ (m * p) : ℤ) : ℝ) / ((m * p : ℕ) : ℝ)) * F m) =
      (1 - 1 / (p : ℝ)) *
        ((((μ m : ℤ) : ℝ) / (m : ℝ)) * F m) := by
  rw [nativeMobius_adjoin_prime m p hp hcop]
  push_cast
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  field_simp [hm0, hp0]
  ring

/-- Finite reciprocal-fibre contraction obtained by pairing every cofactor with
its fresh-prime extension.  This is the summed form of the only quantitative
lever used in this module. -/
theorem nativeMobiusAdjoinedPrimeReciprocalFiber_eq
    (s : Finset ℕ) (p : ℕ) (F : ℕ → ℝ)
    (hp : p.Prime)
    (hpos : ∀ m ∈ s, 1 ≤ m)
    (hcop : ∀ m ∈ s, Nat.Coprime m p) :
    nativeMobiusAdjoinedPrimeReciprocalFiber s p F =
      (1 - 1 / (p : ℝ)) * nativeMobiusReciprocalFiber s F := by
  unfold nativeMobiusAdjoinedPrimeReciprocalFiber nativeMobiusReciprocalFiber
  calc
    (∑ m ∈ s,
      ((((μ m : ℤ) : ℝ) / (m : ℝ)) * F m +
        (((μ (m * p) : ℤ) : ℝ) / ((m * p : ℕ) : ℝ)) * F m)) =
        ∑ m ∈ s,
          (1 - 1 / (p : ℝ)) *
            ((((μ m : ℤ) : ℝ) / (m : ℝ)) * F m) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact nativeMobius_reciprocal_pair_eq m p F (hpos m hm) hp (hcop m hm)
    _ = (1 - 1 / (p : ℝ)) *
        (∑ m ∈ s, (((μ m : ℤ) : ℝ) / (m : ℝ)) * F m) := by
      rw [Finset.mul_sum]

/-- A prime strictly beyond a square prefix is coprime to every positive
cofactor in that prefix. -/
theorem nativePNTSquarePrefix_freshPrime_coprime
    (n m p : ℕ)
    (hm : m ∈ Finset.Icc 1 (squarePrefixEndpoint n))
    (hp : p.Prime) (hfresh : squarePrefixEndpoint n < p) :
    Nat.Coprime m p := by
  have hmI := Finset.mem_Icc.mp hm
  have hmpos : 0 < m := by omega
  have hmp : m < p := lt_of_le_of_lt hmI.2 hfresh
  exact (Nat.coprime_of_lt_prime (Nat.ne_of_gt hmpos) hmp hp).symm

/-- Exact contraction of the complete reciprocal Möbius square prefix after one
fresh prime is adjoined. -/
theorem nativePNTSquarePrefixMobiusReciprocalFiber_adjoin_prime
    (n p : ℕ) (F : ℕ → ℝ)
    (hp : p.Prime) (hfresh : squarePrefixEndpoint n < p) :
    nativeMobiusAdjoinedPrimeReciprocalFiber
        (Finset.Icc 1 (squarePrefixEndpoint n)) p F =
      (1 - 1 / (p : ℝ)) *
        nativePNTSquarePrefixMobiusReciprocalFiber n F := by
  unfold nativePNTSquarePrefixMobiusReciprocalFiber
  apply nativeMobiusAdjoinedPrimeReciprocalFiber_eq
  · exact hp
  · intro m hm
    exact (Finset.mem_Icc.mp hm).1
  · intro m hm
    exact nativePNTSquarePrefix_freshPrime_coprime n m p hm hp hfresh

/-- The same fresh-prime contraction on one square-prefix block. -/
theorem nativePNTSquarePrefixBlockMobiusReciprocalFiber_adjoin_prime
    (n p : ℕ) (F : ℕ → ℝ)
    (hp : p.Prime) (hfresh : squarePrefixEndpoint (n + 1) < p) :
    nativeMobiusAdjoinedPrimeReciprocalFiber
        (nativePNTSquarePrefixBlock n) p F =
      (1 - 1 / (p : ℝ)) *
        nativePNTSquarePrefixBlockMobiusReciprocalFiber n F := by
  unfold nativePNTSquarePrefixBlockMobiusReciprocalFiber
  apply nativeMobiusAdjoinedPrimeReciprocalFiber_eq
  · exact hp
  · intro m hm
    have hmI := Finset.mem_Ioc.mp hm
    have hnonneg : 0 ≤ squarePrefixEndpoint n := Nat.zero_le _
    omega
  · intro m hm
    have hmI := Finset.mem_Ioc.mp hm
    have hmpos : 0 < m := by
      have hnonneg : 0 ≤ squarePrefixEndpoint n := Nat.zero_le _
      omega
    have hmp : m < p := lt_of_le_of_lt hmI.2 hfresh
    exact (Nat.coprime_of_lt_prime (Nat.ne_of_gt hmpos) hmp hp).symm

/-! ## Square-prefix packaging of the absolute Selberg error recurrence -/

/-- The absolute reciprocal error fibre at the native square-prefix endpoint. -/
def nativePNTSquarePrefixAbsoluteErrorFiber (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (squarePrefixEndpoint n),
    Λ d * |nativePNTError (squarePrefixEndpoint n / d)|

/-- The existing absolute Selberg recurrence, stated only at native square-prefix
endpoints.  This is a reindexing theorem, not a new estimate. -/
theorem nativePNTError_abs_log_le_squarePrefixFiber
    (n : ℕ) (hN : 3 ≤ squarePrefixEndpoint n) :
    |nativePNTError (squarePrefixEndpoint n)| *
        Real.log (squarePrefixEndpoint n : ℝ) ≤
      nativePNTSquarePrefixAbsoluteErrorFiber n +
        (3 * (Real.log 4 + 2) + 173) * (squarePrefixEndpoint n : ℝ) := by
  simpa [nativePNTSquarePrefixAbsoluteErrorFiber] using
    (nativePNTError_abs_log_le_weighted (squarePrefixEndpoint n) hN)

/-! ## Explicit rate packaging -/

/-- A density coefficient with exactly the requested quadratic dependence on
the tolerance.  The arithmetic input is separated as `kappa`; adjoining primes
is what is allowed to improve `kappa`. -/
def nativePNTSquarePrefixDensityCoefficient (kappa eps : ℝ) : ℝ :=
  kappa * eps ^ 2

/-- Positivity of the square-prefix density coefficient is completely explicit. -/
theorem nativePNTSquarePrefixDensityCoefficient_pos
    (kappa eps : ℝ) (hkappa : 0 < kappa) (heps : 0 < eps) :
    0 < nativePNTSquarePrefixDensityCoefficient kappa eps := by
  unfold nativePNTSquarePrefixDensityCoefficient
  exact mul_pos hkappa (pow_pos heps 2)

/-- Rate-preserving cubic package.  If a square-prefix argument supplies the
cubic decrement with coefficient `kappa * eps^2`, the finite-step budget keeps
that exact dependence and uses no `Eventually`. -/
theorem nativePNTSquarePrefix_cubic_rate
    (a : ℕ → ℝ) (kappa eps : ℝ)
    (hkappa : 0 < kappa) (heps : 0 < eps)
    (hnonneg : ∀ n, 0 ≤ a n)
    (hrec : ∀ n,
      a (n + 1) ≤ a n -
        nativePNTSquarePrefixDensityCoefficient kappa eps * (a n) ^ 3)
    (n : ℕ) :
    nativePNTSquarePrefixDensityCoefficient kappa eps * (n : ℝ) *
        (a n) ^ 3 ≤ a 0 := by
  apply cubic_recurrence_rate
  · exact nativePNTSquarePrefixDensityCoefficient_pos kappa eps hkappa heps
  · exact hnonneg
  · exact hrec

/-- The corresponding qualitative limit is routed through the already-proved
abstract cubic recurrence theorem. -/
theorem nativePNTSquarePrefix_tendsto_zero_of_cubic_rate
    (a : ℕ → ℝ) (kappa eps : ℝ)
    (hkappa : 0 < kappa) (heps : 0 < eps)
    (hnonneg : ∀ n, 0 ≤ a n)
    (hrec : ∀ n,
      a (n + 1) ≤ a n -
        nativePNTSquarePrefixDensityCoefficient kappa eps * (a n) ^ 3) :
    Tendsto a atTop (𝓝 0) := by
  apply tendsto_zero_of_cubic_recurrence
  · exact nativePNTSquarePrefixDensityCoefficient_pos kappa eps hkappa heps
  · exact hnonneg
  · exact hrec

/-- An explicit iteration count for the existing calibrated native-PNT cubic
slope.  This removes the final nonconstructive choice of an iteration index. -/
def nativePNTSquarePrefixIterationBudget (eta : ℝ) : ℕ :=
  ⌊6 / (nativePNTCubicConstant * eta ^ 3)⌋₊ + 1

/-- The explicit iteration count satisfies the cubic budget inequality. -/
theorem nativePNTSquarePrefixIterationBudget_spec
    (eta : ℝ) (heta : 0 < eta) :
    6 < nativePNTCubicConstant *
        (nativePNTSquarePrefixIterationBudget eta : ℝ) * eta ^ 3 := by
  have hC : 0 < nativePNTCubicConstant := by
    norm_num [nativePNTCubicConstant]
  have hcoef : 0 < nativePNTCubicConstant * eta ^ 3 :=
    mul_pos hC (pow_pos heta 3)
  have hfloor :
      6 / (nativePNTCubicConstant * eta ^ 3) <
        (nativePNTSquarePrefixIterationBudget eta : ℝ) := by
    unfold nativePNTSquarePrefixIterationBudget
    push_cast
    simpa using
      (Nat.lt_floor_add_one (6 / (nativePNTCubicConstant * eta ^ 3)))
  have hmul := (div_lt_iff₀ hcoef).mp hfloor
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Explicit-rate affine-envelope wrapper using the square-prefix iteration
budget.  The endpoint theorem itself is unchanged. -/
theorem nativePNTHasAffineEnvelope_of_squarePrefix_budget
    (eta : ℝ) (heta : 0 < eta) :
    nativePNTHasAffineEnvelope eta := by
  exact nativePNTHasAffineEnvelope_of_cubic_budget
    eta heta (nativePNTSquarePrefixIterationBudget eta)
      (nativePNTSquarePrefixIterationBudget_spec eta heta)

end RHLean.Analysis
