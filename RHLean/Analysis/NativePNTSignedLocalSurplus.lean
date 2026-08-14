import Mathlib
import RHLean.Analysis.NativePNTSignedWheelRemainder

/-!
# Signed local surplus in reciprocal Möbius coordinates

The absolute evolving-tail state loses polynomial scale because it destroys
signed cancellation before self-composition.  This module starts the replacement
arithmetic directly in the signed Möbius/wheel coordinate.

There are two steps here.

* localize the exact Möbius transform and its wheel/residual splitting on an
  arbitrary finite cofactor packet;
* pair the actual reciprocal atoms obtained by adjoining one fresh prime.

For a fixed inner quotient `k`, the atoms at `(m,p*k)` and `(m*p,k)` have the
same Chebyshev endpoint.  Fresh-prime Möbius sign reversal therefore cancels
the duplicated `log k` contribution exactly.  The resulting drop in absolute
mass is an explicit nonnegative local surplus, not a new analytic premise.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- One signed reciprocal Möbius atom in the PNT error transform. -/
def nativePNTMobiusSignedAtom (N m k : ℕ) : ℝ :=
  ((μ m : ℤ) : ℝ) * Real.log (k : ℝ) *
    nativePNTError (N / (m * k))

/-- Signed Möbius reciprocal mass restricted to an arbitrary cofactor packet. -/
def nativePNTMobiusSignedCofactorMassOn
    (N : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ m ∈ s,
    ((μ m : ℤ) : ℝ) *
      nativePNTMobiusLogReciprocalFiber N m
        (fun d => nativePNTError (N / d))

/-- The packet mass is literally the double sum of its signed reciprocal atoms. -/
theorem nativePNTMobiusSignedCofactorMassOn_eq_atom_sum
    (N : ℕ) (s : Finset ℕ) :
    nativePNTMobiusSignedCofactorMassOn N s =
      ∑ m ∈ s, ∑ k ∈ Finset.Icc 1 (N / m),
        nativePNTMobiusSignedAtom N m k := by
  unfold nativePNTMobiusSignedCofactorMassOn
    nativePNTMobiusLogReciprocalFiber nativePNTMobiusSignedAtom
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- The full signed Möbius error mass is the cofactor-local mass on the complete
positive prefix. -/
theorem nativePNTMobiusReciprocalSignedErrorMass_eq_cofactorMassOn
    (N : ℕ) :
    nativePNTMobiusReciprocalSignedErrorMass N =
      nativePNTMobiusSignedCofactorMassOn N (Finset.Icc 1 N) := by
  rfl

/-- Local resolved wheel mass on an arbitrary cofactor packet. -/
def nativePNTWheelResolvedSignedMassOn
    (y N : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ m ∈ s,
    (RHLean.Arithmetic.partialPrimeWheelSite y N m : ℝ) *
      nativePNTMobiusLogReciprocalFiber N m
        (fun d => nativePNTError (N / d))

/-- Local unresolved wheel residual on an arbitrary cofactor packet. -/
def nativePNTWheelResidualSignedMassOn
    (y N : ℕ) (s : Finset ℕ) : ℝ :=
  ∑ m ∈ s,
    ((((μ m : ℤ) : ℝ) -
        (RHLean.Arithmetic.partialPrimeWheelSite y N m : ℝ)) *
      nativePNTMobiusLogReciprocalFiber N m
        (fun d => nativePNTError (N / d)))

/-- Exact signed wheel/residual splitting holds packet by packet.  This is the
local version needed before any packetwise estimate is taken. -/
theorem nativePNTMobiusSignedCofactorMassOn_eq_wheel_add_residual
    (y N : ℕ) (s : Finset ℕ) :
    nativePNTMobiusSignedCofactorMassOn N s =
      nativePNTWheelResolvedSignedMassOn y N s +
        nativePNTWheelResidualSignedMassOn y N s := by
  unfold nativePNTMobiusSignedCofactorMassOn
    nativePNTWheelResolvedSignedMassOn nativePNTWheelResidualSignedMassOn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

/-- Local cofactor masses add exactly across disjoint packets. -/
theorem nativePNTMobiusSignedCofactorMassOn_union
    (N : ℕ) (s t : Finset ℕ) (hdisj : Disjoint s t) :
    nativePNTMobiusSignedCofactorMassOn N (s ∪ t) =
      nativePNTMobiusSignedCofactorMassOn N s +
        nativePNTMobiusSignedCofactorMassOn N t := by
  unfold nativePNTMobiusSignedCofactorMassOn
  rw [Finset.sum_union hdisj]

/-- **Fresh-prime signed atom identity.**  The two reciprocal atoms indexed by
`(m,p*k)` and `(m*p,k)` share exactly the same Chebyshev endpoint.  Möbius sign
reversal removes the inner `log k` contribution and leaves only `log p`. -/
theorem nativePNTMobiusSignedAtom_pair_adjoin_prime
    (N m p k : ℕ) (hk : 1 ≤ k)
    (hp : p.Prime) (hcop : Nat.Coprime m p) :
    nativePNTMobiusSignedAtom N m (p * k) +
        nativePNTMobiusSignedAtom N (m * p) k =
      ((μ m : ℤ) : ℝ) * Real.log (p : ℝ) *
        nativePNTError (N / ((m * p) * k)) := by
  have hpair := nativeMobiusLogFiber_pair_adjoin_prime m p k hk hp hcop
  have hmul : m * (p * k) = (m * p) * k := by ring
  unfold nativePNTMobiusSignedAtom
  rw [hmul]
  calc
    ((μ m : ℤ) : ℝ) * Real.log ((p * k : ℕ) : ℝ) *
          nativePNTError (N / ((m * p) * k)) +
        ((μ (m * p) : ℤ) : ℝ) * Real.log (k : ℝ) *
          nativePNTError (N / ((m * p) * k)) =
      (((μ m : ℤ) : ℝ) * Real.log ((p * k : ℕ) : ℝ) +
        ((μ (m * p) : ℤ) : ℝ) * Real.log (k : ℝ)) *
          nativePNTError (N / ((m * p) * k)) := by ring
    _ = ((μ m : ℤ) : ℝ) * Real.log (p : ℝ) *
          nativePNTError (N / ((m * p) * k)) := by
      rw [hpair]

/-- **Exact local signed surplus.**  Before pairing, the two absolute atom
masses pay both `log(p*k)` and `log k`.  After the signed fresh-prime pairing,
only `log p` survives.  The absolute-mass drop is exactly twice the duplicated
`log k` mass.

This is the first positive local surplus in the replacement signed state. -/
theorem nativePNTMobiusSignedAtom_pair_abs_surplus_eq
    (N m p k : ℕ) (hk : 1 ≤ k)
    (hp : p.Prime) (hcop : Nat.Coprime m p) :
    |nativePNTMobiusSignedAtom N m (p * k)| +
        |nativePNTMobiusSignedAtom N (m * p) k| -
        |nativePNTMobiusSignedAtom N m (p * k) +
          nativePNTMobiusSignedAtom N (m * p) k| =
      2 * |((μ m : ℤ) : ℝ)| * Real.log (k : ℝ) *
        |nativePNTError (N / ((m * p) * k))| := by
  rw [nativePNTMobiusSignedAtom_pair_adjoin_prime N m p k hk hp hcop]
  unfold nativePNTMobiusSignedAtom
  rw [nativeMobius_adjoin_prime m p hp hcop]
  push_cast
  have hmul : m * (p * k) = (m * p) * k := by ring
  rw [hmul]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (show k ≠ 0 by omega)
  have hpLog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.two_le)
  have hkLog0 : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk)
  rw [Real.log_mul hp0 hk0]
  simp only [abs_mul, abs_neg, abs_of_nonneg hpLog0,
    abs_of_nonneg hkLog0, abs_of_nonneg (add_nonneg hpLog0 hkLog0)]
  ring

/-- A large endpoint error turns the exact fresh-prime cancellation into an
explicit lower bound for local surplus.  No scalar good-mass factorization is
used: the estimate is attached to the actual reciprocal atom. -/
theorem nativePNTMobiusSignedAtom_pair_abs_surplus_ge_of_error
    (N m p k : ℕ) (beta : ℝ)
    (hk : 1 ≤ k) (hp : p.Prime) (hcop : Nat.Coprime m p)
    (hbeta : 0 ≤ beta)
    (herror :
      beta * ((N / ((m * p) * k) : ℕ) : ℝ) ≤
        |nativePNTError (N / ((m * p) * k))|) :
    (2 * |((μ m : ℤ) : ℝ)| * Real.log (k : ℝ)) *
        (beta * ((N / ((m * p) * k) : ℕ) : ℝ)) ≤
      |nativePNTMobiusSignedAtom N m (p * k)| +
        |nativePNTMobiusSignedAtom N (m * p) k| -
        |nativePNTMobiusSignedAtom N m (p * k) +
          nativePNTMobiusSignedAtom N (m * p) k| := by
  have hkLog0 : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk)
  have hcoef :
      0 ≤ 2 * |((μ m : ℤ) : ℝ)| * Real.log (k : ℝ) := by
    positivity
  calc
    (2 * |((μ m : ℤ) : ℝ)| * Real.log (k : ℝ)) *
        (beta * ((N / ((m * p) * k) : ℕ) : ℝ)) ≤
      (2 * |((μ m : ℤ) : ℝ)| * Real.log (k : ℝ)) *
        |nativePNTError (N / ((m * p) * k))| :=
      mul_le_mul_of_nonneg_left herror hcoef
    _ = 2 * |((μ m : ℤ) : ℝ)| * Real.log (k : ℝ) *
        |nativePNTError (N / ((m * p) * k))| := by ring
    _ = |nativePNTMobiusSignedAtom N m (p * k)| +
        |nativePNTMobiusSignedAtom N (m * p) k| -
        |nativePNTMobiusSignedAtom N m (p * k) +
          nativePNTMobiusSignedAtom N (m * p) k| :=
      (nativePNTMobiusSignedAtom_pair_abs_surplus_eq
        N m p k hk hp hcop).symm

end RHLean.Analysis
