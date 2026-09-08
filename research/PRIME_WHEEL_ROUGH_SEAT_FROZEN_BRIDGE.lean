import RHLean.Proof.PrimeWheelRoughSeatCorrelation
import RHLean.Proof.PrimeCombVisualizationDynamics

/-!
# The rough-seat kernel is the existing frozen prime universe

The image-derived signed cutoff kernel and the repository's chronological
frozen prime cube are not merely analogous.  They satisfy the same empty-frame
base case and the same exact fresh-prime finite-difference recurrence, hence
are identical on every finite prime set.

This is the coordinate bridge needed to reuse the existing frozen-window,
first-owner, and Go-wall machinery on the rough-seat correlation without any
new norm or reindexing loss.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- **Kernel/frozen-cube identification.**  On every finite prime universe, the
truncated divisor Möbius kernel is exactly the chronological frozen prime
universe mass.  The proof uses only the common fresh-prime recurrence. -/
theorem primeWheelTruncatedMoebiusKernel_eq_frozenPrimeUniverseMass
    (S : Finset ℕ) (X : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    primeWheelTruncatedMoebiusKernel S X =
      frozenPrimeUniverseMass S X := by
  classical
  induction S using Finset.induction_on generalizing X with
  | empty =>
      simp [primeWheelTruncatedMoebiusKernel,
        RHLean.Arithmetic.primorial,
        frozenPrimeUniverseMass,
        truncatedCubeAlternatingSum,
        primeProductAdmissible,
        primeFaceProduct,
        booleanCubeSign]
  | @insert p S hpS ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p S)
      have hS : ∀ q ∈ S, q.Prime := fun q hq =>
        hprime q (Finset.mem_insert_of_mem hq)
      rw [primeWheelTruncatedMoebiusKernel_insert S p X hp hpS hS]
      rw [frozenPrimeUniverseMass_insert hpS hp]
      rw [ih X hS, ih (X / p) hS]

/-- The rough-seat correlation can therefore be written directly with the
existing frozen prime universe mass as its reciprocal response field. -/
def primeWheelFrozenRoughSeatCorrelation (S : Finset ℕ) (B : ℕ) : ℤ :=
  ∑ n ∈ roughWheelInterval (RHLean.Arithmetic.primorial S)
      (B / RHLean.Arithmetic.primorial S) B,
    (μ n : ℤ) * frozenPrimeUniverseMass S (B / n)

/-- Exact equality of the new rough-seat coordinate and the pre-existing
frozen-cube coordinate. -/
theorem primeWheelRoughSeatCorrelation_eq_frozen
    (S : Finset ℕ) (B : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    primeWheelRoughSeatCorrelation S B =
      primeWheelFrozenRoughSeatCorrelation S B := by
  unfold primeWheelRoughSeatCorrelation primeWheelFrozenRoughSeatCorrelation
  apply Finset.sum_congr rfl
  intro n _hn
  rw [primeWheelTruncatedMoebiusKernel_eq_frozenPrimeUniverseMass
    S (B / n) hprime]

/-- **Frozen rough-seat Mertens identity.**  For any nontrivial finite prime
wheel, ordinary Mertens is exactly one Möbius/frozen-cube correlation on the
physical rough seats above the common full-wheel anchor. -/
theorem roughMertens_one_eq_primeWheel_frozenRoughSeatCorrelation
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hWne : RHLean.Arithmetic.primorial S ≠ 1) (B : ℕ) :
    roughMertens 1 B = primeWheelFrozenRoughSeatCorrelation S B := by
  rw [roughMertens_one_eq_primeWheel_roughSeatCorrelation S hprime hWne B,
    primeWheelRoughSeatCorrelation_eq_frozen S B hprime]

/-- A version requiring no nontrivial-wheel hypothesis: keep the full positive
rough carrier instead of deleting the region where the complete cube vanishes. -/
def primeWheelFrozenFullRoughSeatCorrelation (S : Finset ℕ) (B : ℕ) : ℤ :=
  ∑ n ∈ roughWheelInterval (RHLean.Arithmetic.primorial S) 0 B,
    (μ n : ℤ) * frozenPrimeUniverseMass S (B / n)

/-- Every finite prime set, including a proper subwheel, gives an exact signed
Mertens correlation.  This is the form that retains a genuine outer Möbius
factor when the wheel is deliberately stopped below the physical square root. -/
theorem roughMertens_one_eq_primeWheel_frozenFullRoughSeatCorrelation
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) (B : ℕ) :
    roughMertens 1 B =
      primeWheelFrozenFullRoughSeatCorrelation S B := by
  rw [roughMertens_one_eq_primeWheel_fullRoughSeatCorrelation S hprime B]
  unfold primeWheelFrozenFullRoughSeatCorrelation
  apply Finset.sum_congr rfl
  intro n _hn
  rw [primeWheelTruncatedMoebiusKernel_eq_frozenPrimeUniverseMass
    S (B / n) hprime]

/-- Named square-endpoint proper-subwheel target.  No condition `Y = R` is
imposed: stopping at `Y < R` preserves composite rough seats and therefore a
nonconstant outer Möbius parity field. -/
def squareRootProperSubwheelFrozenCorrelation (R Y : ℕ) : ℤ :=
  primeWheelFrozenFullRoughSeatCorrelation (primesUpTo Y)
    (squareRootEndpoint R)

/-- The proper-subwheel target is still exactly the square-endpoint Mertens
value for every wheel depth `Y`; depth changes coordinates, not the quantity. -/
theorem squareRootProperSubwheelFrozenCorrelation_eq_roughMertens
    (R Y : ℕ) :
    squareRootProperSubwheelFrozenCorrelation R Y =
      roughMertens 1 (squareRootEndpoint R) := by
  symm
  apply roughMertens_one_eq_primeWheel_frozenFullRoughSeatCorrelation
  intro p hp
  exact prime_of_mem_primesUpTo hp

end RHLean.Proof
