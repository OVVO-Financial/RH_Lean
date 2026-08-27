import Mathlib
import RHLean.Proof.CanonicalGapAncestryBridge

/-!
# Directional Euler chains for fresh-prime Mobius dynamics

A genuine forward Euler move adjoins one fresh prime which strictly dominates
every prime divisor already present in the cofactor.  The new prime is therefore
the canonical largest prime of the child, the Mobius sign reverses exactly, and
the child determines both its owner prime and its parent uniquely.

Consequently successive genuine Euler moves have strictly increasing owner
primes.  Reversing such a chain strips canonical largest primes in strictly
decreasing order.  This is the arithmetic orientation needed to turn the
processed-seat displacement recursion into a finite rooted ancestry chain.

No analytic estimate, norm, or asymptotic input is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open CanonicalGapAncestryBridge
open CanonicalGapAncestryFlow

/-- Arithmetic data for one genuine forward Euler move `c -> c*p`. -/
structure SquareRootLowPrimeEulerStepData (c p n : ℕ) : Prop where
  source : CanonicalSourceData p c
  child_eq : n = c * p

/-- Canonical source data is exactly the largest-prime orientation needed by a
forward Euler move. -/
theorem squareRootLowPrimeEulerStep_coreMaxPrime
    {c p n : ℕ} (h : SquareRootLowPrimeEulerStepData c p n) :
    CoreMaxPrime p c := by
  exact ⟨h.source.1, h.source.2.2.2.1,
    fun r hr hrc => h.source.2.2.2.2 r hr hrc⟩

/-- A genuine fresh-prime child is owned by the prime just adjoined. -/
theorem squareRootLowPrimeEulerStep_canonicalLargestPrimeFactor
    {c p n : ℕ} (h : SquareRootLowPrimeEulerStepData c p n) :
    canonicalLargestPrimeFactor n = p := by
  have hp : p.Prime := h.source.1
  have hcpos : 1 ≤ c := h.source.2.1
  have hnpos : 0 < n := by
    rw [h.child_eq]
    positivity
  have hple : p ≤ n := by
    rw [h.child_eq]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right p hcpos
  have hcle : c ≤ n := by
    rw [h.child_eq]
    exact Nat.le_mul_of_pos_right c hp.pos
  let s : SourceIndex n :=
    (⟨p, by omega⟩, ⟨c, by omega⟩)
  have hs : SourceAdmissible s := by
    change CanonicalSourceData p c
    exact h.source
  have howner := sourcePrime_eq_canonicalLargestPrimeFactor s hs
  have howner' : p = canonicalLargestPrimeFactor (p * c) := by
    simpa [s, sourcePrime, sourceProduct, sourceCore] using howner
  simpa [h.child_eq, Nat.mul_comm] using howner'.symm

/-- Stripping the canonical largest prime of a fresh child recovers the unique
parent cofactor. -/
theorem squareRootLowPrimeEulerStep_canonicalCofactor
    {c p n : ℕ} (h : SquareRootLowPrimeEulerStepData c p n) :
    canonicalCofactor n = c := by
  have hp : p.Prime := h.source.1
  have hcpos : 1 ≤ c := h.source.2.1
  have hnpos : 0 < n := by
    rw [h.child_eq]
    positivity
  have hple : p ≤ n := by
    rw [h.child_eq]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right p hcpos
  have hcle : c ≤ n := by
    rw [h.child_eq]
    exact Nat.le_mul_of_pos_right c hp.pos
  let s : SourceIndex n :=
    (⟨p, by omega⟩, ⟨c, by omega⟩)
  have hs : SourceAdmissible s := by
    change CanonicalSourceData p c
    exact h.source
  have hcore := sourceCore_eq_canonicalCofactor s hs
  have hcore' : c = canonicalCofactor (p * c) := by
    simpa [s, sourcePrime, sourceProduct, sourceCore] using hcore
  simpa [h.child_eq, Nat.mul_comm] using hcore'.symm

/-- Exact Mobius sign reversal along one genuine forward Euler edge. -/
theorem squareRootLowPrimeEulerStep_moebius
    {c p n : ℕ} (h : SquareRootLowPrimeEulerStepData c p n) :
    (μ n : ℤ) = -(μ c : ℤ) := by
  rw [h.child_eq]
  have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    h.source.2.2.2.1.symm
  rw [hmul, ArithmeticFunction.moebius_apply_prime h.source.1]
  ring

/-- The child determines its fresh owner prime and its parent uniquely. -/
theorem squareRootLowPrimeEulerStep_unique
    {c c' p p' n : ℕ}
    (h : SquareRootLowPrimeEulerStepData c p n)
    (h' : SquareRootLowPrimeEulerStepData c' p' n) :
    c = c' ∧ p = p' := by
  have hprod : c * p = c' * p' := by
    rw [← h.child_eq, ← h'.child_eq]
  have hp : p = p' :=
    coreMaxPrime_unique_factor
      (squareRootLowPrimeEulerStep_coreMaxPrime h)
      (squareRootLowPrimeEulerStep_coreMaxPrime h') hprod
  subst p'
  have hc : c = c' :=
    Nat.mul_right_cancel h.source.1.pos hprod
  exact ⟨hc, rfl⟩

/-- Successive genuine Euler moves have strictly increasing owner primes. -/
theorem squareRootLowPrimeEulerStep_owner_strictMono
    {c p n q m : ℕ}
    (h₁ : SquareRootLowPrimeEulerStepData c p n)
    (h₂ : SquareRootLowPrimeEulerStepData n q m) :
    p < q := by
  have hpDiv : p ∣ n := by
    rw [h₁.child_eq]
    exact ⟨c, by simp [Nat.mul_comm]⟩
  exact h₂.source.2.2.2.2 p h₁.source.1 hpDiv

/-- Hence a two-step forward Euler path cannot return to its starting owner
coordinate. -/
theorem squareRootLowPrimeEulerStep_no_owner_backtrack
    {c p n q m : ℕ}
    (h₁ : SquareRootLowPrimeEulerStepData c p n)
    (h₂ : SquareRootLowPrimeEulerStepData n q m) :
    q ≠ p := by
  exact ne_of_gt (squareRootLowPrimeEulerStep_owner_strictMono h₁ h₂)

/-- Two successive genuine Euler moves restore the original Mobius sign. -/
theorem squareRootLowPrimeEulerStep_twoStep_moebius
    {c p n q m : ℕ}
    (h₁ : SquareRootLowPrimeEulerStepData c p n)
    (h₂ : SquareRootLowPrimeEulerStepData n q m) :
    (μ m : ℤ) = μ c := by
  rw [squareRootLowPrimeEulerStep_moebius h₂,
    squareRootLowPrimeEulerStep_moebius h₁]
  ring

end RHLean.Proof
