import Mathlib
import RHLean.Proof.SquareRootLowPrimeNoLibertyFiniteEquiv
import RHLean.Proof.SquareRootLowPrimeHorizontalTerminalCoverage

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Shallow processed cofactors: all of their visible prime support is at or
below the packet depth. -/
def SquareRootLowPrimeProcessedStateShallow
    (K : ℕ) (x : SquareRootLowPrimeProcessedState) : Prop :=
  canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) ≤ K

/-- Deep processed cofactors: at least one canonical prime coordinate lies
strictly above the packet depth. -/
def SquareRootLowPrimeProcessedStateDeep
    (K : ℕ) (x : SquareRootLowPrimeProcessedState) : Prop :=
  K < canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x)

instance (K : ℕ) (x : SquareRootLowPrimeProcessedState) :
    Decidable (SquareRootLowPrimeProcessedStateShallow K x) := by
  unfold SquareRootLowPrimeProcessedStateShallow
  infer_instance

instance (K : ℕ) (x : SquareRootLowPrimeProcessedState) :
    Decidable (SquareRootLowPrimeProcessedStateDeep K x) := by
  unfold SquareRootLowPrimeProcessedStateDeep
  infer_instance

/-- The shallow/deep split is exhaustive and disjoint. -/
theorem squareRootLowPrimeProcessedState_shallow_or_deep
    (K : ℕ) (x : SquareRootLowPrimeProcessedState) :
    SquareRootLowPrimeProcessedStateShallow K x ∨
      SquareRootLowPrimeProcessedStateDeep K x := by
  unfold SquareRootLowPrimeProcessedStateShallow
    SquareRootLowPrimeProcessedStateDeep
  omega

/-- Strip every prime coordinate above `K`. On the squarefree processed
carrier this is exactly the shallow prime factor of `c`; the gcd presentation
makes fresh-prime invariance elementary. -/
def squareRootLowPrimeShallowBase (K c : ℕ) : ℕ :=
  Nat.gcd c K.factorial

/-- Raw seat coordinate. Prime-toggle edges alter only the cofactor and leave
this coordinate literally unchanged. -/
def squareRootLowPrimeProcessedSeatIndex :
    SquareRootLowPrimeProcessedState → ℕ
  | none => 0
  | some z => z.2

/-- Canonical component key: shallow arithmetic base together with the literal
seat coordinate. -/
def squareRootLowPrimeProcessedSeatStructuralKey
    (K : ℕ) (x : SquareRootLowPrimeProcessedState) : ℕ × ℕ :=
  (squareRootLowPrimeShallowBase K
      (squareRootLowPrimeProcessedStateCofactor x),
    squareRootLowPrimeProcessedSeatIndex x)

/-- Adjoining one prime strictly above `K` does not change the shallow base. -/
theorem squareRootLowPrimeShallowBase_mul_fresh_prime
    {K c p : ℕ} (hp : p.Prime) (hKp : K < p) :
    squareRootLowPrimeShallowBase K (p * c) =
      squareRootLowPrimeShallowBase K c := by
  unfold squareRootLowPrimeShallowBase
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have hdivMul : Nat.gcd (p * c) K.factorial ∣ p * c :=
        Nat.gcd_dvd_left _ _
      have hpCoprimeFact : p.Coprime K.factorial :=
        hp.coprime_factorial_of_lt hKp
      have hpCoprimeGcd : p.Coprime (Nat.gcd (p * c) K.factorial) :=
        hpCoprimeFact.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      exact hpCoprimeGcd.symm.dvd_of_dvd_mul_left hdivMul
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · exact (Nat.gcd_dvd_left c K.factorial).trans
        (Nat.dvd_mul_left c p)
    · exact Nat.gcd_dvd_right _ _

/-- Every fresh processed prime edge preserves the complete structural key. -/
theorem squareRootLowPrimeProcessedSeatStructuralKey_extend
    {K p : ℕ} (hp : p.Prime) (hKp : K < p)
    (x : SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatStructuralKey K
        (squareRootLowPrimeProcessedSeatExtend p x) =
      squareRootLowPrimeProcessedSeatStructuralKey K x := by
  rcases x with _ | z
  · rfl
  · simp only [squareRootLowPrimeProcessedSeatStructuralKey,
      squareRootLowPrimeProcessedStateCofactor,
      squareRootLowPrimeProcessedSeatExtend,
      squareRootLowPrimeProcessedSeatIndex]
    rw [squareRootLowPrimeShallowBase_mul_fresh_prime hp hKp]

end RHLean.Proof
