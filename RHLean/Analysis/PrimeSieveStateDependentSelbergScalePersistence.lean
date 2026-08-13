import Mathlib
import RHLean.Analysis.NativePNTCubicContractionInequality
import RHLean.Analysis.PrimeSieveStateDependentSelbergPositiveGainClosure

/-!
# Effective persistence for state-dependent Selberg gain

A pointwise positive-gain theorem becomes quantitatively useful only when the
improved slope persists on an entire tail at a controlled physical scale.
This module isolates that deterministic step.

The cutoff is held fixed through a finite cubic contraction chain.  Therefore
an arithmetic proof of positive gain above one target-dependent cutoff can be
iterated without paying a new globalization intercept at every step.
-/

noncomputable section

namespace RHLean.Analysis

def PrimeSieveStateDependentSelbergTailAbove
    (M : Nat) (alpha : Real) : Prop :=
  2 <= M ∧ 0 < alpha ∧
    forall q : Nat, M <= q ->
      |nativePNTError q| <= alpha * (q : Real)

def PrimeSieveStateDependentSelbergCubicGainAbove
    (M : Nat) (alpha c : Real) : Prop :=
  forall N : Nat, M <= N ->
    ∃ beta : Real,
      0 <= beta ∧ beta < alpha ∧
        PrimeSieveStateDependentSelbergStateHasPowerGain
          c 3 N M alpha beta

theorem primeSieveStateDependentSelberg_cubicGainAbove_step
    (M : Nat) (alpha c : Real)
    (htail : PrimeSieveStateDependentSelbergTailAbove M alpha)
    (hgain : PrimeSieveStateDependentSelbergCubicGainAbove M alpha c)
    (hnext : 0 < alpha - c * alpha ^ 3) :
    PrimeSieveStateDependentSelbergTailAbove
      M (alpha - c * alpha ^ 3) := by
  rcases htail with ⟨hM2, halpha, htail⟩
  refine ⟨hM2, hnext, ?_⟩
  intro N hMN
  rcases hgain N hMN with ⟨beta, hbeta0, hbeta, hpower⟩
  have hN2 : 2 <= N := hM2.trans hMN
  have hM1 : 1 <= M := by omega
  have hadm :
      PrimeSieveStateDependentSelbergAdmissible N M alpha beta :=
    ⟨⟨hN2, hM1, hMN, halpha, htail⟩, hbeta0, hbeta⟩
  exact primeSieveStateDependentSelberg_error_le_power_contraction
    N M alpha beta c 3 hadm hpower

def PrimeSieveStateDependentSelbergCubicGainChainAt
    (M : Nat) (c : Real) (a : Nat -> Real) : Prop :=
  forall n : Nat,
    PrimeSieveStateDependentSelbergCubicGainAbove M (a n) c

theorem primeSieveStateDependentSelberg_cubic_chain_persists
    (M : Nat) (c : Real) (a : Nat -> Real)
    (hpos : forall n : Nat, 0 < a n)
    (hrec : forall n : Nat,
      a (n + 1) = a n - c * (a n) ^ 3)
    (hgain : PrimeSieveStateDependentSelbergCubicGainChainAt M c a)
    (htail0 : PrimeSieveStateDependentSelbergTailAbove M (a 0)) :
    forall n : Nat,
      PrimeSieveStateDependentSelbergTailAbove M (a n) := by
  intro n
  induction n with
  | zero => exact htail0
  | succ n ih =>
      have hnext : 0 < a n - c * (a n) ^ 3 := by
        simpa [hrec n] using hpos (n + 1)
      have hstep := primeSieveStateDependentSelberg_cubicGainAbove_step
        M (a n) c ih (hgain n) hnext
      rw [hrec n]
      exact hstep

theorem primeSieveStateDependentSelberg_tail_le_eta_of_cubic_budget
    (M : Nat) (c eta : Real) (a : Nat -> Real)
    (hc : 0 <= c) (heta : 0 < eta)
    (hpos : forall n : Nat, 0 < a n)
    (hrec : forall n : Nat,
      a (n + 1) = a n - c * (a n) ^ 3)
    (hgain : PrimeSieveStateDependentSelbergCubicGainChainAt M c a)
    (htail0 : PrimeSieveStateDependentSelbergTailAbove M (a 0))
    (n : Nat)
    (hbudget : 1 < 2 * c * (n : Real) * eta ^ 2) :
    forall N : Nat, M <= N ->
      |nativePNTError N| <= eta * (N : Real) := by
  have hrec_le : forall j : Nat,
      a (j + 1) <= a j - c * (a j) ^ 3 := by
    intro j
    rw [hrec j]
  have haeta : a n <= eta :=
    cubic_contraction_inequality_le_eta_of_budget
      a c eta hc heta hpos hrec_le n hbudget
  have htailn :=
    primeSieveStateDependentSelberg_cubic_chain_persists
      M c a hpos hrec hgain htail0 n
  intro N hMN
  have hbound := htailn.2.2 N hMN
  have hN0 : 0 <= (N : Real) := by positivity
  exact hbound.trans (mul_le_mul_of_nonneg_right haeta hN0)

end RHLean.Analysis
