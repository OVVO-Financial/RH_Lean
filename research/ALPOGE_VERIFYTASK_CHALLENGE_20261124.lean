import Mathlib

/-!
# Independent statements for the VerifyTask/native application audit

This challenge imports Mathlib only. It cannot depend on an RH_Lean
geometric certificate or on a native definition of the desired conclusion.
The CM formula is the first conjunct of VerifyTask Core 6, read against
the frozen upstream CMGoodModels/Statement.lean at 7cbf7a0.
The principal-window formula is the literal all-prime-power arithmetic
target of the #1205 handoff. These are propositions, not proofs.
-/

set_option autoImplicit false
noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.VerifyTaskChallenge

def cmJ (L : PeriodPair) : ℂ :=
  1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)

def cmJStatement : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 4 = 3 →
    (∀ z ∈ L.lattice,
      ((1 + Complex.I * ((Real.sqrt (d : ℝ)) : ℂ)) / 2) * z ∈ L.lattice) →
    IsIntegral ℤ (cmJ L)

def literalGz (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / (n : ℝ) - 1)) -
    x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

def principalWindow (K eps₁ : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < eps₁ →
    ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
      ∀ y ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2)),
        literalGz y ≤ C * y ^ (1 / 2 + K * eps)

end RHLean.VerifyTaskChallenge
