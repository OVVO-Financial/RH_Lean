import Mathlib

/-!
# RH_Lean / Alpöge shared arithmetic and RH proposition interface

THIS EXACT FILE is compiled in BOTH:
  1. RH_Lean (Lean 4.34.1 / Mathlib d13f23...), and
  2. Alpöge's unmodified source tree (Lean 4.33.1 / Mathlib 0df444...),
     copied verbatim by integrations/alpoge/check_joint_proof.sh.

It contains only Mathlib-level definitions; NO axiom, no assumed RH
proof, and no backported or edited external theorem.

RHLean.Analysis.AlpogeUnifiedNativeBridge proves these expressions
are definitionally the existing native Psi / reciprocal-Lambda sums.
The external AlpogeProofAdapter proves gz = Formalism.Gz, proves
the RH statement from the ORIGINAL upstream rhOfAll, and checks
the exported Dirichlet nonvanishing theorem against the SAME
shared interface.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.AlpogeInterface

/-- EXACT RH_Lean Chebyshev-von-Mangoldt sum, as a Mathlib-only interface. -/
def psi (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, Λ n

/-- EXACT RH_Lean reciprocal von-Mangoldt sum, as a Mathlib-only interface. -/
def lambdaRecip (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, Λ n / (n : ℝ)

/-- RH_Lean's ordinary Chebyshev error in the shared coordinates. -/
def error (N : ℕ) : ℝ :=
  psi N - (N : ℝ)

/-- Same all-real Gz observable used by Alpöge (native sum representation). -/
def gz (x : ℝ) : ℝ :=
  x * lambdaRecip ⌊x⌋₊ - psi ⌊x⌋₊ -
    x * Real.log x +
    (1 + Real.eulerMascheroniConstant) * x

/-- The EXACT Mathlib proposition of RH_Lean/Proof/RiemannHypothesisBridge. -/
def rhStatement : Prop := RiemannHypothesis

/-- The exact additional right-half Dirichlet L-function nonvanishing
statement exported by Alpöge, using native Mathlib DirichletCharacter. -/
def dirichletRightHalfStatement : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0

/-- Source-faithful finite sum expansion for the same Gz at EVERY real x.
This lemma is independent of RH and of any geometric witness. -/
theorem gz_eq_vonMangoldtWeightedSum (x : ℝ) :
    gz x =
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        Λ n * (x / (n : ℝ) - 1)) -
      x * Real.log x +
      (1 + Real.eulerMascheroniConstant) * x := by
  have hsource :
      x * lambdaRecip ⌊x⌋₊ - psi ⌊x⌋₊ =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          Λ n * (x / (n : ℝ) - 1) := by
    unfold lambdaRecip psi
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  unfold gz
  rw [hsource]


/-- Exact all-real Gz/prime-error link, with the original scalar
x - floor(x) term present. This is proved in the SAME shared Mathlib
source that gets compiled in BOTH Lean environments. -/
theorem gz_eq_reciprocal_sub_error (x : ℝ) :
    gz x =
      x * (lambdaRecip ⌊x⌋₊ - Real.log x +
        Real.eulerMascheroniConstant) -
        error ⌊x⌋₊ + (x - (⌊x⌋₊ : ℝ)) := by
  unfold gz error
  ring


end RHLean.AlpogeInterface
