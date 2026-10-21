import «research.VF_919_NATIVE_SEXTIC_IDEAL_FIBER_20261019»

/-!
# Exact complete-residue sextic trace moments

This file formalizes the finite phase-bucket calculation in claim
`20261020-coordinator-1`.

For one split selected prime, a complete unit residue carrier gives two
independent exponents in `Fin 6`. The conjugate trace values are
`2, 1, -1, -2, -1, 1`; the complete four-label trace is the sum of two
such values. The resulting distribution and its second and fourth moments
are exact finite identities.

These theorems do not assert that the weighted physical detector source is
uniform in these buckets. They omit the nonunit zero branches, principal
row, ramified prime, decorations, and exceptional rows, and therefore supply
no analytic moment estimate or seven-eighths conclusion.
-/

namespace RHLean.Analysis

set_option maxRecDepth 100000

/-- The real integral trace of a sixth root and its inverse, indexed by its
    exponent modulo six. -/
def vf919CompleteResidueTau : Fin 6 → ℤ :=
  ![2, 1, -1, -2, -1, 1]

/-- The complete four-label trace attached to two independent sixth-root
    exponents. -/
def vf919CompleteResidueTrace (e f : Fin 6) : ℤ :=
  vf919CompleteResidueTau e + vf919CompleteResidueTau f

/-- Exact multiplicities of the trace values `-4, -3, ..., 4` on the 36
    complete phase buckets. -/
theorem vf919CompleteResidueTrace_distribution :
    ((Finset.univ.filter fun ef : Fin 6 × Fin 6 =>
        vf919CompleteResidueTrace ef.1 ef.2 = -4).card = 1) ∧
    ((Finset.univ.filter fun ef : Fin 6 × Fin 6 =>
        vf919CompleteResidueTrace ef.1 ef.2 = -3).card = 4) ∧
    ((Finset.univ.filter fun ef : Fin 6 × Fin 6 =>
        vf919CompleteResidueTrace ef.1 ef.2 = -2).card = 4) ∧
    ((Finset.univ.filter fun ef : Fin 6 × Fin 6 =>
        vf919CompleteResidueTrace ef.1 ef.2 = -1).card = 4) ∧
    ((Finset.univ.filter fun ef : Fin 6 × Fin 6 =>
        vf919CompleteResidueTrace ef.1 ef.2 = 0).card = 10) ∧
    ((Finset.univ.filter fun ef : Fin 6 × Fin 6 =>
        vf919CompleteResidueTrace ef.1 ef.2 = 1).card = 4) ∧
    ((Finset.univ.filter fun ef : Fin 6 × Fin 6 =>
        vf919CompleteResidueTrace ef.1 ef.2 = 2).card = 4) ∧
    ((Finset.univ.filter fun ef : Fin 6 × Fin 6 =>
        vf919CompleteResidueTrace ef.1 ef.2 = 3).card = 4) ∧
    ((Finset.univ.filter fun ef : Fin 6 × Fin 6 =>
        vf919CompleteResidueTrace ef.1 ef.2 = 4).card = 1) := by
  decide

/-- The exact unnormalized second moment on the 36 complete phase buckets.
    Equivalently, the uniform average is `144 / 36 = 4`. -/
theorem vf919CompleteResidueTrace_secondMoment :
    ∑ ef : Fin 6 × Fin 6, vf919CompleteResidueTrace ef.1 ef.2 ^ 2 = 144 := by
  decide

/-- The exact unnormalized fourth moment on the 36 complete phase buckets.
    Equivalently, the uniform average is `1296 / 36 = 36`. -/
theorem vf919CompleteResidueTrace_fourthMoment :
    ∑ ef : Fin 6 × Fin 6, vf919CompleteResidueTrace ef.1 ef.2 ^ 4 = 1296 := by
  decide

#print axioms vf919CompleteResidueTrace_distribution
#print axioms vf919CompleteResidueTrace_secondMoment
#print axioms vf919CompleteResidueTrace_fourthMoment

end RHLean.Analysis
