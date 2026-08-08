import Mathlib
import RHLean.Analysis.SquareWheelQuantitativeBridge

/-!
# Möbius synthesis boundary contract

This module gives the synthesis endpoint a single canonical quantitative
interface.  Pull requests are not credited for introducing another exact
representation of the nonzero response.  They advance the analytic frontier
only by proving a stronger instance of the pointwise power-bound predicate
below, or by proving the full RH-scale predicate.

The underlying response is the already isolated nonzero square-wheel response
`H_{k,n}` represented by `squareWheelNonzeroSampleResponse`.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

namespace MobiusSynthesisBoundary

/-- A uniform pointwise power bound for the canonical nonzero response on every
complete square sample in every synchronized primorial block from `k >= 2`.

A theorem of this type is a quantitative statement about the existing boundary
object itself; changing coordinates or proving an equivalent decomposition does
not inhabit this predicate unless it also yields the stated bound. -/
def NonzeroResponsePowerBound (r : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (k n : ℕ),
      2 ≤ k →
      primorialBlockLower k < squarePrefixEndpoint n →
      squarePrefixEndpoint n ≤ primorialBlockUpper k →
      ‖squareWheelNonzeroSampleResponse (primorialMinimalWheelSystem k) n‖ ≤
        K * Real.rpow ((squarePrefixEndpoint n + 1 : ℕ) : ℝ) r

/-- The exact synthesis target: for every positive epsilon, the canonical
nonzero response has a pointwise bound at exponent `1/2 + epsilon`, uniformly
on the synchronized complete-square samples. -/
def NonzeroResponseRHScale : Prop :=
  ∀ ε : ℝ, 0 < ε →
    NonzeroResponsePowerBound ((1 : ℝ) / 2 + ε)

end MobiusSynthesisBoundary

end RHLean.Analysis
