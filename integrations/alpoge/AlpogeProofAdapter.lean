import Main
import Formalism.StatementOC
import RHLean.AlpogeInterface

/-!
# Alpöge ORIGINAL COMPLETE proof + the SAME RH_Lean Mathlib-level interface

This file is compiled ONLY inside the untouched Alpöge/Claude Lean
v4.33.1 / Mathlib 0df444... project, after building original Main.

It IMPORTS the finished ORIGINAL proof (not a mock certificate)
and also imports the EXACT SAME RHLean.AlpogeInterface.lean bytes
that RH_Lean's Lean v4.34.1 project compiles independently.

The equality with Formalism.Gz is proved HERE against the genuine
source definition, not against a hand-transcribed approximation.

None of these declarations has a hypothesis standing in for RH,
a sorry, an axiom, or a substituted geometric/covolume witness.
-/

noncomputable section

namespace RHLean.AlpogeInterface

/-- The actual published Alpöge observable is IDENTICAL to the shared
RH_Lean finite von Mangoldt source at every real x. -/
theorem gz_eq_upstream_Alpoge_Gz (x : ℝ) :
    gz x = Formalism.Gz x := by
  unfold Formalism.Gz
  rw [gz_eq_vonMangoldtWeightedSum]
  rfl

/-- ORIGINAL Alpöge Gz expressed in the true RHLean Chebyshev error
coordinates, inside the very same kernel that imports his finished RH proof.
This is the exact Gz-to-Selberg shared source hook. -/
theorem originalAlpoge_Gz_eq_native_error (x : ℝ) :
    Formalism.Gz x =
      x * (lambdaRecip ⌊x⌋₊ - Real.log x +
        Real.eulerMascheroniConstant) -
        error ⌊x⌋₊ + (x - (⌊x⌋₊ : ℝ)) := by
  rw [← gz_eq_upstream_Alpoge_Gz]
  exact gz_eq_reciprocal_sub_error x

/-- Literal cross-project Riemann Hypothesis theorem. The proof term
is the ORIGINAL upstream rhOfAll, whose dependency tree contains
UpperTheory.FinalTheorems.everyCharacter and all geometric inputs.
No replacement lemma or new conjecture enters the proof. -/
theorem originalAlpoge_proves_RHLean_RH : rhStatement := by
  change RiemannHypothesis
  exact rhOfAll

/-- The ORIGINAL Dirichlet-L right-half nonvanishing theorem, on the
identical shared Mathlib-level statement (GRH right-half boundary). -/
theorem originalAlpoge_proves_RHLean_DirichletHalf :
    dirichletRightHalfStatement := by
  change DirichletLNonvanishingRightOfHalf
  exact LFunction_ne_zero_of_half_lt_re

/-- This makes the concrete theorem composition visible in one
hypothesis-free Lean declaration with the source-identification lemma. -/
theorem originalAlpoge_RH_and_nativeGz :
    rhStatement ∧ ∀ x : ℝ, gz x = Formalism.Gz x := by
  exact ⟨originalAlpoge_proves_RHLean_RH, gz_eq_upstream_Alpoge_Gz⟩

end RHLean.AlpogeInterface
