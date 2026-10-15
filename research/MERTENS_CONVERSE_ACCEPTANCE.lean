import «research.MERTENS_CONVERSE_RECIPROCAL»

/-! Exact signatures and kernel dependencies for the converse development. -/

open RHLean.Analysis RHLean.Analysis.MertensExponent

example {a : ℝ} (ha : 0 ≤ a) (h : ZerosInSymmetricStrip a) :
    DifferentiableOn ℂ nativeInvZetaRegularized (exponentHalfPlane a) :=
  regularizedReciprocal_holomorphic_of_strip ha h

#print axioms RHLean.Analysis.MertensExponent.zeta_ne_zero_of_strip
#print axioms RHLean.Analysis.MertensExponent.regularizedReciprocal_differentiableAt_off_pole
#print axioms RHLean.Analysis.MertensExponent.regularizedReciprocal_differentiableAt_of_strip
#print axioms RHLean.Analysis.MertensExponent.regularizedReciprocal_holomorphic_of_strip
#print axioms RHLean.Analysis.MertensExponent.regularizedReciprocal_eq_mellin_classical
