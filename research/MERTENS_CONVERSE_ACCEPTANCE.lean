import «research.MERTENS_CONVERSE_RECIPROCAL»
import «research.MERTENS_CONVERSE_THREE_CIRCLES»
import «research.MERTENS_CONVERSE_ZETA_BOUNDS»

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
#print axioms RHLean.Analysis.MertensExponent.threeCircle_power_bound
#print axioms RHLean.Analysis.MertensExponent.threeCircle_exponent_mem_Ioo
#print axioms RHLean.Analysis.MertensExponent.zeta_bounded_right_halfPlane
#print axioms RHLean.Analysis.MertensExponent.zeta_norm_le_positive_strip
#print axioms RHLean.Analysis.MertensExponent.zetaDiscPoint_ne_one
#print axioms RHLean.Analysis.MertensExponent.zeta_norm_le_on_shifted_disk
