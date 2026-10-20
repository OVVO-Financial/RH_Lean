import «research.VF_919_NATIVE_SEXTIC_IDEAL_FIBER_20261019»

/-!
# Conjugate split-ideal sextic product

Lean 4.34.1 / current Mathlib native algebraic proof.

For the two conjugate roots r and -1-r above a split rational prime,
the product of the two native sextic residues is the corresponding
rational Eisenstein norm residue raised to the same sextic exponent.

This preserves both ideal-labelled phases while recording the exact
norm invariant that survives their product. It is a structural identity,
not a pointwise cancellation or analytic moment bound.
-/

noncomputable section
namespace RHLean.Analysis

/-- The two conjugate sextic phases have product determined by the
    rational Eisenstein norm. Neither individual phase, nor their sum,
    is determined by this identity. -/
theorem vf919SplitSexticResidue_conj_mul
    (p : ℕ) (r : ZMod p) (hr : r ^ 2 + r + 1 = 0)
    (a b : ℤ) :
    vf919SplitSexticResidue p r a b *
        vf919SplitSexticResidue p (-1 - r) a b =
      (vf919EisensteinCoordNorm a b : ZMod p) ^ ((p - 1) / 6) := by
  unfold vf919SplitSexticResidue
  rw [← mul_pow, vf919SplitIdealResidue_norm p r hr]

#print axioms vf919SplitSexticResidue_conj_mul

end RHLean.Analysis
