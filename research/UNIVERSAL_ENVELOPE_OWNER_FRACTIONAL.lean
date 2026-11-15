import «research.UNIVERSAL_ENVELOPE_OWNER_EQUIVALENCE»
import «research.oai_434.VF919FractionalOwnerContraction»

/-!
# The quantified native fractional-owner target

The critical native-owner equivalence is independent of a numerical Mertens
seed.  The existing fractional-owner definition, however, only quantifies over
current exponents between 1/2 and 7/8.  Its existing forward consumer uses the
certified source to supply an exponent in that range.  Keep that dependency
in this separate module rather than importing it into the core equivalence.

The new reverse direction uses the original complete signed owner identity,
as proved in `UNIVERSAL_ENVELOPE_OWNER_EQUIVALENCE`.  Matching affine exponent
maps alone is not taken to establish any source-level reverse implication.
-/

noncomputable section

namespace RHLean.Analysis.OwnerPrefix

open RHLean.Analysis.MertensExponent

/-- Once the critical Mertens statement is supplied, the choice c=1 renews
the same zero-loss source bound at every current exponent. -/
theorem native_uniform_fractional_owner_one_of_mertens_half
    (hgrowth : MertensGrowthAtMost (1 / 2 : ℝ)) :
    NativeUniformFractionalOwnerContraction 1 := by
  intro _θ _hθ0 _hθ1 _hθ
  simpa only [sub_self, zero_mul] using
    native_owner_zero_of_mertens_half hgrowth

/-- The quantified, uniformly renewable native-source contraction is
RH-strength in both directions.  The forward direction retains the existing
source-based seed in the permitted interval [1/2,7/8]. -/
theorem native_uniform_fractional_owner_iff_mertens_half :
    (∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ NativeUniformFractionalOwnerContraction c) ↔
      MertensGrowthAtMost (1 / 2 : ℝ) := by
  constructor
  · rintro ⟨c, hc0, hc1, hcontract⟩
    exact native_fractional_owner_contraction_implies_mertens_half
      c hc0 hc1 hcontract
  · intro hgrowth
    exact ⟨1, by norm_num, by norm_num,
      native_uniform_fractional_owner_one_of_mertens_half hgrowth⟩

/-- The same quantified source-level equivalence in the zero coordinate. -/
theorem native_uniform_fractional_owner_iff_criticalZeros :
    (∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ NativeUniformFractionalOwnerContraction c) ↔
      ∀ ρ : ℂ, NontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) :=
  native_uniform_fractional_owner_iff_mertens_half.trans
    growthAtMost_half_iff_criticalZeros

/-- Zero owner loss and existence of a positive renewable fractional owner
contraction belong to one logical target class.  Their proof mechanisms may
still be investigated separately. -/
theorem native_owner_zero_iff_uniform_fractional_owner :
    NativeOwnerBound 0 ↔
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ NativeUniformFractionalOwnerContraction c :=
  native_owner_zero_iff_mertens_half.trans
    native_uniform_fractional_owner_iff_mertens_half.symm

end RHLean.Analysis.OwnerPrefix

end
