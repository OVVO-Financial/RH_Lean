import «research.UNIVERSAL_ENVELOPE_OWNER_FRACTIONAL»

/-! The OAI-backed seed is kept out of the independent core acceptance. -/

noncomputable section
set_option autoImplicit false
open RHLean.Analysis.MertensExponent RHLean.Analysis.OwnerPrefix

example (h : MertensGrowthAtMost (1 / 2 : ℝ)) :
    NativeUniformFractionalOwnerContraction 1 :=
  native_uniform_fractional_owner_one_of_mertens_half h

example :
    (∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ NativeUniformFractionalOwnerContraction c) ↔
      MertensGrowthAtMost (1 / 2 : ℝ) :=
  native_uniform_fractional_owner_iff_mertens_half

example :
    (∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ NativeUniformFractionalOwnerContraction c) ↔
      ∀ ρ : ℂ, NontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) :=
  native_uniform_fractional_owner_iff_criticalZeros

example : NativeOwnerBound 0 ↔
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ NativeUniformFractionalOwnerContraction c :=
  native_owner_zero_iff_uniform_fractional_owner

end
