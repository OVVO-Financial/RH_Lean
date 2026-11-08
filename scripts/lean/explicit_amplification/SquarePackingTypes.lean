import «research.oai_434.VF919ExplicitSquareBlockPacking»

set_option autoImplicit false

/-! Exact quantified statements for the square-block signed partition
and the strengthened *actual* fixed-source analytic and Mertens bounds. -/

example : ∀ (f : ℕ → ℤ) (a b : ℕ) (_hab : a ≤ b),
    (∑ n ∈ Finset.Ico (a ^ 2) (b ^ 2), f n) =
      ∑ r ∈ Finset.Ico a b,
        ∑ n ∈ Finset.Ico (r ^ 2) ((r + 1) ^ 2), f n :=
  @RHLean.Proof.groupedSquareBlocks_sum

example :
    OAI.SevenEighths.HeckeZeroSupremum.beta ≤
    ((7 / 8 : ℝ) -
      1 / (32 * (OAI.SevenEighths.Parameters.nearUniformSlotCount : ℝ))) :=
  OAI.SevenEighths.RHLeanNearUniformSlotPacking.native_beta_le_near_uniform_slots

example :
    RHLean.Analysis.MertensExponent.MertensGrowthAtMost
      ((7 / 8 : ℝ) -
        1 / (32 * (OAI.SevenEighths.Parameters.nearUniformSlotCount : ℝ))) :=
  RHLean.Analysis.native_mertens_near_uniform_slots
