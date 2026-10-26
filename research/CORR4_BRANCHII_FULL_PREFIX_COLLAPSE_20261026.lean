import Mathlib
import «research.CORR4_BRANCHII_OWNER_ANTI_CIRCULAR_20261026»
import «research.CORR4_DECODER_FINITE_PREFIX_20261026»

/-!
# CORR-4: full Branch-II finite decoder returns actual Mertens

At all physical cutoffs Y >= 6*r the low-owner six-point
Euler collar has zero *summatory* contribution. Thus the complete
quotient decoder applied to the high-Mobius-owner Branch II returns
the genuine rational Mobius prefix exactly. Restricting to u<L
introduces a nonzero high-u boundary, and this theorem does not
bound the remaining low-u summand.

No Mertens power bound, RH hypothesis or prime-distribution
estimate is used.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

theorem corr4_delta_prefix (f : ArithmeticFunction ℂ) (k Y : ℕ)
    (hk : 0 < k) :
    (∑ n ∈ Finset.Icc 1 Y, (vf919DirichletDelta k * f) n) =
      ∑ m ∈ Finset.Icc 1 (Y / k), f m := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 Y,
          if k ∣ n then f (n / k) else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            exact vf919DirichletDelta_mul_apply k hk f n
    _ = _ := corr4_scaled_prefix_reindex f k Y hk

/-- Finite prefix of a cutoff-supported function is independent of
every enlarged end point. This is used for all four Euler collars. -/
theorem corr4_low_owner_prefix_stabilizes (r Y : ℕ) (hYr : r ≤ Y) :
    (∑ a ∈ Finset.Icc 1 Y, corr4Mu6Low r a) =
      ∑ a ∈ Finset.Icc 1 r, corr4Mu6Low r a := by
  have hsub : Finset.Icc 1 r ⊆ Finset.Icc 1 Y := by
    intro a ha
    obtain ⟨ha1,har⟩ := Finset.mem_Icc.mp ha
    exact Finset.mem_Icc.mpr ⟨ha1, har.trans hYr⟩
  symm
  apply Finset.sum_subset hsub
  intro a ha haNot
  have hgt : r < a := by
    have hpos := (Finset.mem_Icc.mp ha).1
    by_contra hb
    have hle : a ≤ r := Nat.le_of_not_gt hb
    exact haNot (Finset.mem_Icc.mpr ⟨hpos,hle⟩)
  change (if a ≤ r then corr4Mu6 a else 0) = 0
  simp [Nat.not_le.mpr hgt]

theorem corr4_low_owner_six_collar_prefix_zero
    (r Y : ℕ) (hgate : 6 * r ≤ Y) :
    (∑ n ∈ Finset.Icc 1 Y,
      (corr4Mu6Low r *
        (1 - vf919DirichletDelta 2 -
          vf919DirichletDelta 3 + vf919DirichletDelta 6)) n) = 0 := by
  let f := corr4Mu6Low r
  have hc :
      f * (1 - vf919DirichletDelta 2 -
        vf919DirichletDelta 3 + vf919DirichletDelta 6) =
      f - vf919DirichletDelta 2 * f -
        vf919DirichletDelta 3 * f +
        vf919DirichletDelta 6 * f := by ring
  have hY : r ≤ Y := by omega
  have h2 : r ≤ Y / 2 := by omega
  have h3 : r ≤ Y / 3 := by omega
  have h6 : r ≤ Y / 6 := by omega
  change (∑ n ∈ Finset.Icc 1 Y,
    (f * (1 - vf919DirichletDelta 2 -
      vf919DirichletDelta 3 + vf919DirichletDelta 6)) n) = 0
  rw [hc]
  simp only [vf919ArithmeticFunction_sub_apply, ArithmeticFunction.add_apply]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  rw [corr4_delta_prefix f 2 Y (by decide),
    corr4_delta_prefix f 3 Y (by decide),
    corr4_delta_prefix f 6 Y (by decide)]
  rw [corr4_low_owner_prefix_stabilizes r Y hY,
    corr4_low_owner_prefix_stabilizes r (Y / 2) h2,
    corr4_low_owner_prefix_stabilizes r (Y / 3) h3,
    corr4_low_owner_prefix_stabilizes r (Y / 6) h6]
  ring

/-- Complete Branch II decoder: its signed prefix equals the ACTUAL
rational Mobius summatory function. A truncated low-u range is not
claimed to equal M(Y) without its complementary upper-u tail. -/
theorem corr4_complete_branchII_equals_mobius_prefix
    (r Y : ℕ) (hgate : 6 * r ≤ Y) :
    (∑ n ∈ Finset.Icc 1 Y,
      (corr4DecoderEuler * (corr4Mu6High r * corr4B6)) n) =
    ∑ n ∈ Finset.Icc 1 Y, vf919RationalMobius n := by
  have hfull := corr4_decoder_high_owner_eq_mobius_sub_six_collar r
  have hzero := corr4_low_owner_six_collar_prefix_zero r Y hgate
  rw [hfull]
  simp only [vf919ArithmeticFunction_sub_apply]
  rw [Finset.sum_sub_distrib, hzero, sub_zero]

#print axioms corr4_delta_prefix
#print axioms corr4_low_owner_prefix_stabilizes
#print axioms corr4_low_owner_six_collar_prefix_zero
#print axioms corr4_complete_branchII_equals_mobius_prefix

end RHLean.Analysis
