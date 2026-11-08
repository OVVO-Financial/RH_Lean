import RHLean.Proof.RootSmoothCrossRegionGram

/-!
# Complete 2ab reciprocal-parent packets: exact signed band telescope

At X_R = R^2 - 1, t_R(z) is the actual complementary Mobius mass on
(X_R/(z+1), X_R/z].  The exact replacement-fibre dictionary supplies each
parent with EVERY quotient descendant M(floor(z/k)), k = 1,...,z.

Mobius renewal makes the fully completed parent exactly t_R(z).  Therefore
a contiguous, COMPLETED parent band is a difference of two ACTUAL lower-scale
Mertens values.  No triangle inequality, new source assumption, or desired
Mertens estimate is introduced.

The root-adjacent half of the quotient kernel is literally diagonal.  This
does not make its UNCOMPLETED diagonal small, but identifies the actual
small reciprocal intervals and their complete strict descendants.

These identities are not an RH proof and cannot discard the complementary
long-fibre band z < A.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis

/-- Keep the true complementary Mobius parent and ALL its quotient descendants
in one signed packet, before taking any norm. -/
def twoABCompleteReciprocalPacket (R z : ℕ) : ℂ :=
  squareRootReplacementTailMoebiusCoefficient R z *
    ∑ k ∈ Finset.Icc 1 z, mertensSummatory (z / k)

/-- Every fully admitted packet collapses by the ordinary Mobius unit renewal.
This is NOT a bound on the isolated parent or its diagonal term. -/
theorem twoABCompleteReciprocalPacket_eq_parent
    (R z : ℕ) (hz : 1 ≤ z) :
    twoABCompleteReciprocalPacket R z =
      squareRootReplacementTailMoebiusCoefficient R z := by
  unfold twoABCompleteReciprocalPacket
  rw [RHLean.Analysis.sum_mertensSummatory_div_eq_one hz]
  ring

/-- A contiguous set of complete reciprocal packets; a and b are parent
labels, not physical-prime owner cutoffs. -/
def twoABCompleteReciprocalBand (R a b : ℕ) : ℂ :=
  ∑ z ∈ Finset.Icc a b, twoABCompleteReciprocalPacket R z

private theorem twoAB_sum_Icc_forward_difference (f : ℕ → ℂ)
    (a b : ℕ) (hab : a ≤ b) :
    (∑ z ∈ Finset.Icc a b, (f z - f (z + 1))) =
      f a - f (b + 1) := by
  induction b, hab using Nat.le_induction with
  | base =>
      simp
  | succ b hab ih =>
      rw [Finset.sum_Icc_succ_top (by omega : a ≤ b + 1), ih]
      ring

/-- MAIN FINITE THEOREM: with ALL descendants kept, the entire band is exactly
the difference of two historical Mertens values.  Every occurrence is genuine;
there is no independent signed cancellation requirement on this completed
band. -/
theorem twoABCompleteReciprocalBand_eq_mertensDifference
    (R a b : ℕ) (hR : 2 ≤ R) (ha : 1 ≤ a)
    (hab : a ≤ b) (hbR : b < R) :
    twoABCompleteReciprocalBand R a b =
      mertensSummatory (squareRootEndpoint R / a) -
        mertensSummatory (squareRootEndpoint R / (b + 1)) := by
  unfold twoABCompleteReciprocalBand
  calc
    (∑ z ∈ Finset.Icc a b, twoABCompleteReciprocalPacket R z) =
        ∑ z ∈ Finset.Icc a b,
          squareRootReplacementTailMoebiusCoefficient R z := by
            apply Finset.sum_congr rfl
            intro z hz
            exact twoABCompleteReciprocalPacket_eq_parent R z
              (le_trans ha (Finset.mem_Icc.mp hz).1)
    _ = ∑ z ∈ Finset.Icc a b,
          (mertensSummatory (squareRootEndpoint R / z) -
            mertensSummatory (squareRootEndpoint R / (z + 1))) := by
            apply Finset.sum_congr rfl
            intro z hz
            have hzl : 1 ≤ z := le_trans ha (Finset.mem_Icc.mp hz).1
            have hzu : z < R :=
              lt_of_le_of_lt (Finset.mem_Icc.mp hz).2 hbR
            exact squareRootReplacementTailMoebiusCoefficient_eq_mertensIncrement
              R z hR hzl hzu
    _ = mertensSummatory (squareRootEndpoint R / a) -
          mertensSummatory (squareRootEndpoint R / (b + 1)) :=
            twoAB_sum_Icc_forward_difference
              (fun z => mertensSummatory (squareRootEndpoint R / z))
              a b hab

/-- The immediately reusable numerical bound.  A stronger bound on the COMPLETE
band comes from an existing Mertens theorem, not from bounding parent and
descendant energies individually. -/
theorem twoABCompleteReciprocalBand_norm_le_endpoints
    (R a b : ℕ) (hR : 2 ≤ R) (ha : 1 ≤ a)
    (hab : a ≤ b) (hbR : b < R) :
    ‖twoABCompleteReciprocalBand R a b‖ ≤
      ‖mertensSummatory (squareRootEndpoint R / a)‖ +
        ‖mertensSummatory (squareRootEndpoint R / (b + 1))‖ := by
  rw [twoABCompleteReciprocalBand_eq_mertensDifference R a b hR ha hab hbR]
  exact norm_sub_le _ _

/-- For 1 <= y < z < 2*y, no quotient of z by a positive integer is y.
Thus the strict-descendant coupling is absent in the root-adjacent upper half. -/
theorem twoAB_quotientKernel_zero_strict_nearRoot
    {z y : ℕ} (_hy : 1 ≤ y) (hyz : y < z) (hz2 : z < 2 * y) :
    squareRootReplacementQuotientKernel z y = 0 := by
  classical
  unfold squareRootReplacementQuotientKernel
  apply Finset.sum_eq_zero
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  by_cases hkEq : k = 1
  · subst k
    have hne : z ≠ y := by omega
    simp [hne]
  · have hk2 : 2 ≤ k := by omega
    have hmul : 2 * y ≤ y * k := by
      calc
        2 * y = y * 2 := by omega
        _ ≤ y * k := Nat.mul_le_mul_left y hk2
    have hzlt : z < y * k := lt_of_lt_of_le hz2 hmul
    have hq : z / k < y :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).2 hzlt
    have hne : z / k ≠ y := Nat.ne_of_lt hq
    simp [hne]

/-- Exact diagonal (not contraction) of the quotient kernel on its upper
root-adjacent half. -/
theorem twoAB_quotientKernel_diagonal_upperHalf
    (R z y : ℕ) (hzR : z < R) (hy : 1 ≤ y)
    (hhalf : R ≤ 2 * y) :
    squareRootReplacementQuotientKernel z y =
      if z = y then 1 else 0 := by
  by_cases hzlt : z < y
  · rw [squareRootReplacementQuotientKernel_eq_zero_of_lt hzlt]
    simp [ne_of_lt hzlt]
  by_cases hzy : z = y
  · subst z
    simp [squareRootReplacementQuotientKernel_self hy]
  have hyz : y < z := by omega
  have hz2 : z < 2 * y := by omega
  rw [twoAB_quotientKernel_zero_strict_nearRoot hy hyz hz2]
  simp [hzy]

/-- Upper-half physical replacement fibre is exactly the NEGATIVE genuine
complementary Mobius fibre.  All strict quotient children are outside this
upper-half coordinate, so treating this diagonal in isolation loses partners. -/
theorem twoAB_replacementTail_eq_neg_mobius_upperHalf
    (R y : ℕ) (hR : 2 ≤ R) (hy : 1 ≤ y)
    (hyR : y < R) (hhalf : R ≤ 2 * y) :
    squareRootReplacementTailCoefficient R y =
      -squareRootReplacementTailMoebiusCoefficient R y := by
  rw [squareRootReplacementTailCoefficient_eq_neg_tailMoebiusKernel R y hR]
  congr 1
  calc
    (∑ z ∈ Finset.range R,
        squareRootReplacementTailMoebiusCoefficient R z *
          squareRootReplacementQuotientKernel z y) =
      ∑ z ∈ Finset.range R,
        if z = y then squareRootReplacementTailMoebiusCoefficient R z
        else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [twoAB_quotientKernel_diagonal_upperHalf R z y
            (Finset.mem_range.mp hz) hy hhalf]
          by_cases hzy : z = y <;> simp [hzy]
    _ = squareRootReplacementTailMoebiusCoefficient R y := by
          simp [Finset.mem_range.mpr hyR]

/-- Root-adjacent replacement weights are short ACTUAL Mobius increments,
plus only the terminal Kronecker face. -/
theorem twoAB_replacementCoefficient_upperHalf_eq_mertensIncrement
    (R y : ℕ) (hR : 2 ≤ R) (hy : 1 ≤ y)
    (hyR : y < R) (hhalf : R ≤ 2 * y) :
    squareRootReplacementCoefficient R y =
      (if y = R - 1 then 1 else 0) +
        (mertensSummatory (squareRootEndpoint R / y) -
          mertensSummatory (squareRootEndpoint R / (y + 1))) := by
  unfold squareRootReplacementCoefficient
  rw [twoAB_replacementTail_eq_neg_mobius_upperHalf
    R y hR hy hyR hhalf]
  rw [squareRootReplacementTailMoebiusCoefficient_eq_mertensIncrement
    R y hR hy hyR]
  ring

#print axioms twoABCompleteReciprocalPacket_eq_parent
#print axioms twoABCompleteReciprocalBand_eq_mertensDifference
#print axioms twoABCompleteReciprocalBand_norm_le_endpoints
#print axioms twoAB_quotientKernel_diagonal_upperHalf
#print axioms twoAB_replacementCoefficient_upperHalf_eq_mertensIncrement

end RHLean.Proof
