import RHLean.Geometry.AlpogeAllPlace.Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import RHLean.Geometry.AlpogeAllPlace.Formalism.QuotientMetricDivisors.Statement

/-! The finite lattice estimate used by the Core 21 summand comparison.
An independent integral frame measures both the archimedean Gram determinants
and the index of its span inside the original lattice. -/

namespace RHLean.Geometry.NativeSummandCovolume

open Module NumberField RHLean.Geometry.AlpogeAllPlace.Formalism
open scoped BigOperators

/-- An upper bound on each place's Gram determinant gives a normalized log
covolume bound with the actual integral index in the denominator. -/
theorem normalized_lcv_le_of_gram_bounds
    {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    {d r : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ v, IsUnit (X v).det)
    (M : Submodule (𝓞 K) (Fin d → K)) (hM : M.FG)
    (e : Fin r → Fin d → K) (he : LinearIndependent K e)
    (hspan : Submodule.span (𝓞 K) (Set.range e) ≤ M) (hr : HN.rkK M = r)
    (B : InfinitePlace K → ℝ) (hB : ∀ v, (DivisionValues.gram X v e).det.re ≤ B v)
    (D : ℕ) (hD : 0 < D) :
    DivisionValues.lcv X M / (D : ℝ) ≤
      (2 / (finrank ℚ K : ℝ)) * Real.log ((∏ v, B v) /
        ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex M.toAddSubgroup : ℝ)) /
        (D : ℝ) := by
  classical
  let b := Pi.basisFun K (Fin d)
  let F := Submodule.span (𝓞 K) (Set.range e)
  let I := F.toAddSubgroup.relIndex M.toAddSubgroup
  obtain ⟨hprod, hindex⟩ :=
    HN.height_gram_determinant K (Fin d → K) (Fin d) b X hX r e he
  have hmul : HN.ht b X M * (I : ℝ) = HN.ht b X F := hindex M hM hspan hr
  have hpos := (HN.place_lattice_structure K _ _ b X hX M hM).2.2
  have hframe := (HN.place_lattice_structure K _ _ b X hX F
    (Submodule.fg_span (Set.finite_range e))).2.2
  have hi : (I : ℝ) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hmul
    exact hframe.ne hmul
  have hheight : HN.ht b X M ≤ (∏ v, B v) / (I : ℝ) := by
    apply (le_div_iff₀ (lt_of_le_of_ne (Nat.cast_nonneg I) hi.symm)).2
    rw [hmul.trans hprod]
    apply Finset.prod_le_prod _ (fun v _ => hB v)
    intro v _
    change 0 ≤ (HN.gramPl b X v e).det.re
    rw [← HN.HeightGram.norm_det_gramPl]
    exact norm_nonneg _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.log_le_log hpos hheight)
      (div_nonneg (by norm_num) (Nat.cast_nonneg _))) (Nat.cast_pos.mpr hD).le

end RHLean.Geometry.NativeSummandCovolume
