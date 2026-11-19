import «research.NYMAN_TAIL_ABEL»

/-! An upper and a lower strict tail phase for every nonconstant squared residual. -/
set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators
namespace RHLean.Analysis

private theorem weight_drop (t : Nat) (ht : 0<t) : 0 < nymanWeight t-nymanWeight (t+1) := by
  have hx : (0:ℝ)<t := by exact_mod_cast ht
  unfold nymanWeight
  rw [Nat.cast_add, Nat.cast_one]
  apply sub_pos.mpr
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith

private theorem reaches (F : Nat → ℝ) (P : Nat) (hp : 0<P) (h : Function.Periodic F P)
    (s t : Nat) : ∃ n : Nat, F (s+n+1) = F t := by
  have hle : s+1 ≤ (s+1)*P+t := by
    have hl := Nat.mul_le_mul_left (s+1) (show 1 ≤ P by omega)
    simpa only [Nat.mul_one] using hl.trans (Nat.le_add_right _ t)
  refine ⟨(s+1)*P+t-(s+1), ?_⟩
  rw [show s+((s+1)*P+t-(s+1))+1 = (s+1)*P+t by omega, ← h.map_mod_nat ((s+1)*P+t)]
  simpa only [Nat.mul_add_mod] using h.map_mod_nat t

private theorem sum_pos {f : Nat → ℝ} {z : ℝ} (h : HasSum f z) (hn : ∀ n, 0 ≤ f n)
    {j : Nat} (hj : 0 < f j) : 0 < z := by
  rw [← h.tsum_eq]; exact h.summable.tsum_pos hn j hj

/-- Both signs hold from the first positive cutoff in their respective classes, not just eventually. -/
theorem nyman_tail_two_phases (N P : Nat) (c : Nat → ℝ) (hP : 0<P)
    (hp : ∀ k ∈ Icc 2 N, k ∣ P)
    (hv : ∃ i j, nymanResidual N c i ^ 2 ≠ nymanResidual N c j ^ 2) :
    ∃ a b : Fin P, a ≠ b ∧
      (∀ s : Nat, 0<s → s%P=a.val → nymanPeriodLevel N c/(s:ℝ) < nymanPhysicalTail N c s) ∧
      (∀ s : Nat, 0<s → s%P=b.val → nymanPhysicalTail N c s < nymanPeriodLevel N c/(s:ℝ)) := by
  let F := nymanCutoffPrimitive N c
  have hper : Function.Periodic F P := nyman_cutoff_primitive_periodic N P c hp
  have hne : (range P).Nonempty := ⟨0, mem_range.mpr hP⟩
  obtain ⟨a, ha, hmin⟩ := (range P).exists_min_image F hne
  obtain ⟨b, hb, hmax⟩ := (range P).exists_max_image F hne
  have hlo (t : Nat) : F a ≤ F t := by rw [← hper.map_mod_nat t]; exact hmin _ (mem_range.mpr (Nat.mod_lt _ hP))
  have hhi (t : Nat) : F t ≤ F b := by rw [← hper.map_mod_nat t]; exact hmax _ (mem_range.mpr (Nat.mod_lt _ hP))
  have hlt : F a < F b := by
    by_contra! h
    have hc (t : Nat) : F t = F a := le_antisymm ((hhi t).trans h) (hlo t)
    have hd (t : Nat) : nymanResidual N c t ^ 2 = nymanPeriodLevel N c := by
      have hh : F (t+1) = F t + (nymanResidual N c t^2-nymanPeriodLevel N c) := by
        exact sum_range_succ _ t
      rw [hc (t+1), hc t] at hh; linarith
    obtain ⟨i,j,hij⟩ := hv
    exact hij ((hd i).trans (hd j).symm)
  refine ⟨⟨a, mem_range.mp ha⟩, ⟨b, mem_range.mp hb⟩, ?_, ?_, ?_⟩
  · intro he
    have hv' : a=b := congrArg Fin.val he
    exact hlt.ne (congrArg F hv')
  · intro s hs hclass
    have hfs : F s = F a := (hper.map_mod_nat s).symm.trans (congrArg F hclass)
    obtain ⟨j,hj⟩ := reaches F P hP hper s b
    apply sub_pos.mp
    apply sum_pos (nyman_tail_abel N P s c hP hs hp) (j := j)
    · intro n
      apply mul_nonneg (weight_drop (s+n) (by omega)).le
      change 0 ≤ F (s+n+1)-F s; rw [hfs]; exact sub_nonneg.mpr (hlo _)
    · apply mul_pos (weight_drop (s+j) (by omega))
      change 0 < F (s+j+1)-F s; rw [hfs, hj]; exact sub_pos.mpr hlt
  · intro s hs hclass
    have hfs : F s = F b := (hper.map_mod_nat s).symm.trans (congrArg F hclass)
    obtain ⟨j,hj⟩ := reaches F P hP hper s a
    have H := (nyman_tail_abel N P s c hP hs hp).neg
    have hz : 0 < -(nymanPhysicalTail N c s - nymanPeriodLevel N c/(s:ℝ)) := by
      apply sum_pos H (j := j)
      · intro n; apply neg_nonneg.mpr
        apply mul_nonpos_of_nonneg_of_nonpos (weight_drop (s+n) (by omega)).le
        change F (s+n+1)-F s ≤ 0; rw [hfs]; exact sub_nonpos.mpr (hhi _)
      · apply neg_pos.mpr
        apply mul_neg_of_pos_of_neg (weight_drop (s+j) (by omega))
        change F (s+j+1)-F s < 0; rw [hfs, hj]; exact sub_neg.mpr hlt
    linarith

/-- The two original coefficient moments give the physical two-sign obstruction with no bias term. -/
theorem nyman_two_moment_tail_phases (N P : Nat) (c : Nat → ℝ) (hP : 0<P)
    (hp : ∀ k ∈ Icc 2 N, k ∣ P) (h1 : ∑ k ∈ Icc 2 N, c k/(k:ℝ) = 1)
    (h3 : ∑ k ∈ Icc 2 N, c k = 3) :
    ∃ a b : Fin P, a ≠ b ∧
      (∀ s : Nat, 0<s → s%P=a.val → nymanCovariance N c/(s:ℝ) < nymanPhysicalTail N c s) ∧
      (∀ s : Nat, 0<s → s%P=b.val → nymanPhysicalTail N c s < nymanCovariance N c/(s:ℝ)) := by
  have r0 : nymanResidual N c 0 = 1 := by simp [nymanResidual, nymanResidue]
  have hsum : (∑ k ∈ Icc 2 N, c k * nymanResidue k 1) = ∑ k ∈ Icc 2 N, c k/(k:ℝ) := by
    apply sum_congr rfl; intro k hk
    have hk' : 1<k := by have := (mem_Icc.mp hk).1; omega
    simp [nymanResidue, Nat.mod_eq_of_lt hk', div_eq_mul_inv]
  have r1 : nymanResidual N c 1 = 0 := by simp only [nymanResidual, hsum, h1, sub_self]
  have bias : nymanPeriodBias N c = 0 := by
    have he : (∑ k ∈ Icc 2 N, (c k/(k:ℝ))*(((k:ℝ)-1)/2)) =
        ((∑ k ∈ Icc 2 N, c k)-(∑ k ∈ Icc 2 N, c k/(k:ℝ)))/2 := by
      rw [← sum_sub_distrib, sum_div]
      apply sum_congr rfl; intro k hk
      have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by have := (mem_Icc.mp hk).1; omega)
      field_simp; ring
    unfold nymanPeriodBias; rw [he,h3,h1]; norm_num
  have out := nyman_tail_two_phases N P c hP hp ⟨0,1,by rw [r0,r1]; norm_num⟩
  simpa [nymanPeriodLevel, bias] using out

end RHLean.Analysis
