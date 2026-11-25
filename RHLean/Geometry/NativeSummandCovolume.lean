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
    refine Finset.prod_le_prod₀ ?_ (fun v _ => hB v)
    intro v _
    change 0 ≤ (HN.gramPl b X v e).det.re
    rw [← HN.HeightGram.norm_det_gramPl]
    exact norm_nonneg _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.log_le_log hpos hheight)
      (div_nonneg (by norm_num) (Nat.cast_nonneg _))) (Nat.cast_pos.mpr hD).le

/-- Residue lifts at comaximal moduli can be combined in the same global module.
The local maps may have different target modules. -/
theorem joint_residues_of_comaximal {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype ι] {Q : ι → Type*} [∀ i, AddCommGroup (Q i)] [∀ i, Module R (Q i)]
    (I : ι → Ideal R) (hI : Pairwise fun i j => IsCoprime (I i) (I j))
    (hzero : ∀ i (a : R), a ∈ I i → ∀ z : Q i, a • z = 0)
    (red : (i : ι) → V →ₗ[R] Q i) (T : (i : ι) → AddSubgroup (Q i))
    (hlift : ∀ i, T i ≤ (red i).toAddMonoidHom.range) :
    AddSubgroup.pi Set.univ T ≤ (LinearMap.pi red).toAddMonoidHom.range := by
  classical
  intro y hy
  have hone : ∀ i, ∃ b : R, ∀ j, b - (if j = i then 1 else 0) ∈ I j :=
    fun i => Ideal.exists_forall_sub_mem_ideal hI (fun j => if j = i then 1 else 0)
  choose b hb using hone
  have hpoint : ∀ i, ∃ v : V, red i v = y i := fun i => hlift i (hy i (Set.mem_univ i))
  choose v hv using hpoint
  refine ⟨∑ i, b i • v i, funext fun j => ?_⟩
  change red j (∑ i, b i • v i) = y j
  simp only [map_sum, map_smul]
  rw [Fintype.sum_eq_single j]
  · have hm : b j - 1 ∈ I j := by simpa only [if_pos rfl] using hb j j
    have hs := hzero j _ hm (red j (v j))
    rw [sub_smul, one_smul, sub_eq_zero] at hs
    exact hs.trans (hv j)
  · intro i hij
    have hm : b i ∈ I j := by simpa only [if_neg hij.symm, sub_zero] using hb i j
    exact hzero j _ hm _

/-- Recovered residue coordinates contribute to the index when every measured frame
vector reduces to zero. The reduction is defined on the integral lattice itself. -/
theorem recovered_card_dvd_frame_relIndex
    {R V Q ι : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [AddCommGroup Q] [Module R Q]
    (M : Submodule R V) (e : ι → V) (hspan : Submodule.span R (Set.range e) ≤ M)
    (red : M →ₗ[R] Q) (T : AddSubgroup Q)
    (hframe : ∀ i, red ⟨e i, hspan (Submodule.subset_span ⟨i, rfl⟩)⟩ = 0)
    (hlift : T ≤ red.toAddMonoidHom.range) :
    Nat.card T ∣ (Submodule.span R (Set.range e)).toAddSubgroup.relIndex M.toAddSubgroup := by
  have hk : Submodule.span R (Set.range e) ≤ red.ker.map M.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_map.mpr
      ⟨⟨e i, hspan (Submodule.subset_span ⟨i, rfl⟩)⟩, hframe i, rfl⟩
  have hsub : (Submodule.span R (Set.range e)).toAddSubgroup.addSubgroupOf M.toAddSubgroup ≤
      red.toAddMonoidHom.ker := by
    intro x hx
    change (x : V) ∈ Submodule.span R (Set.range e) at hx
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp (hk hx)
    have hyx : y = x := Subtype.ext heq
    change red x = 0
    rw [← hyx]
    exact hy
  calc
    Nat.card T ∣ Nat.card red.toAddMonoidHom.range := AddSubgroup.card_dvd_of_le hlift
    _ = red.toAddMonoidHom.ker.index := (AddSubgroup.index_ker _).symm
    _ ∣ _ := AddSubgroup.index_dvd_of_le hsub

/-- The number of tuples in an ideal-power layer, measured in powers of the ideal. -/
theorem card_idealPower_residue_grid
    {K : Type} [Field K] [NumberField K] (P : Ideal (𝓞 K)) (hP : P ≠ ⊥) (a b n : ℕ) :
    let red := (Ideal.Quotient.mk (P ^ (a + b))).toAddMonoidHom
    let T := (P ^ a).toAddSubgroup.map red
    Nat.card (AddSubgroup.pi Set.univ (fun _ : Fin n => T)) = P.absNorm ^ (b * n) := by
  classical
  let red := (Ideal.Quotient.mk (P ^ (a + b))).toAddMonoidHom
  let T := (P ^ a).toAddSubgroup.map red
  let Tn := AddSubgroup.pi Set.univ (fun _ : Fin n => T)
  change Nat.card Tn = P.absNorm ^ (b * n)
  have hle : (P ^ (a + b)).toAddSubgroup ≤ (P ^ a).toAddSubgroup :=
    show P ^ (a + b) ≤ P ^ a from Ideal.pow_le_pow_right (by omega)
  have hi := AddSubgroup.relIndex_mul_index hle
  simp only [← Ideal.absNorm_eq_index, map_pow] at hi
  have hn : P.absNorm ^ a ≠ 0 := pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  have hindex : (P ^ (a + b)).toAddSubgroup.relIndex (P ^ a).toAddSubgroup = P.absNorm ^ b :=
    mul_right_cancel₀ hn (hi.trans (by rw [pow_add, mul_comm]))
  have hker : red.ker = (P ^ (a + b)).toAddSubgroup := by
    ext z
    exact Ideal.Quotient.eq_zero_iff_mem
  have hcard : Nat.card T = P.absNorm ^ b := by
    change Nat.card ((P ^ a).toAddSubgroup.map red) = _
    rw [← AddSubgroup.relIndex_ker, hker, hindex]
  let bij : Tn ≃ (Fin n → T) :=
    { toFun := fun x i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
      invFun := fun x => ⟨fun i => (x i).1, fun i _ => (x i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr bij, Nat.card_fun, hcard, Nat.card_fin, pow_mul]

/-- The determinants and the vanishing residues are both measured on the same frame. -/
theorem normalized_lcv_le_of_recovered_residues
    {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    {d r : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ v, IsUnit (X v).det)
    (M : Submodule (𝓞 K) (Fin d → K)) (hM : M.FG)
    (e : Fin r → Fin d → K) (he : LinearIndependent K e)
    (hspan : Submodule.span (𝓞 K) (Set.range e) ≤ M) (hr : HN.rkK M = r)
    (B : InfinitePlace K → ℝ) (hB : ∀ v, (DivisionValues.gram X v e).det.re ≤ B v)
    {Q : Type*} [AddCommGroup Q] [Module (𝓞 K) Q]
    (red : M →ₗ[𝓞 K] Q) (T : AddSubgroup Q) [Finite T]
    (hframe : ∀ i, red ⟨e i, hspan (Submodule.subset_span ⟨i, rfl⟩)⟩ = 0)
    (hlift : T ≤ red.toAddMonoidHom.range) (D : ℕ) (hD : 0 < D) :
    DivisionValues.lcv X M / (D : ℝ) ≤
      (2 / (finrank ℚ K : ℝ)) * Real.log ((∏ v, B v) / (Nat.card T : ℝ)) / (D : ℝ) := by
  classical
  let b := Pi.basisFun K (Fin d)
  let F := Submodule.span (𝓞 K) (Set.range e)
  let I := F.toAddSubgroup.relIndex M.toAddSubgroup
  have hmul : HN.ht b X M * (I : ℝ) = HN.ht b X F :=
    (HN.height_gram_determinant K (Fin d → K) (Fin d) b X hX r e he).2 M hM hspan hr
  have hfpos : 0 < HN.ht b X F := (HN.place_lattice_structure K _ _ b X hX F
    (Submodule.fg_span (Set.finite_range e))).2.2
  have hi : I ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero, mul_zero] at hmul
    exact hfpos.ne hmul
  have hcard : Nat.card T ≤ I := Nat.le_of_dvd (Nat.pos_of_ne_zero hi)
    (recovered_card_dvd_frame_relIndex M e hspan red T hframe hlift)
  have htr : 0 < (Nat.card T : ℝ) := Nat.cast_pos.mpr Nat.card_pos
  have hle : (Nat.card T : ℝ) ≤ (I : ℝ) := by exact_mod_cast hcard
  have hlog : Real.log ((∏ v, B v) / (I : ℝ)) ≤
      Real.log ((∏ v, B v) / (Nat.card T : ℝ)) := by
    by_cases hz : (∏ v, B v) = 0
    · simp [hz]
    rw [Real.log_div hz (htr.trans_le hle).ne', Real.log_div hz htr.ne']
    exact sub_le_sub_left (Real.log_le_log htr hle) _
  exact (normalized_lcv_le_of_gram_bounds X hX M hM e he hspan hr B hB D hD).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog
      (div_nonneg (by norm_num) (Nat.cast_nonneg _))) (Nat.cast_pos.mpr hD).le)

end RHLean.Geometry.NativeSummandCovolume
