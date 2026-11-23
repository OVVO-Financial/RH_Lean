import RHLean.Geometry.NativeAllPlaceDescent

/-!
# Measured component normalization in the existing all-place lattice degree

The normalizing mass belongs to a measured component. Scaling each embedding's
norm by its inverse square root contributes exactly rank / 2 times the mean
logarithmic mass to the arithmetic degree. The proof changes the existing
Hermitian frame and computes its Gram determinant on the original O_K lattice;
there is no new definition of arithmetic degree or replacement lattice.

The orthogonal-sum part likewise uses the existing integer lattice, covolume,
field degree, and discriminant convention. It proves actual rank and degree
additivity from the component sublattices and their norm-square identity.
`NativeMeasuredComponentNorm` derives that identity for functions with disjoint
measurable supports and derives the mass factor from normalized restriction.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
Development/AbelianVarietyTheory/Proofs/DivisorProofs/
SlopeSqSubLeSlopeSqSpan.lean (`sum_mk`, `rk_mul_mu_eq`), DegScale.lean,
and InnerRealizeEqZero.lean. These finite all-place calculations are reconstructed
with the already-native Hermitian lattice implementation. No external olean or
terminal RH result is imported. The source mirror states no license.

Actual cusp realization, measured automorphic component identification, geometric
jet injection, and lower rank shares remain separate construction obligations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module TensorProduct Matrix
open RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt

namespace RHLean.Geometry.NativeMeasuredComponentDegree

section HeightNormalization

open RHLean.Geometry.AlpogeAllPlace.Formalism.HN

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

omit [StarRing K] in
private theorem place_count_ne_zero : (nPl K : ℝ) ≠ 0 := by
  unfold nPl
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

private theorem log_height (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    Real.log (ht b X L) = (nPl K : ℝ) * (rkK L : ℝ) * Real.log 2 -
      (rkK L : ℝ) / 2 * logDisc K -
      RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg
        (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L := by
  have hpos := (place_lattice_structure K V ι b X hX L hL).2.2
  have hc : RHLean.Geometry.AlpogeAllPlace.Formalism.F.covol
      (zl (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L) ≠ 0 := by
    intro h0
    rw [ht, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hd : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have h2 : ((2 : ℝ) ^ (nPl K * rkK L)) ≠ 0 := by positivity
  have h3 : |(NumberField.discr K : ℝ)| ^ (-(rkK L : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hd _).ne'
  rw [ht, Real.log_mul (mul_ne_zero h2 h3) hc, Real.log_mul h2 h3,
    Real.log_pow, Real.log_rpow hd]
  simp only [RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg,
    RHLean.Geometry.AlpogeAllPlace.Formalism.F.deg, logDisc]
  push_cast
  ring

private theorem rank_mul_squaredSlope [IsTotallyComplex K]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    (rkK L : ℝ) * muDef b X L = -Real.log (ht b X L) / (nPl K : ℝ) := by
  by_cases h0 : L = ⊥
  · rw [log_height b X hX L hL, h0,
      RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot,
      RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX]
    simp
  · have hpos := (place_lattice_structure K V ι b X hX L hL).2.2
    have hj : (rkK L : ℝ) ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      intro h
      exact h0
        (RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap.OrthogonalSumAlt.eq_bot_of_rkK b h)
    have hf : (nPl K : ℝ) ≠ 0 := place_count_ne_zero
    rw [(size_maximal_slope K V ι b X hX L hL h0).2.1, size, Real.log_rpow hpos]
    field_simp

end HeightNormalization

theorem embedding_sum_of_places (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (g : InfinitePlace K → ℝ) :
    ∑ σ : K →+* ℂ, g (InfinitePlace.mk σ) = 2 * ∑ v, g v := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun σ : K →+* ℂ => InfinitePlace.mk σ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g v) (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]),
    Finset.sum_const, nsmul_eq_mul, InfinitePlace.card_filter_mk_eq, (IsTotallyComplex.isComplex v).mult_eq_two]
  rfl


theorem rk_mul_mu_eq {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) {j : ℕ} (e : Fin j → V)
    (he : LinearIndependent K e) (L : Submodule (𝓞 K) V) (hL : L.FG)
    (hle : Submodule.span (𝓞 K) (Set.range e) ≤ L) (hj : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L = j) :
    (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 ∧
      (∀ v, 0 < (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.gramPl b X v e).det.re) ∧
      (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.nPl K : ℝ) * ((j : ℝ) * RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef b X L) =
        Real.log ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) -
          ∑ v, Real.log (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.gramPl b X v e).det.re := by
  obtain ⟨h1, h2⟩ := RHLean.Geometry.AlpogeAllPlace.Formalism.HN.htGram K V ι b X hX j e he
  have h3 := h2 L hL hle hj
  have p1 := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X hX L hL).2.2
  have p2 := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V ι b X hX _ (Submodule.fg_span (Set.finite_range e))).2.2
  have hi : ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≠ 0 := fun h => by
    rw [h, mul_zero] at h3
    exact p2.ne h3
  have hne : ∀ v ∈ Finset.univ, (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.gramPl b X v e).det.re ≠ 0 :=
    Finset.prod_ne_zero_iff.1 (h1 ▸ p2.ne')
  refine ⟨by exact_mod_cast hi, fun v => lt_of_le_of_ne ?_ (hne v (Finset.mem_univ v)).symm, ?_⟩
  · rw [← RHLean.Geometry.AlpogeAllPlace.Formalism.HN.HeightGram.norm_det_gramPl]; exact norm_nonneg _
  · have h4 := congrArg Real.log (h3.trans h1)
    rw [Real.log_mul p1.ne' hi, Real.log_prod hne] at h4
    have h5 := rank_mul_squaredSlope b X hX L hL
    rw [hj] at h5
    rw [h5, mul_div_cancel₀ _ place_count_ne_zero]
    linarith


theorem degree_scale : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N N' : (K →+* ℂ) → V → ℝ) (t : (K →+* ℂ) → ℝ), HasGram N → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ x = t σ * N σ x) → HasGram N' ∧ ∀ L : Submodule (𝓞 K) V, L.FG → deg N' L = deg N L - (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L : ℝ) * ((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) := by
  intro K V _ _ _ _ _ _ _ N N' t hN ht hc hN'
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  set X' : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ := fun v => ((t v.embedding : ℂ)⁻¹) • X v with hX'
  have htc : ∀ v : InfinitePlace K, (t v.embedding : ℂ) ≠ 0 := fun v => by
    exact_mod_cast (ht v.embedding).ne'
  have hinv : ∀ v, (X' v)⁻¹ = (t v.embedding : ℂ) • (X v)⁻¹ := fun v => by
    refine Matrix.inv_eq_left_inv ?_
    simp only [hX', Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ (hG v).1,
      inv_mul_cancel₀ (htc v), one_smul]
  have hfc : ∀ v x, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord b X' v x = (t v.embedding : ℂ) • RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord b X v x := fun v x => by
    simp only [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord, hinv]
    exact Matrix.smul_mulVec _ _ _
  have hnorm : ∀ v x, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.normAt b X' v x = t v.embedding * RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.normAt b X v x := fun v x => by
    simp only [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.normAt, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.cnorm, hfc, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
      ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ht _)]
  have hG' : IsGram b X' N' := fun v => by
    refine ⟨?_, fun x => by rw [hnorm, (hG v).2, hN']⟩
    simp only [hX', Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 (inv_ne_zero (htc v)))).mul (hG v).1
  refine ⟨hG'.hasGram, fun L hL => ?_⟩
  have hgram : ∀ v {j : ℕ} (e : Fin j → V), RHLean.Geometry.AlpogeAllPlace.Formalism.HN.gramPl b X' v e = (((t v.embedding) ^ 2 : ℝ) : ℂ) • RHLean.Geometry.AlpogeAllPlace.Formalism.HN.gramPl b X v e := by
    intro v j e
    ext a c
    simp only [RHLean.Geometry.AlpogeAllPlace.Formalism.HN.gramPl, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.majAt, hfc, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  have hdet : ∀ v {j : ℕ} (e : Fin j → V), (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.gramPl b X' v e).det.re =
      t v.embedding ^ (2 * j) * (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.gramPl b X v e).det.re := by
    intro v j e
    rw [hgram, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul, ← pow_mul]
  haveI : Module.Finite K V := Module.Finite.of_basis b
  obtain ⟨e, heL, hsp, he⟩ := Submodule.exists_fun_fin_finrank_span_eq K (L : Set V)
  have hj : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L = Module.finrank K (Submodule.span K (L : Set V)) := rfl
  generalize Module.finrank K (Submodule.span K (L : Set V)) = j at e heL hsp he hj
  obtain ⟨-, g1, m1⟩ := rk_mul_mu_eq b X (fun v => (hG v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  obtain ⟨-, g2, m2⟩ := rk_mul_mu_eq b X' (fun v => (hG' v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  have hlog : ∀ v, Real.log (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.gramPl b X' v e).det.re =
      (2 * j : ℝ) * Real.log (t v.embedding) + Real.log (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.gramPl b X v e).det.re := fun v => by
    rw [hdet, Real.log_mul (pow_pos (ht _) _).ne' (g1 v).ne', Real.log_pow]
    push_cast; ring
  have hsum : ∑ σ : K →+* ℂ, Real.log (t σ) = 2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    rw [← embedding_sum_of_places K (fun v => Real.log (t v.embedding))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]; exact congrArg Real.log (hc σ).symm
  have hfin : (Module.finrank ℚ K : ℝ) = 2 * RHLean.Geometry.AlpogeAllPlace.Formalism.HN.nPl K := by
    have := embedding_sum_of_places K (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    rw [← NumberField.Embeddings.card K ℂ, this]
    rfl
  have hP : (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.nPl K : ℝ) ≠ 0 := by exact_mod_cast (place_count_ne_zero (K := K))
  rw [Finset.sum_congr rfl (fun v _ => hlog v), Finset.sum_add_distrib, ← Finset.mul_sum] at m2
  simp only [RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.deg, RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.slope, slope_sq_eq hG hL, slope_sq_eq hG' hL, hj, hsum, hfin]
  have key : (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.nPl K : ℝ) * ((j : ℝ) * RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef b X' L) = (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.nPl K : ℝ) * ((j : ℝ) * RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef b X L)
      - 2 * j * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by linarith
  field_simp
  linear_combination key


end RHLean.Geometry.NativeMeasuredComponentDegree

namespace RHLean.Geometry.NativeMeasuredComponentDegree.OrthogonalSum

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

theorem gram_zero [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.IsGram b X N) (v : InfinitePlace K) : N v.embedding 0 = 0 := by
  rw [← (hG v).2 0]
  simp [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.normAt, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.cnorm, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord_zero]

theorem inner_realize_eq_zero [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.IsGram b X N) {x y : V}
    (h : ∀ v : InfinitePlace K, N v.embedding (x + y) ^ 2 = N v.embedding x ^ 2 + N v.embedding y ^ 2) :
    inner ℝ (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X x) (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  have hs : ∀ z, ‖RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X z‖ ^ 2 = ∑ v : InfinitePlace K, N v.embedding z ^ 2 := fun z => by
    rw [RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.norm_realize_sq]
    exact Finset.sum_congr rfl fun v _ => by rw [(hG v).2]
  have h1 := hs (x + y)
  rw [map_add, norm_add_sq_real, hs x, hs y] at h1
  rw [Finset.sum_congr rfl fun v _ => h v, Finset.sum_add_distrib] at h1
  linarith

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem inner_pair [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.IsGram b X N) {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V)
    (hN : ∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) →
      N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2)
    {i j : ι} (hij : i ≠ j) {x y : V} (hx : x ∈ M i) (hy : y ∈ M j) :
    inner ℝ (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X x) (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  refine inner_realize_eq_zero hG fun v => ?_
  have hmem : ∀ (k : ι) (z : V) (_ : z ∈ M k) (l : ι),
      (Pi.single k z : ι → V) l ∈ Submodule.span K (M l : Set V) := by
    intro k z hz l
    by_cases hl : l = k
    · subst hl; simpa using Submodule.subset_span hz
    · simp [Pi.single_apply, hl]
  have h := hN v.embedding (Pi.single i x + Pi.single j y) fun l =>
    Submodule.add_mem _ (hmem i x hx l) (hmem j y hy l)
  have hsum : ∑ l, (Pi.single i x + Pi.single j y : ι → V) l = x + y := by
    simp [Finset.sum_add_distrib]
  have hpt : ∀ l, N v.embedding ((Pi.single i x + Pi.single j y : ι → V) l) ^ 2 =
      (Pi.single i (N v.embedding x ^ 2) : ι → ℝ) l + (Pi.single j (N v.embedding y ^ 2) : ι → ℝ) l := by
    intro l
    by_cases hli : l = i
    · subst hli; simp [Pi.single_apply, hij]
    · by_cases hlj : l = j
      · subst hlj; simp [Pi.single_apply, hli]
      · simp [Pi.single_apply, hli, hlj, gram_zero hG v]
  rw [hsum, Finset.sum_congr rfl fun l _ => hpt l, Finset.sum_add_distrib] at h
  simpa using h

theorem deg_eq [IsTotallyComplex K] [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.IsGram b X N) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.deg N L = 1 / (Module.finrank ℚ K : ℝ) * RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L +
      (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L : ℝ) * ((-Real.log 2 + RHLean.Geometry.AlpogeAllPlace.Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) / 2) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  rw [RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.deg, RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.slope, RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.slope_sq_eq hG hL]
  by_cases h0 : L = ⊥
  · subst h0
    simp [RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX]
  · have hr : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L ≠ 0 := fun h => h0 (RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap.OrthogonalSumAlt.eq_bot_of_rkK b h)
    have hrk := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V (Fin n) b X hX L hL).2.1
    have hs : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.slope (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L =
        RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L / (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rk (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) L : ℝ) := rfl
    have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
      exact_mod_cast (RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)).ne'
    have hr' : (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L : ℝ) ≠ 0 := by exact_mod_cast hr
    rw [RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef, hs, hrk]
    push_cast
    field_simp
    ring

end RHLean.Geometry.NativeMeasuredComponentDegree.OrthogonalSum

namespace RHLean.Geometry.NativeMeasuredComponentDegree.OrthogonalSum

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem sum_finset [IsTotallyComplex K] [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.IsGram b X N) {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V)
    (hM : ∀ i, (M i).FG)
    (hN : ∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) →
      N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2) (s : Finset ι) :
    (⨆ i ∈ s, M i).FG ∧ RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (⨆ i ∈ s, M i) = ∑ i ∈ s, RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (M i) ∧
      RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) (⨆ i ∈ s, M i) =
        ∑ i ∈ s, RHLean.Geometry.AlpogeAllPlace.Formalism.HN.deg (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) (M i) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  induction s using Finset.induction_on with
  | empty =>
    simp [RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX, Submodule.fg_bot]
  | insert a s ha ih =>
    obtain ⟨ihfg, ihrk, ihdeg⟩ := ih
    rw [Finset.iSup_insert]
    set B := ⨆ i ∈ s, M i with hB
    have ho : ∀ x ∈ M a, ∀ y ∈ B,
        inner ℝ (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X x) (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
      intro x hx y hy
      obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum M y).1 hy
      rw [← hμ, map_sum, inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact inner_pair hG M hN (by rintro rfl; exact ha hi) hx (μ i).2
    have hlA := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V (Fin n) b X hX (M a) (hM a)).1
    have hlB := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V (Fin n) b X hX B ihfg).1
    obtain ⟨hl, hdeg, -⟩ :=
      (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) V _ (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X)).2 (M a) B hlA hlB ho
    have hfg : (M a ⊔ B).FG := (hM a).sup ihfg
    have hinf : M a ⊓ B = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have h1 := ho x hx.1 x hx.2
      rw [inner_self_eq_zero] at h1
      exact RHLean.Geometry.AlpogeAllPlace.Formalism.HN.HeightGram.realize_injective b X hX (by rw [h1, map_zero])
    have hrk := (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.degSupermod (𝓞 K) V _ (RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.realize b X) (M a ⊔ B) (M a) B hl
      le_sup_left le_sup_right).1
    rw [hinf, (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V (Fin n) b X hX _ hfg).2.1, (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V (Fin n) b X hX _ (hM a)).2.1,
      (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V (Fin n) b X hX _ ihfg).2.1,
      (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.plLat K V (Fin n) b X hX _ Submodule.fg_bot).2.1, RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, mul_zero, add_zero,
      ← mul_add] at hrk
    have hrk' := Nat.eq_of_mul_eq_mul_left (RHLean.Geometry.AlpogeAllPlace.Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)) hrk
    refine ⟨hfg, ?_, ?_⟩
    · rw [hrk', Finset.sum_insert ha, ihrk]
    · rw [hdeg, Finset.sum_insert ha, ihdeg]

theorem rkK_deg_iSup : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (ι : Type) [Fintype ι] (N : (K →+* ℂ) → V → ℝ)
    (M : ι → Submodule (𝓞 K) V), HasGram N → (∀ i, (M i).FG) →
    (∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) → N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2) →
    RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (⨆ i, M i) = ∑ i, RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (M i) ∧ deg N (⨆ i, M i) = ∑ i, deg N (M i) := by
  intro K V _ _ _ _ _ _ _ ι _ N M hG hM hN
  classical
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨⟨b, X⟩, hbX⟩⟩⟩ := hG
  obtain ⟨hfg, hrk, hdeg⟩ := sum_finset hbX M hM hN Finset.univ
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), M i) = ⨆ i, M i := by simp
  rw [hu] at hfg hrk hdeg
  refine ⟨hrk, ?_⟩
  rw [deg_eq hbX _ hfg, hdeg, hrk, Finset.mul_sum]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (deg_eq hbX _ (hM i)).symm

end RHLean.Geometry.NativeMeasuredComponentDegree.OrthogonalSum
namespace RHLean.Geometry.NativeMeasuredComponentDegree.Restriction

open scoped MatrixOrder ComplexOrder

/-! Restriction is carried out on the original O_K module by the actual linear
inclusion. Positive Gram factorization constructs its frame, and native
`HN.rerealize` proves equality of rank and degree of the mapped lattice.
Source: `ExistsSmulMemOfMemSpan.lean` and `HasGramComp.lean`. -/

theorem sum_norm_sq_eq {n : ℕ} (u : Fin n → ℂ) : ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem cnorm_mulVec_eq {n n' m : ℕ} {A : Matrix (Fin n) (Fin m) ℂ} {Y : Matrix (Fin n') (Fin m) ℂ} (h : Aᴴ * A = Yᴴ * Y)
    (u : Fin m → ℂ) : RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.cnorm (Y *ᵥ u) = RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.cnorm (A *ᵥ u) := by
  have key : ∀ {k : ℕ} (B : Matrix (Fin k) (Fin m) ℂ), star (B *ᵥ u) ⬝ᵥ (B *ᵥ u) = star u ⬝ᵥ ((Bᴴ * B) *ᵥ u) := fun B => by
    have e0 : star u ⬝ᵥ (Bᴴ *ᵥ (B *ᵥ u)) = (star u ᵥ* Bᴴ) ⬝ᵥ (B *ᵥ u) := dotProduct_mulVec _ _ _
    rw [← mulVec_mulVec, e0, star_mulVec]
  have e : ∑ i, ‖(Y *ᵥ u) i‖ ^ 2 = ∑ i, ‖(A *ᵥ u) i‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [sum_norm_sq_eq, sum_norm_sq_eq, key, key, h]
  simp only [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.cnorm, e]

theorem cnorm_smul {n : ℕ} {t : ℝ} (ht : 0 < t) (u : Fin n → ℂ) :
    RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.cnorm ((t : ℂ) • u) = t * RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.cnorm u := by
  simp only [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.cnorm, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, mul_pow,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem exists_unit_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ A = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  refine ⟨B, ?_, by simpa [star_eq_conjTranspose] using hB⟩
  have h1 : A.det ≠ 0 := hA.det_pos.ne'
  rw [hB, star_eq_conjTranspose, det_mul] at h1
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)

theorem hasGram_of_injective {N : (K →+* ℂ) → V → ℝ} (h : HasGram N) (φ : W →ₗ[K] V) (hφ : Function.Injective φ)
    {N' : (K →+* ℂ) → W → ℝ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (hN : ∀ (v : InfinitePlace K) (x : W), N' v.embedding x = t v * N v.embedding (φ x)) : HasGram N' := by
  classical
  obtain ⟨n, ⟨b, X⟩, hX⟩ := h
  dsimp only at hX
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  haveI : FiniteDimensional K W := FiniteDimensional.of_injective φ hφ
  let b' := Module.finBasis K W
  let B : Matrix (Fin n) (Fin (finrank K W)) K := LinearMap.toMatrix b' b φ
  obtain ⟨g, hg⟩ := φ.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hφ)
  let C : Matrix (Fin (finrank K W)) (Fin n) K := LinearMap.toMatrix b b' g
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  have key : ∀ v : InfinitePlace K, ∃ Y : Matrix (Fin (finrank K W)) (Fin (finrank K W)) ℂ, IsUnit Y.det ∧
      ((X v)⁻¹ * B.map v.embedding)ᴴ * ((X v)⁻¹ * B.map v.embedding) = Yᴴ * Y := fun v => by
    have hu := (hX v).1
    have hL : (C.map v.embedding * X v) * ((X v)⁻¹ * B.map v.embedding) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (X v), Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, ← Matrix.map_mul, hCB,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hinj : Function.Injective ((X v)⁻¹ * B.map v.embedding).mulVec := fun y z hyz => by
      have := congrArg (C.map v.embedding * X v).mulVec hyz
      simpa only [mulVec_mulVec, hL, one_mulVec] using this
    exact exists_unit_factor (PosDef.conjTranspose_mul_self _ hinj)
  choose Y hY hYG using key
  have hu : ∀ v, IsUnit (((t v : ℂ)) • Y v).det := fun v => by
    rw [det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 (by exact_mod_cast (ht v).ne'))).mul (hY v)
  refine IsGram.hasGram (b := b') (X := fun v => ((t v : ℂ) • Y v)⁻¹) fun v => ⟨?_, fun x => ?_⟩
  · exact Matrix.isUnit_nonsing_inv_det _ (hu v)
  · have e1 : RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.vecAt b v (φ x) = B.map v.embedding *ᵥ RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.vecAt b' v x := by
      funext i
      have e := congrFun (LinearMap.toMatrix_mulVec_repr b' b φ x) i
      show v.embedding (b.repr (φ x) i) = _
      rw [← e]
      exact RingHom.map_mulVec v.embedding _ _ i
    rw [hN v x, ← (hX v).2 (φ x)]
    simp only [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.normAt, RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord]
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu v), smul_mulVec, cnorm_smul (ht v), e1, mulVec_mulVec,
      cnorm_mulVec_eq (hYG v)]

theorem restrict_deg : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (φ : W →ₗ[K] V), Function.Injective φ → HasGram N → HasGram (fun σ (x : W) => N σ (φ x)) ∧ ∀ L : Submodule (𝓞 K) W, L.FG → RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (L.map (φ.restrictScalars (𝓞 K))) = RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L ∧ deg N (L.map (φ.restrictScalars (𝓞 K))) = deg (fun σ (x : W) => N σ (φ x)) L := by
  intro K V _ _ _ _ _ _ _ W _ _ _ _ N φ hφ hN
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  have hN' : HasGram (fun σ (x : W) => N σ (φ x)) :=
    hasGram_of_injective hG.hasGram φ hφ (fun _ => 1) (fun _ => one_pos)
      (fun _ _ => (one_mul _).symm)
  refine ⟨hN', fun L hL => ?_⟩
  obtain ⟨⟨m, ⟨c, Y⟩, hG'⟩⟩ := hN'
  letI : StarRing K := starRingOfComm
  have hr := RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rerealize K W (Fin m) V (Fin n) c Y b X φ (fun v => (hG' v).1) (fun v => (hG v).1) hφ
    (fun v x => by rw [(hG v).2, (hG' v).2]) L hL
  have hrk : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (L.map (φ.restrictScalars (𝓞 K))) = RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L := by
    unfold RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK
    have hs : Submodule.span K ((L.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) =
        (Submodule.span K (L : Set W)).map φ := by
      rw [Submodule.map_coe, ← Submodule.span_image]
      rfl
    rw [hs]
    exact (Submodule.equivMapOfInjective φ hφ _).finrank_eq.symm
  refine ⟨hrk, ?_⟩
  unfold RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.deg RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.slope
  rw [hrk, slope_sq_eq hG (hL.map _), slope_sq_eq hG' hL]
  unfold RHLean.Geometry.AlpogeAllPlace.Formalism.HN.muDef
  rw [hr.2.2.1]

end RHLean.Geometry.NativeMeasuredComponentDegree.Restriction

end
