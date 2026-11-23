import RHLean.Geometry.NativeMeasuredComponentDegree

/-!
# Component measures, actual L2 norms, and their arithmetic-degree correction

For functions supported on a measured component, the global squared L2 norm is
its measured mass times the squared norm for normalized restriction. Disjoint
measurable supports give an orthogonal sum. Both equalities are proved from the
integrals; neither an orthogonality certificate nor a prescribed mass is an input.

The final theorems use these identities in the existing all-place O_K lattice
rank and degree. The component degree contains the exact logarithmic mass term,
including the rank-zero case. This is the normalization calculation in
`CompAdds.degRes_eq` and `CompAdds.sums`, before the actual cusp/model realization
has been supplied. It is not an identification of a torus Haar measure with an
automorphic Petersson measure.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
Development/AbelianVarietyTheory/Proofs/DivisorProofs/
ComponentsPeterssonOrthogonalAndMasses.lean (`lint_sqN_sum`, `petAt_muOn_sq`),
ComponentRanksDegreesAddWithMasses.lean (`normOn_eq_of_mass`, `degRes_eq`, `sums`),
and ExistsSmulMemOfMemSpan.lean (`HasGram_eq_zero`).
The source mirror states no license; attribution is preserved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField MeasureTheory Matrix Module
open scoped BigOperators ENNReal

namespace RHLean.Geometry.NativeMeasuredComponentNorm

variable {X : Type} [MeasurableSpace X]

/-- Squared magnitude of the actual function, as a nonnegative integrand. -/
def squareMagnitude (f : X → ℂ) (x : X) : ℝ≥0∞ := ‖f x‖ₑ ^ (2 : ℕ)

/-- The literal square-integral norm. Finiteness is stated wherever sums of
real-valued norms or nondegeneracy require it. -/
def measuredNorm (μ : Measure X) (f : X → ℂ) : ℝ :=
  Real.sqrt ((∫⁻ x, squareMagnitude f x ∂μ).toReal)

/-- Restrict the given measure, then normalize by its actual mass. -/
def normalizedRestriction (μ : Measure X) (S : Set X) : Measure X :=
  (μ S)⁻¹ • μ.restrict S

/-- No independent scalar is chosen for the component mass. -/
def componentMass (μ : Measure X) (S : Set X) : ℝ := (μ S).toReal

theorem componentMass_nonneg (μ : Measure X) (S : Set X) :
    0 ≤ componentMass μ S := ENNReal.toReal_nonneg

/-- Probability normalization supplies the actual component-mass bound. -/
theorem componentMass_le_one (μ : Measure X) [IsProbabilityMeasure μ] (S : Set X) :
    componentMass μ S ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    rw [ENNReal.ofReal_one]
    exact prob_le_one)

theorem measuredNorm_nonneg (μ : Measure X) (f : X → ℂ) :
    0 ≤ measuredNorm μ f := Real.sqrt_nonneg _

theorem measuredNorm_sq (μ : Measure X) (f : X → ℂ) :
    measuredNorm μ f ^ 2 = (∫⁻ x, squareMagnitude f x ∂μ).toReal :=
  Real.sq_sqrt ENNReal.toReal_nonneg

theorem squareMagnitude_support {f : X → ℂ} {S : Set X}
    (hf : Function.support f ⊆ S) : Function.support (squareMagnitude f) ⊆ S := by
  intro x hx
  apply hf
  intro h0
  apply hx
  simp [squareMagnitude, h0]

/-- Measured normalization is proved directly from restriction. The zero-mass
case is included and the original integral is retained. -/
theorem mass_mul_normalizedNorm_sq (μ : Measure X) [IsFiniteMeasure μ]
    (S : Set X) (f : X → ℂ) (hf : Function.support f ⊆ S) :
    componentMass μ S * measuredNorm (normalizedRestriction μ S) f ^ 2 =
      measuredNorm μ f ^ 2 := by
  rw [measuredNorm_sq, measuredNorm_sq]
  unfold normalizedRestriction componentMass
  have key := setLIntegral_eq_of_support_subset (μ := μ) (squareMagnitude_support hf)
  rw [lintegral_smul_measure, key]
  by_cases h0 : μ S = 0
  · have hI : ∫⁻ x, squareMagnitude f x ∂μ = 0 := by
      rw [← key, Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]
    simp [h0, hI]
  · have ha : (μ S).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨h0, measure_ne_top _ _⟩
    rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
    field_simp

/-- The exact norm factor is the inverse square root of the measured mass. -/
theorem normalizedNorm_eq (μ : Measure X) [IsFiniteMeasure μ]
    (S : Set X) (f : X → ℂ) (hf : Function.support f ⊆ S)
    (hm : 0 < componentMass μ S) :
    measuredNorm (normalizedRestriction μ S) f =
      (Real.sqrt (componentMass μ S))⁻¹ * measuredNorm μ f := by
  have h1 := mass_mul_normalizedNorm_sq μ S f hf
  have hs := Real.sqrt_pos.2 hm
  have h2 : measuredNorm μ f = Real.sqrt (componentMass μ S) *
      measuredNorm (normalizedRestriction μ S) f := by
    rw [← sq_eq_sq₀ (measuredNorm_nonneg μ f)
      (mul_nonneg hs.le (measuredNorm_nonneg _ _)), mul_pow, Real.sq_sqrt hm.le]
    exact h1.symm
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

/-- Disjoint component supports prove the original square-integral decomposition,
without a supplied orthogonality identity. -/
theorem lintegral_squareMagnitude_sum {ι : Type} [Fintype ι]
    (μ : Measure X) (S : ι → Set X) (hS : ∀ i, NullMeasurableSet (S i) μ)
    (hdisj : Pairwise (Function.onFun Disjoint S))
    (f : ι → X → ℂ) (hf : ∀ i, Function.support (f i) ⊆ S i) :
    ∫⁻ x, squareMagnitude (∑ i, f i) x ∂μ =
      ∑ i, ∫⁻ x, squareMagnitude (f i) x ∂μ := by
  classical
  have hpt : ∀ i, ∀ x ∈ S i, squareMagnitude (∑ j, f j) x = squareMagnitude (f i) x := by
    intro i x hx
    have he : (∑ j, f j) x = f i x := by
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · intro j _ hji
        by_contra h0
        exact Set.disjoint_left.1 (hdisj hji) (hf j h0) hx
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    simp only [squareMagnitude, he]
  have hsupp : Function.support (squareMagnitude (∑ i, f i)) ⊆ ⋃ i, S i := by
    intro x hx
    by_contra hn
    simp only [Set.mem_iUnion, not_exists] at hn
    apply hx
    have he : (∑ i, f i) x = 0 := by
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_contra h0
      exact hn i (hf i h0)
    simp [squareMagnitude, he]
  rw [← setLIntegral_eq_of_support_subset hsupp,
    lintegral_iUnion₀ hS (fun i j hij => (hdisj hij).aedisjoint), tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← setLIntegral_eq_of_support_subset (squareMagnitude_support (hf i))]
  exact lintegral_congr_ae ((ae_restrict_mem₀ (hS i)).mono fun x hx => hpt i x hx)

theorem measuredNorm_sum_sq {ι : Type} [Fintype ι]
    (μ : Measure X) (S : ι → Set X) (hS : ∀ i, NullMeasurableSet (S i) μ)
    (hdisj : Pairwise (Function.onFun Disjoint S))
    (f : ι → X → ℂ) (hf : ∀ i, Function.support (f i) ⊆ S i)
    (hfinite : ∀ i, ∫⁻ x, squareMagnitude (f i) x ∂μ ≠ ⊤) :
    measuredNorm μ (∑ i, f i) ^ 2 = ∑ i, measuredNorm μ (f i) ^ 2 := by
  rw [measuredNorm_sq, lintegral_squareMagnitude_sum μ S hS hdisj f hf,
    ENNReal.toReal_sum (fun i _ => hfinite i)]
  exact Finset.sum_congr rfl fun i _ => (measuredNorm_sq μ (f i)).symm

open RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt

section Nondegeneracy

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

/-- The original all-place Gram norm is nondegenerate at each infinite place. -/
theorem eq_zero_of_hasGram_norm_zero {N : (K →+* ℂ) → V → ℝ}
    (h : HasGram N) (v : InfinitePlace K) {x : V} (hx : N v.embedding x = 0) :
    x = 0 := by
  obtain ⟨n, ⟨b, M⟩, hM⟩ := h
  dsimp only at hM
  have h0 := (hM v).2 x
  rw [hx] at h0
  have h1 : ∑ i, ‖RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord b M v x i‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h0
  have h2 : RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord b M v x = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h1 i (Finset.mem_univ i)
    simpa using this
  have h3 : RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.vecAt b v x = 0 := by
    have := congrArg (M v).mulVec h2
    simpa only [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.fcoord,
      mulVec_mulVec, Matrix.mul_nonsing_inv _ (hM v).1, one_mulVec, mulVec_zero] using this
  apply b.repr.map_eq_zero_iff.1
  ext i
  have := congrFun h3 i
  simpa [RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory.vecAt] using this

theorem hasGram_pos {N : (K →+* ℂ) → V → ℝ} (h : HasGram N)
    (hn : ∀ σ x, 0 ≤ N σ x)
    (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    {x : V} (hx : x ≠ 0) (σ : K →+* ℂ) : 0 < N σ x := by
  have e : N σ x = N (InfinitePlace.mk σ).embedding x := by
    rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · rw [h1]
    · have hconj : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun a => ComplexEmbedding.conjugate_coe_eq σ a
      rw [h1, hconj, hc]
  rw [e]
  exact lt_of_le_of_ne (hn _ _) fun h0 =>
    hx (eq_zero_of_hasGram_norm_zero h _ h0.symm)

end Nondegeneracy

section Degree

variable {K V : Type} [Field K] [NumberField K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (μ : (K →+* ℂ) → Measure X) [∀ σ, IsFiniteMeasure (μ σ)]
  (S : (K →+* ℂ) → Set X) (F : (K →+* ℂ) → V → X → ℂ)

/-- Global restricted norm of the same component functions. -/
def restrictionNorm (σ : K →+* ℂ) (f : V) : ℝ := measuredNorm (μ σ) (F σ f)

/-- Component probability norm of the same functions. -/
def componentNorm (σ : K →+* ℂ) (f : V) : ℝ :=
  measuredNorm (normalizedRestriction (μ σ) (S σ)) (F σ f)

/-- A nonzero component lattice forces positive measured mass, because a
zero-mass component would annihilate its actual positive Gram norm. -/
theorem componentMass_pos_of_rank
    (hG : HasGram (restrictionNorm μ F))
    (hc : ∀ σ f, restrictionNorm μ F ((starRingEnd ℂ).comp σ) f = restrictionNorm μ F σ f)
    (hs : ∀ σ f, Function.support (F σ f) ⊆ S σ)
    (L : Submodule (𝓞 K) V)
    (hr : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L ≠ 0)
    (σ : K →+* ℂ) : 0 < componentMass (μ σ) (S σ) := by
  have hL : L ≠ ⊥ := fun h0 => hr (by simp [h0,
    RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK])
  obtain ⟨f, _, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  have hp := hasGram_pos hG (fun _ _ => measuredNorm_nonneg _ _) hc hf σ
  have h1 := mass_mul_normalizedNorm_sq (μ σ) (S σ) (F σ f) (hs σ f)
  refine lt_of_le_of_ne ENNReal.toReal_nonneg fun h0 => ?_
  rw [← h0, zero_mul] at h1
  exact hp.ne' ((pow_eq_zero_iff two_ne_zero).1 h1.symm)

/-- Exact measured arithmetic-degree comparison, on the original integral
lattice, including its zero-rank case. The mass is computed by the measure,
and the norm-rescaling formula is proved by restriction above. -/
theorem degree_eq_componentDegree_sub_mass
    (hG : HasGram (restrictionNorm μ F))
    (hc : ∀ σ f, restrictionNorm μ F ((starRingEnd ℂ).comp σ) f = restrictionNorm μ F σ f)
    (hm : ∀ σ, componentMass (μ ((starRingEnd ℂ).comp σ)) (S ((starRingEnd ℂ).comp σ)) =
      componentMass (μ σ) (S σ))
    (hs : ∀ σ f, Function.support (F σ f) ⊆ S σ)
    (L : Submodule (𝓞 K) V) (hL : L.FG) :
    deg (restrictionNorm μ F) L = deg (componentNorm μ S F) L -
      (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L : ℝ) / 2 *
        ((∑ σ : K →+* ℂ, Real.log (componentMass (μ σ) (S σ))) /
          (Module.finrank ℚ K : ℝ)) := by
  by_cases hr : RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK L = 0
  · simp [deg, hr]
  · have hpos := componentMass_pos_of_rank μ S F hG hc hs L hr
    have hsc := (NativeMeasuredComponentDegree.degree_scale K V
      (restrictionNorm μ F) (componentNorm μ S F)
      (fun σ => (Real.sqrt (componentMass (μ σ) (S σ)))⁻¹) hG
      (fun σ => inv_pos.2 (Real.sqrt_pos.2 (hpos σ)))
      (fun σ => congrArg (fun m => (Real.sqrt m)⁻¹) (hm σ))
      (fun σ f => normalizedNorm_eq (μ σ) (S σ) (F σ f) (hs σ f) (hpos σ))).2 L hL
    have hl : ∀ σ, Real.log (Real.sqrt (componentMass (μ σ) (S σ)))⁻¹ =
        -(Real.log (componentMass (μ σ) (S σ)) / 2) := fun σ => by
      rw [Real.log_inv, Real.log_sqrt ENNReal.toReal_nonneg]
    simp only [hl, Finset.sum_neg_distrib, ← Finset.sum_div] at hsc
    rw [hsc]
    ring

end Degree

section Ranks

variable {K V ι : Type} [Field K] [NumberField K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι]

/-- The rank and degree of the actual sum of integral component lattices.
Orthogonality is supplied by disjoint measured supports of the realized
functions; no numerical rank or degree decomposition is an input. -/
theorem rank_degree_iSup_of_measured_supports
    (μ : (K →+* ℂ) → Measure X) (F : ∀ σ : K →+* ℂ, V →ₛₗ[σ] (X → ℂ))
    (S : (K →+* ℂ) → ι → Set X) (M : ι → Submodule (𝓞 K) V)
    (hG : HasGram (fun σ f => measuredNorm (μ σ) (F σ f)))
    (hM : ∀ i, (M i).FG)
    (hS : ∀ σ i, NullMeasurableSet (S σ i) (μ σ))
    (hdisj : ∀ σ, Pairwise (Function.onFun Disjoint (S σ)))
    (hs : ∀ σ i f, f ∈ Submodule.span K (M i : Set V) →
      Function.support (F σ f) ⊆ S σ i)
    (hfinite : ∀ σ i f, f ∈ Submodule.span K (M i : Set V) →
      ∫⁻ x, squareMagnitude (F σ f) x ∂μ σ ≠ ⊤) :
    RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (⨆ i, M i) =
        ∑ i, RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (M i) ∧
      deg (fun σ f => measuredNorm (μ σ) (F σ f)) (⨆ i, M i) =
        ∑ i, deg (fun σ f => measuredNorm (μ σ) (F σ f)) (M i) := by
  apply NativeMeasuredComponentDegree.OrthogonalSum.rkK_deg_iSup K V ι
    (fun σ f => measuredNorm (μ σ) (F σ f)) M hG hM
  intro σ f hf
  rw [map_sum]
  exact measuredNorm_sum_sq (μ σ) (S σ) (hS σ) (hdisj σ)
    (fun i => F σ (f i)) (fun i => hs σ i (f i) (hf i))
    (fun i => hfinite σ i (f i) (hf i))

end Ranks

section Decomposition

variable {K V ι : Type} [Field K] [NumberField K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι]

/-- The combined measured component identity, with the actual component
inclusions and their original integral lattices. Rank is invariant under each
inclusion, the global degree is the sum of restricted degrees, and each
restricted degree has its measured logarithmic mass correction. No numerical
rank identity, orthogonality identity, or degree decomposition is assumed. -/
theorem rank_degree_iSup_with_measured_masses
    (W : ι → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, Module (𝓞 K) (W i)] [∀ i, IsScalarTower (𝓞 K) K (W i)]
    (μ : (K →+* ℂ) → Measure X) [∀ σ, IsFiniteMeasure (μ σ)]
    (F : ∀ σ : K →+* ℂ, V →ₛₗ[σ] (X → ℂ))
    (φ : ∀ i, W i →ₗ[K] V) (hφ : ∀ i, Function.Injective (φ i))
    (S : (K →+* ℂ) → ι → Set X) (L : ∀ i, Submodule (𝓞 K) (W i))
    (hG : HasGram (fun σ f => measuredNorm (μ σ) (F σ f)))
    (hL : ∀ i, (L i).FG)
    (hc : ∀ σ f, measuredNorm (μ ((starRingEnd ℂ).comp σ))
        (F ((starRingEnd ℂ).comp σ) f) = measuredNorm (μ σ) (F σ f))
    (hm : ∀ i σ, componentMass (μ ((starRingEnd ℂ).comp σ))
        (S ((starRingEnd ℂ).comp σ) i) = componentMass (μ σ) (S σ i))
    (hS : ∀ σ i, NullMeasurableSet (S σ i) (μ σ))
    (hdisj : ∀ σ, Pairwise (Function.onFun Disjoint (S σ)))
    (hs : ∀ σ i (f : W i), Function.support (F σ (φ i f)) ⊆ S σ i)
    (hfinite : ∀ σ i (f : W i),
      ∫⁻ x, squareMagnitude (F σ (φ i f)) x ∂μ σ ≠ ⊤) :
    RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK
        (⨆ i, (L i).map ((φ i).restrictScalars (𝓞 K))) =
        ∑ i, RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (L i) ∧
      deg (fun σ f => measuredNorm (μ σ) (F σ f))
          (⨆ i, (L i).map ((φ i).restrictScalars (𝓞 K))) =
        ∑ i, (deg (componentNorm μ (fun σ => S σ i)
            (fun σ f => F σ (φ i f))) (L i) -
          (RHLean.Geometry.AlpogeAllPlace.Formalism.HN.rkK (L i) : ℝ) / 2 *
            ((∑ σ : K →+* ℂ, Real.log (componentMass (μ σ) (S σ i))) /
              (Module.finrank ℚ K : ℝ))) := by
  let N : (K →+* ℂ) → V → ℝ := fun σ f => measuredNorm (μ σ) (F σ f)
  let M : ι → Submodule (𝓞 K) V := fun i => (L i).map ((φ i).restrictScalars (𝓞 K))
  have hrd := fun i => NativeMeasuredComponentDegree.Restriction.restrict_deg
    K V (W i) N (φ i) (hφ i) hG
  have hspan : ∀ i, Submodule.span K (M i : Set V) ≤ LinearMap.range (φ i) := by
    intro i
    refine Submodule.span_le.2 ?_
    rintro y ⟨f, _, rfl⟩
    exact (φ i).mem_range_self f
  have hs' : ∀ σ i f, f ∈ Submodule.span K (M i : Set V) →
      Function.support (F σ f) ⊆ S σ i := by
    intro σ i f hf
    obtain ⟨g, rfl⟩ := hspan i hf
    exact hs σ i g
  have hf' : ∀ σ i f, f ∈ Submodule.span K (M i : Set V) →
      ∫⁻ x, squareMagnitude (F σ f) x ∂μ σ ≠ ⊤ := by
    intro σ i f hf
    obtain ⟨g, rfl⟩ := hspan i hf
    exact hfinite σ i g
  obtain ⟨hr, hd⟩ := rank_degree_iSup_of_measured_supports μ F S M hG
    (fun i => (hL i).map _) hS hdisj hs' hf'
  refine ⟨hr.trans (Finset.sum_congr rfl fun i _ => ((hrd i).2 (L i) (hL i)).1), ?_⟩
  rw [hd]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [((hrd i).2 (L i) (hL i)).2]
  exact degree_eq_componentDegree_sub_mass μ (fun σ => S σ i)
    (fun σ f => F σ (φ i f)) (hrd i).1
    (fun σ f => hc σ (φ i f)) (hm i) (fun σ f => hs σ i f) (L i) (hL i)

end Decomposition

end RHLean.Geometry.NativeMeasuredComponentNorm

end
