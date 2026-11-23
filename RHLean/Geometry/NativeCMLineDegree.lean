import RHLean.Geometry.NativeMeasuredComponentDegree
import RHLean.Geometry.NativeCMFiniteDegreeCorrection

/-!
# Fractional-ideal line degree in the existing all-place normalization

The integral lattice remains the literal nonzero fractional ideal. Its norm
at an embedding is `sqrt (n σ) * ‖σ x‖`. We construct the existing all-place
Gram frame and compute the original `AllWt.deg`, including the exact finite
ideal norm and the full embedding mean of the explicit metric coefficients.
Conjugate embeddings have equal metric coefficients, as required by the
existing degree's infinite-place convention.

The native specialization uses the actual Serre coefficient ideal B^-1 and
its different twist B^-1 D = conjugate(B). It does not identify this lattice
with a scheme-theoretic Lie eigenspace or assign an arithmetic Lie metric.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/ReciprocityTheory/SemistableReduction/SemiDegCA.lean,
`absNorm_mul_relIndex_one`;
src/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean,
`ds_prod_embeddings_eq_norm` and `ds_sum_log_normSq_embeddings`;
src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/
OneMulConjFracOneEqInvDifferent.lean, `deg_lineHerm` and the finite part of
`two_mul_deg_lineHerm_different`. The source mirror states no license;
attribution is retained without assigning a new license.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module Matrix
open scoped nonZeroDivisors Pointwise BigOperators

namespace RHLean.Geometry.NativeCM.LineDegree

theorem absNorm_mul_relIndex_one {K : Type} [Field K] [NumberField K] (C : Submodule (𝓞 K) K)
    (hC : C.FG) (h1 : 1 ≤ C) :
    FractionalIdeal.absNorm
        (⟨C, FractionalIdeal.isFractional_of_fg hC⟩ : FractionalIdeal (𝓞 K)⁰ K) *
      ((1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup : ℚ) = 1 := by
  classical
  set I : FractionalIdeal (𝓞 K)⁰ K := ⟨C, FractionalIdeal.isFractional_of_fg hC⟩ with hIdef
  have hden := FractionalIdeal.den_mul_self_eq_num I
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  set J : Ideal (𝓞 K) := I.num with hJ
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero I.den.2
  have hdK : algebraMap (𝓞 K) K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.2
  let ι : 𝓞 K →+ K := (algebraMap (𝓞 K) K).toAddMonoidHom
  have hι : Function.Injective ι := IsFractionRing.injective (𝓞 K) K
  let μ : K →+ K := AddMonoidHom.mulLeft (algebraMap (𝓞 K) K d)
  have hμ : Function.Injective μ := mul_right_injective₀ hdK
  have hsm : ∀ y : K, (I.den : 𝓞 K) • y = μ y := fun y => by
    rw [Algebra.smul_def]
    rfl
  have hone : AddSubgroup.map μ (1 : Submodule (𝓞 K) K).toAddSubgroup =
      AddSubgroup.map ι (Ideal.span {d}).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_one,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      exact ⟨r * d, ⟨r, rfl⟩, by simp [μ, ι, mul_comm]⟩
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      exact ⟨algebraMap (𝓞 K) K r, ⟨r, rfl⟩, by simp [μ, ι, mul_comm]⟩
  have hCm : AddSubgroup.map μ C.toAddSubgroup = AddSubgroup.map ι J.toAddSubgroup := by
    ext x
    open Pointwise in
    have hx : x ∈ ((I.den : 𝓞 K) • (I : Submodule (𝓞 K) K)) ↔
        x ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← hden]
      exact Iff.rfl
    rw [Submodule.mem_map, Submodule.mem_smul_pointwise_iff_exists] at hx
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzx⟩ := hx.mp ⟨y, hy, hsm y⟩
      exact ⟨z, hz, hzx⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hx.mpr ⟨z, hz, rfl⟩
      exact ⟨y, hy, by rw [← hsm]; exact hyx⟩
  have hidx : (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup =
      (Ideal.span {d}).toAddSubgroup.relIndex J.toAddSubgroup := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hμ, hone, hCm,
      AddSubgroup.relIndex_map_map_of_injective _ _ hι]
  have hle : Ideal.span {d} ≤ J := by
    rw [Ideal.span_singleton_le_iff_mem]
    have h1C : (1 : K) ∈ C := h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
    have hm : algebraMap (𝓞 K) K d ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← hden]
      open Pointwise in
      show _ ∈ ((I.den : 𝓞 K) • (I : Submodule (𝓞 K) K))
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨1, h1C, by rw [hsm]; simp [μ]⟩
    obtain ⟨z, hz, hzd⟩ := Submodule.mem_map.mp hm
    have hzd' := hι hzd
    rw [hd, ← hzd']
    exact hz
  have htower := AddSubgroup.relIndex_mul_relIndex (Ideal.span {d}).toAddSubgroup
    J.toAddSubgroup ⊤ hle le_top
  rw [AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_right] at htower
  have hiJ : J.toAddSubgroup.index = Ideal.absNorm J := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, AddSubgroup.index_eq_card]
    rfl
  have hid : (Ideal.span {d}).toAddSubgroup.index = (Algebra.norm ℤ d).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      AddSubgroup.index_eq_card]
    rfl
  rw [hiJ, hid] at htower
  have hb : (Algebra.norm ℤ d).natAbs ≠ 0 := by
    rw [← Ideal.absNorm_span_singleton]
    intro h
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
    exact hd0 h
  have hbq : ((Algebra.norm ℤ d).natAbs : ℚ) ≠ 0 := by exact_mod_cast hb
  have hcast : ((|Algebra.norm ℤ d| : ℤ) : ℚ) = ((Algebra.norm ℤ d).natAbs : ℚ) := by
    simp [Nat.cast_natAbs, Int.cast_abs]
  rw [hidx, FractionalIdeal.absNorm_eq, hcast, div_mul_eq_mul_div, div_eq_one_iff_eq hbq]
  rw [mul_comm] at htower
  exact_mod_cast htower


section
variable {K : Type} [Field K] [NumberField K]

theorem ds_prod_embeddings_eq_norm (x : K) :
    ∏ σ : K →+* ℂ, σ x = algebraMap ℚ ℂ (Algebra.norm ℚ x) := by
  rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => by simp [RingHom.equivRatAlgHom_apply])

theorem ds_sum_log_normSq_embeddings (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log (Complex.normSq (σ x)) = 2 * Real.log |(Algebra.norm ℚ x : ℝ)| := by
  rw [← Real.log_prod (fun σ _ => (Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hx)).ne'),
    ← map_prod, ds_prod_embeddings_eq_norm]
  have hn : (Algebra.norm ℚ x : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx)
  rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.normSq_ofReal, Real.log_mul hn hn,
    Real.log_abs]
  ring


end

open RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt (IsGram HasGram slope_sq_eq)
open RHLean.Geometry.AlpogeAllPlace.Formalism.HermitianLatticesTheory
  (fcoord vecAt normAt cnorm majAt)
open RHLean.Geometry.AlpogeAllPlace.Formalism.HN (rkK nPl muDef gramPl)
open RHLean.Geometry.NativeMeasuredComponentDegree

section Frame

variable {K : Type} [Field K]

/-- The prescribed line norm on the original field, before restricting to
an integral fractional-ideal lattice. -/
def lineNorm (n : (K →+* ℂ) → ℝ) (σ : K →+* ℂ) (x : K) : ℝ :=
  Real.sqrt (n σ) * ‖σ x‖

private theorem line_fcoord (v : InfinitePlace K) (x : K) (i : Fin 1) :
    fcoord (Basis.singleton (Fin 1) K) (fun _ => 1) v x i = v.embedding x := by
  simp [fcoord, vecAt, Basis.singleton_repr]

private theorem line_isGram :
    IsGram (Basis.singleton (Fin 1) K) (fun _ => 1)
      (fun (σ : K →+* ℂ) (x : K) => ‖σ x‖) := by
  intro v
  refine ⟨by simp, fun x => ?_⟩
  simp only [normAt, cnorm, line_fcoord, Finset.univ_unique, Finset.sum_singleton]
  exact Real.sqrt_sq (norm_nonneg _)

private theorem line_gramdet (v : InfinitePlace K) (a : K) :
    (gramPl (Basis.singleton (Fin 1) K) (fun _ => 1) v (fun _ : Fin 1 => a)).det.re =
      Complex.normSq (v.embedding a) := by
  rw [gramPl, Matrix.det_fin_one]
  simp only [Matrix.of_apply, majAt, line_fcoord, Finset.univ_unique,
    Finset.sum_singleton, Complex.star_def]
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re, Complex.sq_norm]

end Frame

section Degree

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
/-- A nonzero fractional ideal spans its actual one-dimensional generic
fiber; no integral basis or principality is used. -/
theorem fractionalIdeal_rank (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    rkK (I : Submodule (𝓞 K) K) = 1 := by
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ I, a ≠ 0 := by
    simpa [FractionalIdeal.eq_zero_iff] using hI
  have hsp : Submodule.span K ((I : Submodule (𝓞 K) K) : Set K) = ⊤ := by
    apply top_unique
    intro x _
    have hm := (Submodule.span K ((I : Submodule (𝓞 K) K) : Set K)).smul_mem
      (x / a) (Submodule.subset_span ha)
    simpa only [smul_eq_mul, div_mul_cancel₀ x ha0] using hm
  rw [rkK, hsp, finrank_top, finrank_self]

/-- The relative index is computed from the norm of the literal fractional
ideal. This retains the original integral subgroup in the degree formula. -/
theorem log_relIndex_span_singleton (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (a : K) (ha : a ∈ I) (ha0 : a ≠ 0) :
    Real.log ((Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => a)).toAddSubgroup.relIndex
      (I : Submodule (𝓞 K) K).toAddSubgroup : ℝ) =
      Real.log |(Algebra.norm ℚ a : ℝ)| - Real.log (FractionalIdeal.absNorm I : ℝ) := by
  let J := FractionalIdeal.spanSingleton (𝓞 K)⁰ a⁻¹ * I
  have hm : ∀ x, x ∈ J ↔ a * x ∈ I := fun x => by
    rw [FractionalIdeal.mem_singleton_mul]
    exact ⟨fun ⟨y, hy, e⟩ => by rwa [e, mul_inv_cancel_left₀ ha0],
      fun h => ⟨_, h, by field_simp⟩⟩
  have h1 := absNorm_mul_relIndex_one (J : Submodule (𝓞 K) K)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl J)
    (Submodule.one_le.2 ((hm 1).2 (by simpa using ha)))
  have e1 : (1 : Submodule (𝓞 K) K).toAddSubgroup.map (AddMonoidHom.mulLeft a) =
      (Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => a)).toAddSubgroup := by
    ext x
    simp [Submodule.mem_span_singleton, Algebra.smul_def, mul_comm]
  have e2 : (J : Submodule (𝓞 K) K).toAddSubgroup.map (AddMonoidHom.mulLeft a) =
      (I : Submodule (𝓞 K) K).toAddSubgroup := by
    ext x
    refine ⟨?_, fun h => ⟨a⁻¹ * x, (hm _).2 (by rwa [mul_inv_cancel_left₀ ha0]),
      mul_inv_cancel_left₀ ha0 x⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact (hm y).1 hy
  rw [← AddSubgroup.relIndex_map_map_of_injective (f := AddMonoidHom.mulLeft a)
      _ _ (mul_right_injective₀ ha0), e1, e2] at h1
  change FractionalIdeal.absNorm J * _ = 1 at h1
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, Algebra.norm_inv, abs_inv] at h1
  have hN : Algebra.norm ℚ a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha0
  have hNI : FractionalIdeal.absNorm I ≠ 0 := (map_ne_zero _).2 hI
  have h2 := eq_inv_of_mul_eq_one_right h1
  have h3 := congrArg (fun q : ℚ => Real.log (q : ℝ)) h2
  simp only [Rat.cast_natCast, mul_inv, inv_inv, Rat.cast_mul, Rat.cast_inv,
    Rat.cast_abs] at h3
  rw [Real.log_mul (by simpa using hN) (by simpa using hNI), Real.log_inv] at h3
  simpa only [sub_eq_add_neg] using h3

variable [IsTotallyComplex K]

private theorem sum_log_normSq_places (a : K) (ha : a ≠ 0) :
    ∑ v : InfinitePlace K, Real.log (Complex.normSq (v.embedding a)) =
      Real.log |(Algebra.norm ℚ a : ℝ)| := by
  have hsum : ∑ σ : K →+* ℂ, Real.log (Complex.normSq (σ a)) =
      2 * ∑ v : InfinitePlace K, Real.log (Complex.normSq (v.embedding a)) := by
    rw [← embedding_sum_of_places K (fun v => Real.log (Complex.normSq (v.embedding a)))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      simp [ComplexEmbedding.conjugate_coe_eq]
  have hnorm := ds_sum_log_normSq_embeddings a ha
  linarith

/-- The existing all-place arithmetic degree of the actual fractional ideal
with its ordinary embedding norm. -/
theorem degree_baseNorm (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.deg
      (fun (σ : K →+* ℂ) (x : K) => ‖σ x‖) (I : Submodule (𝓞 K) K) =
      -Real.log (FractionalIdeal.absNorm I : ℝ) / (finrank ℚ K : ℝ) := by
  let : StarRing K := starRingOfComm
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ I, a ≠ 0 := by
    simpa [FractionalIdeal.eq_zero_iff] using hI
  have hfg := FractionalIdeal.fg_of_isNoetherianRing le_rfl I
  have hr := fractionalIdeal_rank I hI
  obtain ⟨-, -, hmu⟩ := rk_mul_mu_eq
    (Basis.singleton (Fin 1) K) (fun _ => 1) (fun _ => by simp)
    (fun _ : Fin 1 => a) (linearIndependent_unique_iff.mpr ha0)
    (I : Submodule (𝓞 K) K) hfg
    (Submodule.span_le.2 (Set.range_subset_iff.2 fun _ => ha)) hr
  simp only [Nat.cast_one, one_mul, line_gramdet] at hmu
  rw [log_relIndex_span_singleton I hI a ha ha0, sum_log_normSq_places a ha0] at hmu
  have hmu' : (nPl K : ℝ) * muDef (Basis.singleton (Fin 1) K) (fun _ => 1)
      (I : Submodule (𝓞 K) K) = -Real.log (FractionalIdeal.absNorm I : ℝ) := by
    linarith
  have hfin : (finrank ℚ K : ℝ) = 2 * nPl K := by
    have := embedding_sum_of_places K (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    rw [← NumberField.Embeddings.card K ℂ, this]
    rfl
  have hD : (finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (finrank_pos.ne' : finrank ℚ K ≠ 0)
  rw [RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.deg,
    RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.slope,
    slope_sq_eq line_isGram hfg, hr]
  simp only [Nat.cast_one, one_mul]
  apply (eq_div_iff hD).2
  rw [hfin]
  calc
    _ = (nPl K : ℝ) * muDef (Basis.singleton (Fin 1) K) (fun _ => 1)
        (I : Submodule (𝓞 K) K) := by ring
    _ = _ := hmu'

/-- The actual Gram frame exists for the prescribed positive line metric. -/
theorem lineNorm_hasGram (n : (K →+* ℂ) → ℝ) (hn : ∀ σ, 0 < n σ)
    (hc : ∀ σ, n ((starRingEnd ℂ).comp σ) = n σ) : HasGram (lineNorm n) :=
  (degree_scale K K (fun σ x => ‖σ x‖) (lineNorm n) (fun σ => Real.sqrt (n σ))
    line_isGram.hasGram (fun σ => Real.sqrt_pos.2 (hn σ))
    (fun σ => congrArg Real.sqrt (hc σ)) (fun _ _ => rfl)).1

/-- Exact line-degree formula in the original AllWt definition. Every
embedding appears in the metric correction and the integral fractional
ideal appears unchanged in the finite contribution. -/
theorem degree_lineNorm (n : (K →+* ℂ) → ℝ) (hn : ∀ σ, 0 < n σ)
    (hc : ∀ σ, n ((starRingEnd ℂ).comp σ) = n σ)
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.deg
      (lineNorm n) (I : Submodule (𝓞 K) K) =
      -Real.log (FractionalIdeal.absNorm I : ℝ) / (finrank ℚ K : ℝ) -
        (∑ σ : K →+* ℂ, Real.log (n σ)) / (2 * (finrank ℚ K : ℝ)) := by
  obtain ⟨-, hscale⟩ := degree_scale K K (fun σ x => ‖σ x‖) (lineNorm n)
    (fun σ => Real.sqrt (n σ)) line_isGram.hasGram (fun σ => Real.sqrt_pos.2 (hn σ))
    (fun σ => congrArg Real.sqrt (hc σ)) (fun _ _ => rfl)
  rw [hscale _ (FractionalIdeal.fg_of_isNoetherianRing le_rfl I),
    degree_baseNorm I hI, fractionalIdeal_rank I hI]
  simp only [Nat.cast_one, one_mul]
  rw [Finset.sum_congr rfl (fun σ _ => Real.log_sqrt (le_of_lt (hn σ))),
    ← Finset.sum_div]
  ring

end Degree

end RHLean.Geometry.NativeCM.LineDegree

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry.NativeCM.LineDegree

variable {φ : Frame} (H : HostRaw φ)

/-- The norm and different correction are now joined in the original
all-place degree of the actual coefficient ideal. The metric coefficients
remain explicit until the arithmetic Lie metric is constructed. -/
theorem coefficientDifferent_line_degree [IsTotallyComplex H.E]
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (n : (H.E →+* ℂ) → ℝ) (hn : ∀ σ, 0 < n σ)
    (hc : ∀ σ, n ((starRingEnd ℂ).comp σ) = n σ) :
    2 * RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.deg (lineNorm n)
        ((coefficientIdeal H B *
          (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E)) :
            Submodule (𝓞 H.E) H.E) =
      -(∑ σ : H.E →+* ℂ, Real.log (n σ)) / (finrank ℚ H.E : ℝ) +
        Real.log (rootDiscr H.K) - Real.log (rootDiscr H.E) := by
  have hI : coefficientIdeal H B *
      (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (halfDifferent_ne_zero H B hB).1)
      (FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot)
  rw [← FractionalIdeal.coe_mul, degree_lineNorm n hn hc _ hI]
  have hfinite := coefficientDifferent_degree_correction H B hB
  linear_combination hfinite

/-- The same exact degree holds on the extended integral ideal, ready for
an integral eigenlattice evaluation map whose image is this ideal. -/
theorem coefficientDifferent_extended_line_degree
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] [Algebra H.E L]
    (n : (L →+* ℂ) → ℝ) (hn : ∀ σ, 0 < n σ)
    (hc : ∀ σ, n ((starRingEnd ℂ).comp σ) = n σ) :
    2 * RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.deg (lineNorm n)
        ((FractionalIdeal.extendedHom L (𝓞 L) (coefficientIdeal H B *
          (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E))) :
            Submodule (𝓞 L) L) =
      -(∑ σ : L →+* ℂ, Real.log (n σ)) / (finrank ℚ L : ℝ) +
        Real.log (rootDiscr H.K) - Real.log (rootDiscr H.E) := by
  have hI : coefficientIdeal H B *
      (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (halfDifferent_ne_zero H B hB).1)
      (FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot)
  have hJ : FractionalIdeal.extendedHom L (𝓞 L) (coefficientIdeal H B *
      (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E)) ≠ 0 := by
    rwa [Ne, FractionalIdeal.extendedHom_eq_zero_iff]
  rw [degree_lineNorm n hn hc _ hJ]
  have hfinite := coefficientDifferent_baseChange_logNorm H B hB L
  linear_combination -hfinite

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization
