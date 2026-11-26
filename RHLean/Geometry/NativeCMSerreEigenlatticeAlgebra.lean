import RHLean.Geometry.NativeCMSerreTensor

/-!
# The algebraic coordinate criterion for the actual Serre eigenlattice

The source's self-dual-coordinate lemma is used only after its pairing and
dual frame have been constructed on the literal inverse half-different.
The quadratic-order form is identified with the sum of x * conjugate(y)
over the actual host automorphisms fixing its quadratic root. Thus its
rank-one coefficient is exactly one, without replacing the projective
module or choosing a metric.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/
SingleMemSpanIffOfSelfDual.lean, TwoMulDegreeEigenLatticeTensorRankOne.lean
(`span_embeddings_eq_top`), and ExistsFractionalIdealTraceFormRankOne.lean
(`RankOne.relTrace_eq`). The archive states no license; attribution is
retained without assigning one. No scheme or Lie metric is assumed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical BigOperators Pointwise nonZeroDivisors TensorProduct

namespace RHLean.Geometry.NativeCM.SerreEigenlattice

/-- A perfect pairing with a finite dual frame detects the integral
coordinate axis inside the integral span, including its entire index. -/
theorem single_mem_span_iff_of_pairing
    (O R K L I : Type) [CommRing O] [CommRing R] [Field K] [Algebra R K]
    [Fintype I] [DecidableEq I] (τ₀ : O →+* R) (h : L → L → O)
    (ev dv : L → I → K) (n : ℕ) (x y : Fin n → L)
    (hh : ∀ a b, algebraMap R K (τ₀ (h a b)) = ∑ i, ev a i * dv b i)
    (hev : ∀ a, ev a = ∑ m, algebraMap R K (τ₀ (h a (y m))) • ev (x m))
    (hspan : Submodule.span K (Set.range ev) = ⊤) (i : I) (t : K) :
    Pi.single i t ∈ Submodule.span R (Set.range ev) ↔
      ∀ b, t * dv b i ∈ (algebraMap R K).range := by
  have hsum : ∀ b, ∑ j, (Pi.single i t : I → K) j * dv b j = t * dv b i := by
    intro b
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  constructor
  · intro hm b
    rw [← hsum b]
    generalize (Pi.single i t : I → K) = v at hm
    induction hm using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      exact ⟨_, hh a b⟩
    | zero => simp
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      exact add_mem hu hw
    | smul r u _ hu =>
      have he : ∑ j, (r • u) j * dv b j =
          algebraMap R K r * ∑ j, u j * dv b j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by
          rw [Pi.smul_apply, Algebra.smul_def, mul_assoc]
      rw [he]
      exact mul_mem ⟨r, rfl⟩ hu
  · intro hb
    have key : ∀ v : I → K, v = ∑ m, (∑ j, v j * dv (y m) j) • ev (x m) := by
      intro v
      have hv : v ∈ Submodule.span K (Set.range ev) := hspan ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, rfl⟩ := hv
        simp only [← hh]
        exact hev a
      | zero => simp
      | add u w _ _ hu hw =>
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
        rw [← hu, ← hw]
      | smul r u _ hu =>
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum,
          mul_smul, ← Finset.smul_sum]
        rw [← hu]
    rw [key (Pi.single i t)]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [hsum]
    obtain ⟨r, hr⟩ := hb (y m)
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- Distinct field embeddings span all coordinate directions, even when
the coefficient ideal has no chosen free basis. -/
theorem span_embeddings_eq_top
    {E F M I : Type} [Field E] [NumberField E] [Field F]
    [AddCommGroup M] [Module (𝓞 E) M] [Fintype I]
    (σ : I → (E →+* F)) (hσ : Function.Injective σ)
    (e : M →ₗ[𝓞 E] E) (a₀ : M) (h₀ : e a₀ ≠ 0) :
    Submodule.span F (Set.range fun a i => σ i (e a)) = ⊤ := by
  refine span_flip_eq_top_iff_linearIndependent.2
    (?_ : LinearIndependent F fun i a => σ i (e a))
  have hinj : Function.Injective fun i =>
      ((σ i).comp (algebraMap (𝓞 E) E)).toMonoidHom := fun i j hij =>
    hσ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      (RingHom.ext fun a => DFunLike.congr_fun hij a))
  have hli := (linearIndependent_monoidHom (𝓞 E) F).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg i
  have hi := hli (fun i => g i * σ i (e a₀)) (funext fun s => by
    have hs := congrFun hg (s • a₀)
    simp only [Finset.sum_apply, Algebra.smul_def, Pi.zero_apply] at hs
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Function.comp]
    rw [← hs]
    exact Finset.sum_congr rfl fun i _ => by
      simp [Algebra.smul_def]
      ring) i
  exact (mul_eq_zero.1 hi).resolve_right ((map_ne_zero _).2 h₀)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/-- The actual automorphisms giving the pure quadratic character. -/
abbrev RootAut (G : NativeGeometricHost E) :=
  {σ : E ≃ₐ[ℚ] E // σ (G.rt : E) = (G.rt : E)}

def identityAut (G : NativeGeometricHost E) : RootAut G := ⟨1, rfl⟩

theorem rootAut_fix_order (G : NativeGeometricHost E) (σ : RootAut G) (a : OK G) :
    σ.1 ((a : 𝓞 E) : E) = ((a : 𝓞 E) : E) := by
  have hw : σ.1 (G.w0 : E) = (G.w0 : E) := by
    have h := congrArg (fun u : 𝓞 E => (u : E)) G.two_weight_eq_one_add_root
    have hs := congrArg σ.1 h
    simp only [map_mul, map_ofNat, map_add, map_one, σ.2] at hs
    exact mul_left_cancel₀ (by norm_num : (2 : E) ≠ 0) (hs.trans h.symm)
  obtain ⟨⟨m, n⟩, ha, -⟩ := existsUnique_coord G a
  rw [ha]
  simp [wK, hw]

/-- The quadratic trace projector, evaluated entirely in the same host.
Completeness of the automorphisms is supplied by the actual Galois host. -/
theorem relative_trace_root [IsGalois ℚ E] (G : NativeGeometricHost E) (z : E) :
    ((Algebra.trace ℚ E ((G.w0 : E) * z / G.rt) : ℚ) : E) -
        (Algebra.trace ℚ E (z / G.rt) : ℚ) +
        (Algebra.trace ℚ E (z / G.rt) : ℚ) * (G.w0 : E) =
      ∑ σ : RootAut G, σ.1 z := by
  have tr (t : E) : ((Algebra.trace ℚ E t : ℚ) : E) =
      ∑ σ : E ≃ₐ[ℚ] E, σ t := by
    simpa using trace_eq_sum_automorphisms (K := ℚ) t
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun σ : E ≃ₐ[ℚ] E => σ (G.rt : E) = (G.rt : E))
    (by simp) (fun σ : E ≃ₐ[ℚ] E => σ z), Finset.sum_filter,
    tr, tr, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hr : (G.rt : E) = 2 * (G.w0 : E) - 1 := by
    have h := congrArg (algebraMap (𝓞 E) E) (rt_eq G)
    simpa only [map_sub, map_mul, map_ofNat, map_one] using h
  have hsq : (G.rt : E) ^ 2 = -(G.d : E) := by
    have h := congrArg (algebraMap (𝓞 E) E) G.rt_sq
    simpa only [map_pow, map_neg, map_natCast] using h
  have h0 : σ (G.rt : E) ≠ 0 :=
    (map_ne_zero σ).2 (by exact_mod_cast rt_ne_zero G)
  have h3 : σ (G.rt : E) = 2 * σ (G.w0 : E) - 1 := by
    rw [hr, map_sub, map_mul, map_ofNat, map_one]
  have h2 : σ (G.rt : E) ^ 2 = -(G.d : E) := by
    rw [← map_pow, hsq, map_neg, map_natCast]
  simp only [map_div₀, map_mul]
  split_ifs with hσ
  · field_simp
    linear_combination (σ z / 2) * (-hσ - h3 - hr)
  · have h5 := (sq_eq_sq_iff_eq_or_eq_neg.1 (h2.trans hsq.symm)).resolve_left hσ
    field_simp
    linear_combination (σ z / 2) * (h5 - h3 - hr)

end RHLean.Geometry.NativeCM.SerreEigenlattice

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM RHLean.Geometry.NativeCM.SerreEigenlattice

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]

/-- The source rank-one trace coefficient is exactly beta=1 on the literal
native B^-1, rather than an unspecified positive multiplier. -/
theorem coefficient_kLin_sum
    (G : NativeGeometricHost H.E) (hroot : (G.rt : H.E) = H.sqd)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (x y : (coefficientIdeal H B : Submodule (𝓞 H.E) H.E)) :
    (((kLin (coefficientTraceLattice H G hbar B hB) 1 x y : OK G) : 𝓞 H.E) : H.E) =
      ∑ σ : RootAut G, σ.1 ((x : H.E) * H.conj (y : H.E)) := by
  set v : H.E := (((kLin (coefficientTraceLattice H G hbar B hB) 1 x y : OK G) :
    𝓞 H.E) : H.E)
  have := H.galois
  have hEF (u v : (coefficientIdeal H B : Submodule (𝓞 H.E) H.E)) :
      (integralTraceForm H B hB u v : H.E) =
        (Algebra.trace ℚ H.E ((u : H.E) * H.conj (v : H.E) / G.rt) : ℚ) := by
    have hc : H.conj (xi H * H.conj (u : H.E) * (v : H.E)) =
        (u : H.E) * H.conj (v : H.E) / G.rt := by
      rw [map_mul, map_mul, conj_xi, conj_conj, xi, ← hroot]
      ring
    have ht := congrArg (algebraMap ℚ H.E)
      (integralTraceForm_cast H B hB u v)
    rw [map_intCast] at ht
    rw [← Algebra.trace_eq_of_algEquiv H.conj, hc] at ht
    exact ht
  have hk := congrArg (algebraMap (𝓞 H.E) H.E)
    (coefficient_kFun_formula H G hbar B hB 1 x y)
  change v = _ at hk
  simp only [map_add, map_mul, map_sub, map_intCast, Units.val_one, one_mul, Int.cast_sub] at hk
  simp only [hEF] at hk
  change v =
    (Algebra.trace ℚ H.E (((G.w0 : H.E) * x) * H.conj (y : H.E) / G.rt) : ℚ) -
      (Algebra.trace ℚ H.E ((x : H.E) * H.conj (y : H.E) / G.rt) : ℚ) +
      (Algebra.trace ℚ H.E ((x : H.E) * H.conj (y : H.E) / G.rt) : ℚ) *
        (G.w0 : H.E) at hk
  rw [mul_assoc] at hk
  exact hk.trans (relative_trace_root G ((x : H.E) * H.conj (y : H.E)))

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
