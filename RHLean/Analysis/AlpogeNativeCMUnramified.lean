import RHLean.Analysis.AlpogeNativeHostPrimes

/-!
# The native CM host is unramified over its maximal real subfield

The actual prime-ideal calculation is promoted to the exact algebraic
unramifiedness class required by the original geometric host. A local
integral element separated from its conjugate generates the quadratic
extension. Its minimal-polynomial derivative lies in the relative different
and avoids the selected prime. No unramifiedness or different-ideal bound is
assumed for the native field.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/LocalToGlobal/ProjectiveLattices/UnramBridgeHolds.lean`,
`Formalism.L2.Pj.unramBridge_holds`; the supplier interface is
`HalfOneAddSqrtNegIsIntegral.lean`, `Formalism.L2.Pj.cmUnram_conj`.
Here that supplier is proved from the actual native cyclotomic prime-ideal
inertia result, with the same field and original conductor. The source
archive/mirror states no license; this notice preserves attribution without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Polynomial
open scoped Pointwise

namespace RHLean.Analysis.NativeCMUnramified

attribute [local instance] FractionRing.liftAlgebra

theorem unramified_of_conjugation_separates : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    (∀ P : Ideal (𝓞 K), P.IsMaximal → ∃ θ : 𝓞 K,
      θ - RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ ∉ P) →
    Algebra.Unramified (𝓞 (maximalRealSubfield K)) (𝓞 K) := by
  intro K _ _ _ hθ
  let F := maximalRealSubfield K
  let _ : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 K)) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (𝓞 F) F).symm.toRingEquiv
          (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 F) F).symm
      (FractionRing.algEquiv (𝓞 K) K).symm _
  rw [Algebra.unramified_iff_forall]
  rintro ⟨Q, hQ⟩
  let : Q.IsPrime := hQ
  change Algebra.IsUnramifiedAt (𝓞 F) Q
  rcases eq_or_ne Q ⊥ with rfl | hne
  · exact Algebra.isUnramifiedAt_bot
  have hmax : Q.IsMaximal := hQ.isMaximal hne
  obtain ⟨θ, hθP⟩ := hθ Q hmax
  set θ' := RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ with hθ'
  have hσ : θ' = IsCMField.ringOfIntegersComplexConj K θ := RingOfIntegers.ext rfl
  have hne' : θ - θ' ≠ 0 := fun h => hθP (h ▸ Ideal.zero_mem _)

  have hnotF : (θ : K) ∉ F := by
    intro hm
    apply hne'
    rw [sub_eq_zero, hσ]
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    exact ((IsCMField.complexConj_eq_self_iff K _).mpr hm).symm

  have hfin : Module.finrank F K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F K
  have hint : IsIntegral F (θ : K) := Algebra.IsIntegral.isIntegral _
  have hadj : Algebra.adjoin F {algebraMap (𝓞 K) K θ} = ⊤ := by
    have : IsSimpleOrder (IntermediateField F K) :=
      IntermediateField.isSimpleOrder_of_finrank_prime F K (hfin ▸ Nat.prime_two)
    rcases eq_bot_or_eq_top (IntermediateField.adjoin F {(θ : K)}) with h | h
    · exfalso
      rw [IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot] at h
      obtain ⟨y, hy⟩ := h
      exact hnotF (hy ▸ y.2)
    · rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
      change (IntermediateField.adjoin F {(θ : K)}).toSubalgebra = ⊤
      rw [h, IntermediateField.top_toSubalgebra]
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 F) F K θ hadj

  set f := minpoly (𝓞 F) θ with hf
  have hθint : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral _
  have hmonic : f.Monic := minpoly.monic hθint
  have hdeg : f.natDegree ≤ 2 := by
    have h1 : f = minpoly (𝓞 F) (algebraMap (𝓞 K) K θ) :=
      (minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K) K) θ).symm
    have h2 := minpoly.isIntegrallyClosed_eq_field_fractions' F
      (IsIntegral.algebraMap hθint : IsIntegral (𝓞 F) (algebraMap (𝓞 K) K θ))
    have h3 : (minpoly F (algebraMap (𝓞 K) K θ)).natDegree ≤ 2 :=
      hfin ▸ minpoly.natDegree_le _
    rw [h2, Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h3
    rw [h1]; exact h3
  set fK := f.map (algebraMap (𝓞 F) (𝓞 K)) with hfK
  have hKmonic : fK.Monic := hmonic.map _
  have hKdeg : fK.natDegree ≤ 2 := by
    rw [hfK, hmonic.natDegree_map]; exact hdeg
  have hr1 : fK.IsRoot θ := by
    rw [IsRoot, hfK, eval_map, ← aeval_def]; exact minpoly.aeval _ _
  have hr2 : fK.IsRoot θ' := by
    rw [IsRoot, hfK, eval_map, ← aeval_def, hσ]
    rw [show IsCMField.ringOfIntegersComplexConj K θ = (IsCMField.ringOfIntegersComplexConj K).toAlgHom θ from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  set g := fK /ₘ (X - C θ) with hg
  have hfg : (X - C θ) * g = fK := (mul_divByMonic_eq_iff_isRoot).mpr hr1
  have hg2 : g.IsRoot θ' := by
    have := hr2
    rw [← hfg, IsRoot, eval_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exfalso; apply hne'; simp at h; rw [sub_eq_zero] at h ⊢; exact h.symm
    · exact h
  set h := g /ₘ (X - C θ') with hh
  have hgh : (X - C θ') * h = g := (mul_divByMonic_eq_iff_isRoot).mpr hg2
  have hfac : fK = (X - C θ) * ((X - C θ') * h) := by rw [hgh, hfg]
  have hhmonic : h.Monic := by
    have hm2 : ((X - C θ) * (X - C θ')).Monic := (monic_X_sub_C θ).mul (monic_X_sub_C θ')
    rw [hfac, ← mul_assoc] at hKmonic
    exact hm2.of_mul_monic_left hKmonic
  have hh1 : h = 1 := by
    rw [← hhmonic.natDegree_eq_zero]
    have := hKdeg
    rw [hfac, natDegree_mul (X_sub_C_ne_zero θ) (mul_ne_zero (X_sub_C_ne_zero θ') hhmonic.ne_zero),
      natDegree_mul (X_sub_C_ne_zero θ') hhmonic.ne_zero, natDegree_X_sub_C, natDegree_X_sub_C] at this
    omega
  have hval : aeval θ (derivative f) = θ - θ' := by
    rw [aeval_def, ← eval_map, ← derivative_map, ← hfK, hfac, hh1]
    simp [derivative_mul]
  rw [← not_dvd_differentIdeal_iff, Ideal.dvd_iff_le]
  intro hle
  exact hθP (hle (hval ▸ hmem))

end RHLean.Analysis.NativeCMUnramified

namespace RHLean.Analysis

/-- The canonical CM conjugation and the constructed native conjugation
are the same map, independently of the presentation of the CM instance. -/
theorem alpogeNativeHostConj_complexConj
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    [IsCMField (alpogeNativeHostField e q d)]
    (x : alpogeNativeHostField e q d) :
    IsCMField.complexConj (alpogeNativeHostField e q d) x =
      alpogeNativeHostConj e q d x := by
  let ψ : alpogeNativeHostField e q d →+* ℂ := Classical.choice inferInstance
  apply ψ.injective
  exact (IsCMField.complexEmbedding_complexConj
    (alpogeNativeHostField e q d) ψ x).trans
      (alpogeNativeHostConj_apply e q d ψ x).symm

/-- The exact unramifiedness class required by the geometric host, on the
actual native fixed field and its actual maximal real subfield. -/
theorem alpogeNativeHostField_unramified
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    Algebra.Unramified (𝓞 (maximalRealSubfield (alpogeNativeHostField e q d)))
      (𝓞 (alpogeNativeHostField e q d)) := by
  let : IsCMField (alpogeNativeHostField e q d) :=
    alpogeNativeHostField_isCMField e q d hq2 hd2 hqd hq4 hd4
  apply NativeCMUnramified.unramified_of_conjugation_separates (alpogeNativeHostField e q d)
  intro P hP
  let : P.IsMaximal := hP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP
    (RingOfIntegers.not_isField (alpogeNativeHostField e q d))
  have hnot := alpogeNativeHostConj_unramEF e q d hq2 hd2 hqd hq4 hd4 P hP.isPrime hP0
  push_neg at hnot
  obtain ⟨θ, hθ⟩ := hnot
  have hconj :
      RingOfIntegers.mapRingEquiv
        (IsCMField.complexConj (alpogeNativeHostField e q d) :
          alpogeNativeHostField e q d ≃+* alpogeNativeHostField e q d) θ =
      alpogeNativeHostConj e q d • θ := by
    apply RingOfIntegers.ext
    exact alpogeNativeHostConj_complexConj e q d θ
  refine ⟨θ, fun hmem => hθ ?_⟩
  simpa only [hconj, neg_sub] using P.neg_mem hmem

end RHLean.Analysis

end
