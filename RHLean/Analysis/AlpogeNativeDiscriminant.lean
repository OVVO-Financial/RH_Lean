import RHLean.Analysis.AlpogeNativeCMUnramified

/-!
# The actual native host's relative different and discriminant square

The native field is the already constructed CM fixed field. Its proved
unramified extension over its maximal real subfield forces the relative
different to be the unit ideal. The discriminant tower formula, the actual
degree and the discriminant sign then give the original square identity.
No discriminant or unramifiedness premise is supplied for this host.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/KcDiff.lean`, `Der.discr_sq`, and `CycBasic.lean`,
`Der.finrank_F`. The source archive/mirror states no license; this notice
retains attribution without assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

open NumberField IntermediateField Ideal

namespace RHLean.Analysis

attribute [local instance] FractionRing.liftAlgebra

/-- The maximal real subfield has exactly half the actual native degree. -/
theorem alpogeNativeHostReal_finrank
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    Module.finrank ℚ (maximalRealSubfield (alpogeNativeHostField e q d)) = 2 * 2 ^ e := by
  have : IsCMField (alpogeNativeHostField e q d) :=
    alpogeNativeHostField_isCMField e q d hq2 hd2 hqd hq4 hd4
  have h := Module.finrank_mul_finrank ℚ
    (maximalRealSubfield (alpogeNativeHostField e q d)) (alpogeNativeHostField e q d)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two,
    alpogeNativeHostField_finrank e q d hq2 hd2 hqd] at h
  omega

/-- The relative different is the unit ideal because the actual native
extension over its maximal real subfield is unramified. -/
theorem alpogeNativeHostField_different_eq_top
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    differentIdeal (𝓞 (maximalRealSubfield (alpogeNativeHostField e q d)))
      (𝓞 (alpogeNativeHostField e q d)) = ⊤ := by
  let E := alpogeNativeHostField e q d
  let F := maximalRealSubfield E
  have : IsCMField E := alpogeNativeHostField_isCMField e q d hq2 hd2 hqd hq4 hd4
  have : Algebra.Unramified (𝓞 F) (𝓞 E) :=
    alpogeNativeHostField_unramified e q d hq2 hd2 hqd hq4 hd4
  have : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 E)) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (𝓞 F) F).symm.toRingEquiv
      (FractionRing.algEquiv (𝓞 E) E).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 F) F).symm
      (FractionRing.algEquiv (𝓞 E) E).symm x
  change differentIdeal (𝓞 F) (𝓞 E) = ⊤
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have : P.IsMaximal := hP
  have hun : Algebra.IsUnramifiedAt (𝓞 F) P := inferInstance
  exact (not_dvd_differentIdeal_iff.mpr hun) (Ideal.dvd_iff_le.mpr hle)

/-- The original discriminant-square conclusion on the SAME native CM field. -/
theorem alpogeNativeHostField_discr_sq
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    discr (alpogeNativeHostField e q d) =
      discr (maximalRealSubfield (alpogeNativeHostField e q d)) ^ 2 := by
  let E := alpogeNativeHostField e q d
  let F := maximalRealSubfield E
  have : IsCMField E := alpogeNativeHostField_isCMField e q d hq2 hd2 hqd hq4 hd4
  have hdiff : differentIdeal (𝓞 F) (𝓞 E) = ⊤ :=
    alpogeNativeHostField_different_eq_top e q d hq2 hd2 hqd hq4 hd4
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [hdiff, Ideal.absNorm_top, one_mul, Algebra.IsQuadraticExtension.finrank_eq_two] at h
  have hsign : (discr E).sign = 1 := by
    rw [sign_discr]
    have h1 := IsTotallyComplex.finrank E
    have hE : Module.finrank ℚ E = 4 * 2 ^ e :=
      alpogeNativeHostField_finrank e q d hq2 hd2 hqd
    rw [hE] at h1
    have hplaces : InfinitePlace.nrComplexPlaces E = 2 * 2 ^ e := by omega
    rw [hplaces, pow_mul, neg_one_sq, one_pow]
  change discr E = discr F ^ 2
  rw [← Int.sign_mul_natAbs (discr E), hsign, one_mul, h, Nat.cast_pow, Int.natAbs_sq]

end RHLean.Analysis

end
