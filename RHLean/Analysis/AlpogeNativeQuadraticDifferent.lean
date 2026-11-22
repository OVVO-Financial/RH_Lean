import Mathlib

/-!
# The actual different of an imaginary quadratic field

The squarefree quadratic radicand determines the discriminant from the
integral pair 1,(1+x)/2. The derivative of the actual integral generator
puts x in the different, and equality of ideal norms gives the exact
principal different. No discriminant or different formula is assumed.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/DirichletDensity/DirichletDensityProofs/QuadDiscr.lean`,
`P.{quad_not_sq_rat,quadDiscr_ne_one}`; and
`src/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/`
`EqOfLeOfAbsNormEq.lean`, `HK.{eq_of_le_of_absNorm_eq,different_quad}`.
Only the actual quadratic arithmetic is reconstructed here, with Mathlib
as its sole dependency. The source archive/mirror states no license;
attribution is retained without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Polynomial Matrix

namespace RHLean.Analysis.NativeQuadraticDifferent

lemma not_sq_rat (a : ℤ) (ha : Squarefree a) (h1 : a ≠ 1) : ∀ b : ℚ, b ^ 2 ≠ (a : ℚ) := by
  intro b hb
  have hsq : IsSquare (a : ℚ) := ⟨b, by rw [← hb]; ring⟩
  obtain ⟨n, hn⟩ := Rat.isSquare_intCast_iff.1 hsq
  have hu : IsUnit n := ha n ⟨1, by rw [hn, mul_one]⟩
  rcases Int.isUnit_iff.1 hu with h | h <;> (subst h; simp at hn; exact h1 hn)

theorem discr_eq (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a)
    (h4 : a % 4 = 1) (h1 : a ≠ 1) : discr K = a := by
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have hint : IsIntegral ℚ x := .of_finite ℚ x
  have hrank : Module.finrank ℚ K = 2 := by
    have := IntermediateField.adjoin.finrank hint
    rw [hmin, natDegree_X_pow_sub_C, hadj, IntermediateField.finrank_top'] at this
    exact this
  have htrq : ∀ q : ℚ, Algebra.trace ℚ K (algebraMap ℚ K q) = 2 * q := by
    intro q
    rw [Algebra.trace_algebraMap, hrank]; simp
  have htrlin : ∀ (q : ℚ) (z : K), Algebra.trace ℚ K (algebraMap ℚ K q * z) =
      q * Algebra.trace ℚ K z := by
    intro q z
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have htrx : Algebra.trace ℚ K x = 0 := by
    have hnc : (X ^ 2 - C (a : ℚ)).nextCoeff = 0 := by
      rw [nextCoeff, natDegree_X_pow_sub_C, coeff_sub, coeff_X_pow, coeff_C]; norm_num
    rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin, hnc]; simp
  set ω : K := (1 + x) / 2 with hω
  have hω1 : ω = algebraMap ℚ K (1 / 2) + algebraMap ℚ K (1 / 2) * x := by
    rw [hω]; simp; ring
  have hω2 : ω * ω = algebraMap ℚ K ((1 + a) / 4) + algebraMap ℚ K (1 / 2) * x := by
    rw [hω]; simp; linear_combination (1 / 4 : K) * hx
  have htr1 : Algebra.trace ℚ K 1 = 2 := by
    rw [show (1 : K) = algebraMap ℚ K 1 by simp, htrq]; norm_num
  have htrω : Algebra.trace ℚ K ω = 1 := by
    rw [hω1, map_add, htrq, htrlin, htrx]; norm_num
  have htrωω : Algebra.trace ℚ K (ω * ω) = (1 + a) / 2 := by
    rw [hω2, map_add, htrq, htrlin, htrx]; ring
  have hdisc : Algebra.discr ℚ ![(1 : K), ω] = a := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, mul_one]
    rw [htr1, htrω, htrωω]; ring
  obtain ⟨c, hc⟩ : ∃ c : ℤ, a = 4 * c + 1 := ⟨a / 4, by omega⟩
  have hcK : (a : K) = 4 * c + 1 := by rw [hc]; push_cast; ring
  have hωint : IsIntegral ℤ ω := by
    refine ⟨X ^ 2 - X - C c, ?_, ?_⟩
    · monicity!
    · rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, algebraMap_int_eq, eq_intCast, hω]
      linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * hcK
  let B := RingOfIntegers.basis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← hrank, Module.finrank_eq_card_basis (integralBasis K)]
  let e := Fintype.equivFinOfCardEq hcard
  let B' : Module.Basis (Fin 2) ℤ (𝓞 K) := B.reindex e
  let Cb : Module.Basis (Fin 2) ℚ K := (integralBasis K).reindex e
  have hC : ∀ i, Cb i = ((B' i : 𝓞 K) : K) := by
    intro i; simp [Cb, B', B, integralBasis_apply]
  let ω' : 𝓞 K := ⟨ω, hωint⟩
  let v : Fin 2 → 𝓞 K := ![1, ω']
  let P : Matrix (Fin 2) (Fin 2) ℤ := B'.toMatrix v
  have hv : ![(1 : K), ω] = Cb ᵥ* (P.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ K) := by
    have h0 := B'.toMatrix_map_vecMul v
    funext j
    have hj := congrArg (fun w : Fin 2 → 𝓞 K => ((w j : 𝓞 K) : K)) h0
    have hvj : ((v j : 𝓞 K) : K) = ![(1 : K), ω] j := by
      fin_cases j <;> rfl
    rw [← hvj, ← hj]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hC, P]
  have key : (a : ℚ) = ((P.det : ℤ) : ℚ) ^ 2 * (discr K : ℚ) := by
    rw [← hdisc, hv, Algebra.discr_of_matrix_vecMul, coe_discr, Module.Basis.coe_reindex,
      Algebra.discr_reindex]
    congr 2
    exact (RingHom.map_det (Int.castRingHom ℚ) P).symm
  have key' : a = P.det ^ 2 * discr K := by exact_mod_cast key
  have hu : IsUnit P.det := hsf P.det ⟨discr K, by rw [key']; ring⟩
  rcases Int.isUnit_iff.1 hu with h | h <;> (rw [key', h]; ring)

theorem eq_of_le_of_absNorm_eq {K : Type*} [Field K] [NumberField K] {I J : Ideal (𝓞 K)}
    (hle : I ≤ J) (hI : Ideal.absNorm I ≠ 0) (h : Ideal.absNorm I = Ideal.absNorm J) : I = J := by
  obtain ⟨M, hM⟩ := Ideal.dvd_iff_le.mpr hle
  have h1 : Ideal.absNorm M = 1 := by
    have h2 := congrArg Ideal.absNorm hM
    rw [map_mul, ← h] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hI) (h2.symm.trans (mul_one _).symm)
  rw [Ideal.absNorm_eq_one_iff] at h1
  rw [hM, h1, Ideal.mul_top]

theorem different_eq_span_root (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a)
    (h4 : a % 4 = 1) (h1 : a ≠ 1) (x' : 𝓞 K) (hx' : (x' : K) = x) :
    differentIdeal ℤ (𝓞 K) = Ideal.span {x'} := by
  have hdisc : discr K = a := discr_eq K a x hx hadj hsf h4 h1
  have ha0 : a ≠ 0 := hsf.ne_zero
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have hrank : Module.finrank ℚ K = 2 := by
    have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) (.of_finite ℚ x)
    rw [hmin, natDegree_X_pow_sub_C, hadj, IntermediateField.finrank_top'] at this
    exact this
  obtain ⟨c, hc⟩ : ∃ c : ℤ, a = 4 * c + 1 := ⟨a / 4, by omega⟩
  have hcK : (a : K) = 4 * c + 1 := by rw [hc]; push_cast; ring
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω = (1 + x) / 2 := ⟨_, rfl⟩
  have hrelK : ω ^ 2 - ω - (c : K) = 0 := by
    rw [hω]
    linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * hcK
  have hωint : IsIntegral ℤ ω := by
    refine ⟨X ^ 2 - X - C c, by monicity!, ?_⟩
    rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, algebraMap_int_eq, eq_intCast]
    exact hrelK
  obtain ⟨ω', hω'⟩ : ∃ ω' : 𝓞 K, algebraMap (𝓞 K) K ω' = ω := ⟨⟨ω, hωint⟩, rfl⟩
  have hxω : x = 2 * ω - 1 := by rw [hω]; ring
  have hadjω : IntermediateField.adjoin ℚ {ω} = ⊤ := by
    rw [eq_top_iff, ← hadj, IntermediateField.adjoin_simple_le_iff, hxω]
    have hm := IntermediateField.mem_adjoin_simple_self ℚ ω
    exact sub_mem (mul_mem (ofNat_mem _ 2) hm) (one_mem _)
  have hdeg : (minpoly ℚ ω).natDegree = 2 := by
    have := IntermediateField.adjoin.finrank (K := ℚ) (x := ω) (.of_finite ℚ ω)
    rw [hadjω, IntermediateField.finrank_top', hrank] at this
    exact this.symm
  have hint' : IsIntegral ℤ ω' := RingOfIntegers.isIntegral ω'
  have hdegZ : (minpoly ℤ ω').natDegree = 2 := by
    have hmap := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K hint'
    rw [hω'] at hmap
    rw [← (minpoly.monic hint').natDegree_map (algebraMap ℤ ℚ), ← hmap]
    exact hdeg
  have hPmon : (X ^ 2 - X - C c : ℤ[X]).Monic := by monicity!
  have hPdeg : (X ^ 2 - X - C c : ℤ[X]).natDegree = 2 := by compute_degree!
  have hrel : ω' ^ 2 - ω' - (c : 𝓞 K) = 0 := by
    apply RingOfIntegers.coe_injective
    simp only [map_sub, map_pow, map_intCast, map_zero, hω']
    exact hrelK
  have hP : (X ^ 2 - X - C c : ℤ[X]) = minpoly ℤ ω' := by
    refine minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly hPmon ?_ ?_
    · simpa using hrel
    · rw [degree_eq_natDegree hPmon.ne_zero, degree_eq_natDegree (minpoly.ne_zero hint'), hPdeg,
        hdegZ]
  have hAdj : Algebra.adjoin ℚ {algebraMap (𝓞 K) K ω'} = ⊤ := by
    have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (F := ℚ) (α := ω)
      (Algebra.IsAlgebraic.isAlgebraic ω)
    rw [hadjω, IntermediateField.top_toSubalgebra] at this
    rw [hω']
    exact this.symm
  have hmem := aeval_derivative_mem_differentIdeal ℤ ℚ K ω' hAdj
  rw [← hP] at hmem
  have hder : derivative (X ^ 2 - X - C c : ℤ[X]) = C 2 * X - 1 := by
    rw [derivative_sub, derivative_sub, derivative_X_pow, derivative_X, derivative_C, sub_zero]
    norm_num
  have hx'' : x' = 2 * ω' - 1 := by
    apply RingOfIntegers.coe_injective
    show algebraMap (𝓞 K) K x' = algebraMap (𝓞 K) K (2 * ω' - 1)
    rw [map_sub, map_mul, map_one, hω', map_ofNat]
    exact hx'.trans hxω
  have hval : aeval ω' (derivative (X ^ 2 - X - C c : ℤ[X])) = x' := by
    rw [hder, hx'', map_sub, map_mul, aeval_C, aeval_X, map_one]
    simp
  rw [hval] at hmem
  have hle : Ideal.span {x'} ≤ differentIdeal ℤ (𝓞 K) :=
    (Ideal.span_singleton_le_iff_mem _).2 hmem
  have hn : (Algebra.norm ℤ x') ^ 2 = a ^ 2 := by
    have : ((Algebra.norm ℤ x' : ℤ) : ℚ) ^ 2 = (a : ℚ) ^ 2 := by
      rw [Algebra.coe_norm_int, hx', ← map_pow, hx, show ((a : ℤ) : K) = algebraMap ℚ K a by simp,
        Algebra.norm_algebraMap, hrank]
    exact_mod_cast this
  have hN1 : Ideal.absNorm (Ideal.span {x'}) = a.natAbs := by
    rw [Ideal.absNorm_span_singleton]
    exact Int.natAbs_eq_iff_sq_eq.2 hn
  have hN2 : Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = a.natAbs := by
    rw [NumberField.absNorm_differentIdeal K (𝓞 K), hdisc]
  exact (eq_of_le_of_absNorm_eq hle (by rw [hN1]; exact Int.natAbs_ne_zero.2 ha0)
    (hN1.trans hN2.symm)).symm

end RHLean.Analysis.NativeQuadraticDifferent

end
