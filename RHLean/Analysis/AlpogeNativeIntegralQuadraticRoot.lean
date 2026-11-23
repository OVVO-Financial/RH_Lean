import RHLean.Analysis.AlpogeNativeQuadraticRoot

/-!
# Integral quadratic elements for the actual geometric host

The geometric host needs integral elements `rt` and `w0` with
`rt^2 = -d` and `2*w0 = 1+rt`. Both are constructed from the SAME canonical
native Gauss root: `rt = sqrtD`, `w0 = (1+sqrtD)/2`. Integrality of `w0`
comes from its explicit monic quadratic, using `d = 3 mod 4`.

Complex conjugation is the restriction of the already constructed actual
cyclotomic conjugation. Its actions on these two integral elements are
proved, including `w0 + bar(w0) = 1`.

Source: Levent Alpöge (with Claude), `CocoSgt/riemann-hypothesis-lean` at
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean`,
`Decomp.omega_integral`; and
`ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/`
`ToroidalCompactification/TwoWeightEqOneAddRoot.lean`, `Geo.Tor.Host`.

This supplies the actual integral elements and involution needed by that
host. The genuine unramified extension over its maximal real subfield and
the CM abelian moduli remain separate obligations. The source archive/mirror
states no license; this notice preserves attribution without relicensing.
-/

set_option autoImplicit false

noncomputable section
open NumberField

namespace RHLean.Analysis

namespace NativeIntegralQuadratic

/-- The original explicit monic polynomial proves half-root integrality. -/
theorem halfRoot_integral {F : Type} [Field F] [CharZero F]
    {d : ℕ} (hd4 : d % 4 = 3) {r : F} (hr : r ^ 2 = -(d : F)) :
    IsIntegral ℤ ((1 + r) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
  have hm' : (d : F) + 1 = 4 * (m : F) := by exact_mod_cast hm
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
  · monicity!
  · simp
    linear_combination (1 / 4 : F) * hr - (1 / 4 : F) * hm'

end NativeIntegralQuadratic

theorem alpogeNativeSqrtD_integral
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hd4 : d % 4 = 3) :
    IsIntegral ℤ (alpogeNativeSqrtD e q d) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  rw [alpogeNativeSqrtD_sq e q d hd4]
  exact (isIntegral_natCast d).neg

/-- The actual canonical Gauss root as an algebraic integer. -/
def alpogeNativeIntegralSqrtD
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hd4 : d % 4 = 3) :
    𝓞 (alpogeNativeHostField e q d) :=
  ⟨alpogeNativeSqrtD e q d, alpogeNativeSqrtD_integral e q d hd4⟩

/-- The original half-root is integral, with no integral-element premise. -/
def alpogeNativeIntegralHalfRoot
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hd4 : d % 4 = 3) :
    𝓞 (alpogeNativeHostField e q d) :=
  ⟨(1 + alpogeNativeSqrtD e q d) / 2,
    NativeIntegralQuadratic.halfRoot_integral hd4 (alpogeNativeSqrtD_sq e q d hd4)⟩

theorem alpogeNativeIntegralSqrtD_sq
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hd4 : d % 4 = 3) :
    alpogeNativeIntegralSqrtD e q d hd4 ^ 2 =
      -(d : 𝓞 (alpogeNativeHostField e q d)) := by
  apply RingOfIntegers.ext
  exact alpogeNativeSqrtD_sq e q d hd4

theorem alpogeNativeIntegralHalfRoot_two_mul
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hd4 : d % 4 = 3) :
    2 * alpogeNativeIntegralHalfRoot e q d hd4 =
      1 + alpogeNativeIntegralSqrtD e q d hd4 := by
  apply RingOfIntegers.ext
  change 2 * ((1 + alpogeNativeSqrtD e q d) / 2) = 1 + alpogeNativeSqrtD e q d
  field_simp

/-- Restrict the actual fixed-field conjugation to its ring of integers. -/
def alpogeNativeIntegralBar (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    𝓞 (alpogeNativeHostField e q d) ≃+* 𝓞 (alpogeNativeHostField e q d) :=
  RingOfIntegers.mapRingEquiv (alpogeNativeHostConj e q d).toRingEquiv

theorem alpogeNativeIntegralBar_apply
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (a : 𝓞 (alpogeNativeHostField e q d)) :
    (alpogeNativeIntegralBar e q d a : alpogeNativeHostField e q d) =
      alpogeNativeHostConj e q d a := rfl

/-- The integral involution agrees with the CM-field conjugation in every
embedding; it is not a separately chosen involution. -/
theorem alpogeNativeIntegralBar_eq_complexConj
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    [IsCMField (alpogeNativeHostField e q d)]
    (a : 𝓞 (alpogeNativeHostField e q d)) :
    (alpogeNativeIntegralBar e q d a : alpogeNativeHostField e q d) =
      IsCMField.complexConj (alpogeNativeHostField e q d) a := by
  obtain ⟨ψ⟩ : Nonempty (alpogeNativeHostField e q d →+* ℂ) := inferInstance
  apply ψ.injective
  exact (alpogeNativeHostConj_apply e q d ψ a).trans
    (IsCMField.complexEmbedding_complexConj (alpogeNativeHostField e q d) ψ a).symm

theorem alpogeNativeHostConj_sqrtD
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    alpogeNativeHostConj e q d (alpogeNativeSqrtD e q d) =
      -alpogeNativeSqrtD e q d := by
  rw [alpogeNativeSqrtD_galois_apply e q d hq2 hd2 hqd,
    alpogeNativeHostGalEquiv_conj e q d hq2 hd2 hqd hq4 hd4]
  norm_num [alpogeNativeCconj]

theorem alpogeNativeIntegralBar_sqrtD
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    alpogeNativeIntegralBar e q d (alpogeNativeIntegralSqrtD e q d hd4) =
      -alpogeNativeIntegralSqrtD e q d hd4 := by
  apply RingOfIntegers.ext
  exact alpogeNativeHostConj_sqrtD e q d hq2 hd2 hqd hq4 hd4

theorem alpogeNativeIntegralBar_halfRoot
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    alpogeNativeIntegralBar e q d (alpogeNativeIntegralHalfRoot e q d hd4) =
      1 - alpogeNativeIntegralHalfRoot e q d hd4 := by
  apply RingOfIntegers.ext
  change alpogeNativeHostConj e q d ((1 + alpogeNativeSqrtD e q d) / 2) =
    1 - (1 + alpogeNativeSqrtD e q d) / 2
  rw [map_div₀, map_add, map_one, map_ofNat,
    alpogeNativeHostConj_sqrtD e q d hq2 hd2 hqd hq4 hd4]
  ring

theorem alpogeNativeIntegralHalfRoot_add_bar
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    alpogeNativeIntegralHalfRoot e q d hd4 +
      alpogeNativeIntegralBar e q d (alpogeNativeIntegralHalfRoot e q d hd4) = 1 := by
  rw [alpogeNativeIntegralBar_halfRoot e q d hq2 hd2 hqd hq4 hd4]
  ring

end RHLean.Analysis

end
