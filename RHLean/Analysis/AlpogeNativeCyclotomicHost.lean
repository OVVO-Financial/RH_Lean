import RHLean.Analysis.AlpogeNativeDyadicHostSize

/-!
# The actual cyclotomic field of the native dyadic host

The field constructed here is the fixed field of the kernel of the existing
native reciprocity map, composed with the cyclotomic Galois isomorphism. Its
ambient modulus is the original `2^(e+2) * q * d`, and its Galois group is the
same two-bit-plus-dyadic host used by the native arithmetic source.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/OfChar.lean`, declarations
`CharData.{cyc,res,E,gal,gal_restrict,gal_symm_apply}`, and `CycBasic.lean`,
declarations `Der.{tauN_neg_one,conj_apply,conj_iff,finrank_E}`.
The residue calculation at `-1` follows `D7.{sgnN_neg_one,artinMap_neg_one}`
in `ArtinMapSecondEqJacobiSym.lean` at the same pin.

This reconstructs the original kernel fixed-field mechanism over the actual
RH_Lean residue map. The field and its Galois action are constructed, rather
than supplied as premises. Compatibility of ideal inertia and Frobenius,
the CM abelian varieties, and their integral theta lattices remains separate.
No terminal RH theorem or external compiled proof is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

open NumberField IntermediateField

namespace RHLean.Analysis

/-- The ambient cyclotomic field has the literal native conductor modulus. -/
abbrev AlpogeNativeCyclotomic (e q d : ℕ) :=
  CyclotomicField (alpogeNativeHostN e q d) ℚ

set_option backward.isDefEq.respectTransparency false in
/-- Expose Mathlib's cyclotomic instance through the native field abbreviation. -/
@[instance] theorem alpogeNativeCyclotomic_isCyclotomicExtension (e q d : ℕ) :
    IsCyclotomicExtension {alpogeNativeHostN e q d} ℚ (AlpogeNativeCyclotomic e q d) :=
  inferInstanceAs (IsCyclotomicExtension {alpogeNativeHostN e q d} ℚ
    (CyclotomicField (alpogeNativeHostN e q d) ℚ))

@[instance] theorem alpogeNativeCyclotomic_isGalois (e q d : ℕ) :
    IsGalois ℚ (AlpogeNativeCyclotomic e q d) :=
  IsCyclotomicExtension.isGalois {alpogeNativeHostN e q d} ℚ _

/-- The cyclotomic Galois isomorphism for the same modulus. -/
def alpogeNativeCyclotomicGalEquiv (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    (AlpogeNativeCyclotomic e q d ≃ₐ[ℚ] AlpogeNativeCyclotomic e q d) ≃*
      (ZMod (alpogeNativeHostN e q d))ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod
    (alpogeNativeHostN e q d) (AlpogeNativeCyclotomic e q d)

/-- The actual cyclotomic action maps onto the existing arithmetic host. -/
def alpogeNativeCyclotomicRecMap (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    (AlpogeNativeCyclotomic e q d ≃ₐ[ℚ] AlpogeNativeCyclotomic e q d) →*
      Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e) :=
  (alpogeNativeRecMap e q d).comp
    (alpogeNativeCyclotomicGalEquiv e q d).toMonoidHom

theorem alpogeNativeCyclotomicRecMap_surjective
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d) :
    Function.Surjective (alpogeNativeCyclotomicRecMap e q d) :=
  (alpogeNativeRecMap_surjective e q d hq2 hd2 hqd).comp
    (alpogeNativeCyclotomicGalEquiv e q d).surjective

/-- A genuine subfield of the original cyclotomic field, not an abstract
finite group carrying the name of a number field. -/
def alpogeNativeHostField (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    IntermediateField ℚ (AlpogeNativeCyclotomic e q d) :=
  fixedField (alpogeNativeCyclotomicRecMap e q d).ker

theorem alpogeNativeHostField_numberField
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    NumberField (alpogeNativeHostField e q d) := inferInstance

@[instance] theorem alpogeNativeHostField_isGalois
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    IsGalois ℚ (alpogeNativeHostField e q d) :=
  IsGalois.of_fixedField_normal_subgroup
    (alpogeNativeCyclotomicRecMap e q d).ker

private def nativeQuotientGaloisEquiv
    {L G : Type*} [Field L] [CharZero L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] [Group G]
    (ρ : (L ≃ₐ[ℚ] L) →* G) (hρ : Function.Surjective ρ) :
    (fixedField ρ.ker ≃ₐ[ℚ] fixedField ρ.ker) ≃* G :=
  let ε : ((L ≃ₐ[ℚ] L) ⧸ ρ.ker) ≃*
      (fixedField ρ.ker ≃ₐ[ℚ] fixedField ρ.ker) :=
    IsGalois.normalAutEquivQuotient (K := ℚ) (L := L) ρ.ker
  let η : ((L ≃ₐ[ℚ] L) ⧸ ρ.ker) ≃* G :=
    QuotientGroup.quotientKerEquivOfSurjective (G := L ≃ₐ[ℚ] L) (H := G) ρ hρ
  ε.symm.trans η

private theorem nativeQuotientGaloisEquiv_restrict
    {L G : Type*} [Field L] [CharZero L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] [Group G]
    (ρ : (L ≃ₐ[ℚ] L) →* G) (hρ : Function.Surjective ρ) (τ : L ≃ₐ[ℚ] L) :
    nativeQuotientGaloisEquiv ρ hρ (τ.restrictNormal (fixedField ρ.ker)) = ρ τ := by
  have h : (IsGalois.normalAutEquivQuotient (K := ℚ) (L := L) ρ.ker).symm
      (τ.restrictNormal (fixedField ρ.ker)) =
        (τ : (L ≃ₐ[ℚ] L) ⧸ ρ.ker) :=
    (MulEquiv.symm_apply_eq _).mpr
      (IsGalois.normalAutEquivQuotient_apply ρ.ker τ).symm
  change QuotientGroup.quotientKerEquivOfSurjective ρ hρ
    ((IsGalois.normalAutEquivQuotient (K := ℚ) (L := L) ρ.ker).symm
      (τ.restrictNormal (fixedField ρ.ker))) = ρ τ
  rw [h]
  rfl

set_option maxHeartbeats 1000000 in
/-- The Galois group of the constructed field is the full native host. -/
def alpogeNativeHostGalEquiv
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d) :
    (alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) ≃*
      Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e) := by
  unfold alpogeNativeHostField
  exact nativeQuotientGaloisEquiv
    (L := AlpogeNativeCyclotomic e q d)
    (G := Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e))
    (alpogeNativeCyclotomicRecMap e q d)
    (alpogeNativeCyclotomicRecMap_surjective e q d hq2 hd2 hqd)

set_option maxHeartbeats 1000000 in
/-- Restriction of a cyclotomic automorphism induces exactly the existing
native reciprocity image, without replacing either map by a chosen bijection. -/
theorem alpogeNativeHostGalEquiv_restrict
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (τ : AlpogeNativeCyclotomic e q d ≃ₐ[ℚ] AlpogeNativeCyclotomic e q d) :
    alpogeNativeHostGalEquiv e q d hq2 hd2 hqd
      (τ.restrictNormal (alpogeNativeHostField e q d)) =
        alpogeNativeRecMap e q d (alpogeNativeCyclotomicGalEquiv e q d τ) :=
  nativeQuotientGaloisEquiv_restrict
    (L := AlpogeNativeCyclotomic e q d)
    (G := Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e))
    (alpogeNativeCyclotomicRecMap e q d)
    (alpogeNativeCyclotomicRecMap_surjective e q d hq2 hd2 hqd) τ

/-- The field embedding intertwines the actual Galois quotient with the
original cyclotomic action. This is the field-level `art_spec` identity. -/
theorem alpogeNativeHostGalEquiv_symm_apply
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (τ : AlpogeNativeCyclotomic e q d ≃ₐ[ℚ] AlpogeNativeCyclotomic e q d)
    (x : alpogeNativeHostField e q d) :
    (((alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).symm
      (alpogeNativeRecMap e q d (alpogeNativeCyclotomicGalEquiv e q d τ)) x :
        alpogeNativeHostField e q d) : AlpogeNativeCyclotomic e q d) = τ x := by
  rw [← alpogeNativeHostGalEquiv_restrict e q d hq2 hd2 hqd τ,
    MulEquiv.symm_apply_apply]
  exact AlgEquiv.restrictNormal_commutes τ (alpogeNativeHostField e q d) x

/-- Exactly the kernel of the same native residue map fixes the field. -/
theorem alpogeNativeCyclotomic_fixes_hostField_iff
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (τ : AlpogeNativeCyclotomic e q d ≃ₐ[ℚ] AlpogeNativeCyclotomic e q d) :
    (∀ x : alpogeNativeHostField e q d,
      τ (x : AlpogeNativeCyclotomic e q d) = (x : AlpogeNativeCyclotomic e q d)) ↔
      alpogeNativeRecMap e q d (alpogeNativeCyclotomicGalEquiv e q d τ) = 1 := by
  change _ ↔ τ ∈ (alpogeNativeCyclotomicRecMap e q d).ker
  rw [← IntermediateField.fixingSubgroup_fixedField
    (alpogeNativeCyclotomicRecMap e q d).ker,
    IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.2⟩

/-- The actual number-field degree is four times the original dyadic host size. -/
theorem alpogeNativeHostField_finrank
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d) :
    Module.finrank ℚ (alpogeNativeHostField e q d) = 4 * 2 ^ e := by
  rw [← IsGalois.card_aut_eq_finrank]
  calc
    Nat.card (alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) =
        Nat.card (Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e)) :=
      Nat.card_congr (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).toEquiv
    _ = 4 * 2 ^ e := by
      change Nat.card ((ZMod 2 × ZMod 2) × AlpogeNativeDyadicH e) = _
      norm_num only [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card,
        alpogeNativeDyadicH_card]

private theorem nativeCyclotomic_unitsMap_neg_one
    {M N : ℕ} (h : M ∣ N) : ZMod.unitsMap h (-1) = -1 := by
  apply Units.ext
  rw [ZMod.unitsMap_def, Units.coe_map]
  change ZMod.castHom h (ZMod M) (-1) = -1
  rw [map_neg, map_one]

private theorem nativeCyclotomic_legU_neg_one
    (N p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) (hp : p ∣ N) :
    alpogeNativeLegU N p hp (-1) = -1 := by
  have hp2 : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  apply Units.ext
  calc
    ((alpogeNativeLegU N p hp (-1) : ℤˣ) : ℤ) =
        quadraticChar (ZMod p) (-1) := by
      simp only [alpogeNativeLegU, MonoidHom.comp_apply, MulChar.coe_toUnitHom,
        nativeCyclotomic_unitsMap_neg_one, Units.val_neg, Units.val_one]
    _ = -1 := by
      rw [quadraticChar_neg_one hp2, ZMod.card, ZMod.χ₄_nat_three_mod_four hp4]
    _ = ((-1 : ℤˣ) : ℤ) := rfl

/-- The residue `-1` has exactly the two quadratic conjugation bits and
trivial dyadic quotient coordinate. The first native bit is d, the second q. -/
theorem alpogeNativeRecMap_neg_one
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    alpogeNativeRecMap e q d (-1) =
      Multiplicative.ofAdd (alpogeNativeCconj (AlpogeNativeDyadicH e)) := by
  change
    ((Multiplicative.toAdd (alpogeNativeSign2
        (alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d) (-1))),
      Multiplicative.toAdd (alpogeNativeSign2
        (alpogeNativeLegU _ q (alpogeNativeQ_dvd_hostN e q d) (-1)))),
      Additive.ofMul (QuotientGroup.mk
        (ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) (-1)))) =
      ((1, 1), 0)
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · rw [nativeCyclotomic_legU_neg_one _ d hd4]
    change (if (-1 : ℤˣ) = 1 then (0 : ZMod 2) else 1) = 1
    exact ite_eq_right (by decide)
  · rw [nativeCyclotomic_legU_neg_one _ q hq4]
    change (if (-1 : ℤˣ) = 1 then (0 : ZMod 2) else 1) = 1
    exact ite_eq_right (by decide)
  · change (QuotientGroup.mk
      (ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) (-1)) :
        (ZMod (2 ^ (e + 2)))ˣ ⧸
          Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)) = 1
    rw [nativeCyclotomic_unitsMap_neg_one, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_zpowers (-1)

/-- The canonical primitive root in the unchanged ambient field. -/
def alpogeNativeCyclotomicZeta (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    AlpogeNativeCyclotomic e q d :=
  IsCyclotomicExtension.zeta
    (alpogeNativeHostN e q d) ℚ (AlpogeNativeCyclotomic e q d)

theorem alpogeNativeCyclotomicZeta_spec
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    IsPrimitiveRoot (alpogeNativeCyclotomicZeta e q d) (alpogeNativeHostN e q d) :=
  IsCyclotomicExtension.zeta_spec
    (alpogeNativeHostN e q d) ℚ (AlpogeNativeCyclotomic e q d)

/-- The action on the primitive root uniquely determines the residue unit. -/
theorem alpogeNativeCyclotomicGalEquiv_eq_of_zeta_pow
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (u : (ZMod (alpogeNativeHostN e q d))ˣ)
    (τ : AlpogeNativeCyclotomic e q d ≃ₐ[ℚ] AlpogeNativeCyclotomic e q d)
    (hτ : τ (alpogeNativeCyclotomicZeta e q d) =
      alpogeNativeCyclotomicZeta e q d ^
        (u : ZMod (alpogeNativeHostN e q d)).val) :
    alpogeNativeCyclotomicGalEquiv e q d τ = u := by
  have hζ := alpogeNativeCyclotomicZeta_spec e q d
  have h1 : τ (alpogeNativeCyclotomicZeta e q d) =
      alpogeNativeCyclotomicZeta e q d ^
        (alpogeNativeCyclotomicGalEquiv e q d τ :
          ZMod (alpogeNativeHostN e q d)).val :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq _ _ τ hζ.pow_eq_one
  rw [hτ] at h1
  have h2 : (u : ZMod (alpogeNativeHostN e q d)).val =
      (alpogeNativeCyclotomicGalEquiv e q d τ :
        ZMod (alpogeNativeHostN e q d)).val :=
    hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1
  exact Units.ext (ZMod.val_injective _ h2).symm

/-- The exact cyclotomic embedding specification of the native Artin map. -/
theorem alpogeNativeHostField_art_spec
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (u : (ZMod (alpogeNativeHostN e q d))ˣ)
    (τ : AlpogeNativeCyclotomic e q d ≃ₐ[ℚ] AlpogeNativeCyclotomic e q d)
    (hτ : τ (alpogeNativeCyclotomicZeta e q d) =
      alpogeNativeCyclotomicZeta e q d ^
        (u : ZMod (alpogeNativeHostN e q d)).val)
    (x : alpogeNativeHostField e q d) :
    (((alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).symm
      (alpogeNativeRecMap e q d u) x : alpogeNativeHostField e q d) :
        AlpogeNativeCyclotomic e q d) = τ x := by
  rw [← alpogeNativeCyclotomicGalEquiv_eq_of_zeta_pow e q d u τ hτ]
  exact alpogeNativeHostGalEquiv_symm_apply e q d hq2 hd2 hqd τ x

/-- The inverse cyclotomic Galois map acts by the residue exponent on every
root of unity of order dividing the original conductor. -/
theorem alpogeNativeCyclotomicGalEquiv_symm_apply
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (u : (ZMod (alpogeNativeHostN e q d))ˣ)
    (w : AlpogeNativeCyclotomic e q d) (hw : w ^ alpogeNativeHostN e q d = 1) :
    (alpogeNativeCyclotomicGalEquiv e q d).symm u w =
      w ^ (u : ZMod (alpogeNativeHostN e q d)).val := by
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
    (alpogeNativeHostN e q d) (AlpogeNativeCyclotomic e q d) _ hw]
  change w ^ ((alpogeNativeCyclotomicGalEquiv e q d)
    ((alpogeNativeCyclotomicGalEquiv e q d).symm u) :
      ZMod (alpogeNativeHostN e q d)).val = _
  rw [MulEquiv.apply_symm_apply]

/-- In every complex embedding the cyclotomic automorphism attached to `-1`
is actual complex conjugation. -/
theorem alpogeNativeCyclotomic_neg_one_apply
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (Ψ : AlpogeNativeCyclotomic e q d →+* ℂ) (x : AlpogeNativeCyclotomic e q d) :
    Ψ ((alpogeNativeCyclotomicGalEquiv e q d).symm (-1) x) =
      starRingEnd ℂ (Ψ x) := by
  let ζ := alpogeNativeCyclotomicZeta e q d
  have hζ : IsPrimitiveRoot ζ (alpogeNativeHostN e q d) :=
    alpogeNativeCyclotomicZeta_spec e q d
  have key : (Ψ.comp
      ((alpogeNativeCyclotomicGalEquiv e q d).symm (-1) :
        AlpogeNativeCyclotomic e q d →+* AlpogeNativeCyclotomic e q d)).toRatAlgHom =
      ((starRingEnd ℂ).comp Ψ).toRatAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    change Ψ ((alpogeNativeCyclotomicGalEquiv e q d).symm (-1) ζ) =
      starRingEnd ℂ (Ψ ζ)
    have hnorm : ‖Ψ ζ‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one
        (by rw [← map_pow, hζ.pow_eq_one, map_one])
        (NeZero.ne (alpogeNativeHostN e q d))
    have hinv : ζ ^ ((-1 : (ZMod (alpogeNativeHostN e q d))ˣ) :
        ZMod (alpogeNativeHostN e q d)).val * ζ = 1 := by
      rw [← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      simp
    rw [alpogeNativeCyclotomicGalEquiv_symm_apply e q d _ _ hζ.pow_eq_one,
      ← Complex.inv_eq_conj hnorm]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, hinv, map_one]
  exact DFunLike.congr_fun key x

/-- The actual conjugation of the fixed field, obtained by restricting the
ambient cyclotomic automorphism `-1`. -/
def alpogeNativeHostConj (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d :=
  ((alpogeNativeCyclotomicGalEquiv e q d).symm (-1)).restrictNormal
    (alpogeNativeHostField e q d)

/-- Every complex embedding sees this same field automorphism as conjugation. -/
theorem alpogeNativeHostConj_apply
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (ψ : alpogeNativeHostField e q d →+* ℂ) (x : alpogeNativeHostField e q d) :
    ψ (alpogeNativeHostConj e q d x) = starRingEnd ℂ (ψ x) := by
  let Ψ := ComplexEmbedding.lift (AlpogeNativeCyclotomic e q d) ψ
  have hΨ : ∀ y : alpogeNativeHostField e q d,
      Ψ (y : AlpogeNativeCyclotomic e q d) = ψ y :=
    fun y => ComplexEmbedding.lift_algebraMap_apply (AlpogeNativeCyclotomic e q d) ψ y
  calc
    ψ (alpogeNativeHostConj e q d x) =
        Ψ ((alpogeNativeHostConj e q d x : alpogeNativeHostField e q d) :
          AlpogeNativeCyclotomic e q d) := (hΨ _).symm
    _ = Ψ ((alpogeNativeCyclotomicGalEquiv e q d).symm (-1)
        (x : AlpogeNativeCyclotomic e q d)) :=
      congrArg Ψ (AlgEquiv.restrictNormal_commutes
        ((alpogeNativeCyclotomicGalEquiv e q d).symm (-1))
        (alpogeNativeHostField e q d) x)
    _ = starRingEnd ℂ (Ψ (x : AlpogeNativeCyclotomic e q d)) :=
      alpogeNativeCyclotomic_neg_one_apply e q d Ψ x
    _ = starRingEnd ℂ (ψ x) := by rw [hΨ x]

theorem alpogeNativeHostConj_isConj
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (ψ : alpogeNativeHostField e q d →+* ℂ) :
    ComplexEmbedding.IsConj ψ (alpogeNativeHostConj e q d) := by
  ext x
  exact (alpogeNativeHostConj_apply e q d ψ x).symm

/-- The field-theoretic conjugation maps to the already used native `Cconj`. -/
theorem alpogeNativeHostGalEquiv_conj
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    alpogeNativeHostGalEquiv e q d hq2 hd2 hqd (alpogeNativeHostConj e q d) =
      Multiplicative.ofAdd (alpogeNativeCconj (AlpogeNativeDyadicH e)) := by
  rw [alpogeNativeHostConj, alpogeNativeHostGalEquiv_restrict,
    MulEquiv.apply_symm_apply, alpogeNativeRecMap_neg_one e q d hq4 hd4]

/-- Actual conjugation in any complex embedding is equivalent to the same
distinguished native host element, as required by the original host interface. -/
theorem alpogeNativeHostGalEquiv_conj_iff
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3)
    (ψ : alpogeNativeHostField e q d →+* ℂ)
    (σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) :
    (∀ x, ψ (σ x) = starRingEnd ℂ (ψ x)) ↔
      alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ =
        Multiplicative.ofAdd (alpogeNativeCconj (AlpogeNativeDyadicH e)) := by
  constructor
  · intro h
    have hσ : σ = alpogeNativeHostConj e q d :=
      AlgEquiv.ext fun x => ψ.injective
        ((h x).trans (alpogeNativeHostConj_apply e q d ψ x).symm)
    rw [hσ, alpogeNativeHostGalEquiv_conj e q d hq2 hd2 hqd hq4 hd4]
  · intro h
    have hσ : σ = alpogeNativeHostConj e q d :=
      (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).injective
        (h.trans (alpogeNativeHostGalEquiv_conj e q d hq2 hd2 hqd hq4 hd4).symm)
    rw [hσ]
    exact alpogeNativeHostConj_apply e q d ψ

theorem alpogeNativeHostConj_ne_one
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    alpogeNativeHostConj e q d ≠ 1 := by
  intro h
  have hgal := alpogeNativeHostGalEquiv_conj e q d hq2 hd2 hqd hq4 hd4
  rw [h, map_one] at hgal
  have hbit := congrArg
    (fun g : Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e) =>
      g.toAdd.1.1) hgal
  change (0 : ZMod 2) = 1 at hbit
  exact zero_ne_one hbit

/-- The actual constructed field is totally complex for the selected prime
congruences; no square-root or CM-field witness is assumed. -/
theorem alpogeNativeHostField_isTotallyComplex
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    IsTotallyComplex (alpogeNativeHostField e q d) := by
  refine ⟨fun w => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  exact (ComplexEmbedding.isConj_ne_one_iff
    (alpogeNativeHostConj_isConj e q d w.embedding)).mp
      (alpogeNativeHostConj_ne_one e q d hq2 hd2 hqd hq4 hd4)

/-- The same fixed field is a CM field, with its conjugation already
identified with the native arithmetic involution. -/
theorem alpogeNativeHostField_isCMField
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    IsCMField (alpogeNativeHostField e q d) := by
  have := alpogeNativeHostField_isTotallyComplex e q d hq2 hd2 hqd hq4 hd4
  exact IsCMField.of_forall_isConj (alpogeNativeHostField e q d)
    (alpogeNativeHostConj_isConj e q d)

end RHLean.Analysis

end
