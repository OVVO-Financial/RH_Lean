import RHLean.Analysis.AlpogeNativeCyclotomicHost
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The actual quadratic Gauss root in the native fixed field

The element is the finite quadratic Gauss sum at `zeta_N^(N/d)`, where
`N = 2^(e+2) * q * d` is the unchanged native conductor. Its square is `-d`.
The multiplicative-shift identity for Gauss sums proves its cyclotomic Galois
action. The kernel of the existing native reciprocity map therefore fixes
the element, placing it in the SAME native host field.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean`,
`Cond.{chi,gs,gs_sq,prim_pow,sqrt_exists}`;
`Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`ArtinMapSecondEqJacobiSym.lean`, `D7.{gs_act,sqrt_act}`; and
`InertiaGaloisSymmetry/OfChar.lean`, `CharData.exists_root`.

The native coordinate order is explicit: the first bit is the d-character,
and the second is the q-character. No square-root witness, field-identification
premise, or quadratic-action premise is assumed. The source archive/mirror
states no license; this notice preserves attribution without assigning a new
license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField

namespace RHLean.Analysis

namespace NativeQuadraticRoot

/-- The actual quadratic character with coefficients in the ambient field. -/
def chi (p : ℕ) [Fact p.Prime] (K : Type) [Field K] : MulChar (ZMod p) K :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom K)

/-- The finite quadratic Gauss sum attached to the displayed root of unity. -/
def gauss {K : Type} [Field K] (p : ℕ) [Fact p.Prime]
    {x : K} (hx : x ^ p = 1) : K :=
  gaussSum (chi p K) (AddChar.zmodChar p hx)

theorem chi_neg_one {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    (hp4 : p % 4 = 3) : chi p K (-1) = -1 := by
  have hp2 : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  change (Int.castRingHom K) (quadraticChar (ZMod p) (-1)) = -1
  rw [quadraticChar_neg_one hp2, ZMod.card, ZMod.χ₄_nat_three_mod_four hp4,
    map_neg, map_one]

theorem gauss_sq {K : Type} [Field K] [CharZero K]
    {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) {x : K}
    (hx : IsPrimitiveRoot x p) :
    gauss p hx.pow_eq_one ^ 2 = -(p : K) := by
  have hnontrivial : chi p K ≠ 1 := by
    intro h
    have hneg := chi_neg_one (K := K) hp4
    have hone : (1 : MulChar (ZMod p) K) (-1) = 1 :=
      MulChar.one_apply isUnit_one.neg
    rw [h, hone] at hneg
    norm_num at hneg
  have hquadratic : (chi p K).IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod p)).comp _
  have hprimitive : (AddChar.zmodChar p hx.pow_eq_one).IsPrimitive :=
    AddChar.zmodChar_primitive_of_primitive_root p hx
  unfold gauss
  rw [gaussSum_sq hnontrivial hquadratic hprimitive, chi_neg_one hp4, ZMod.card]
  ring

/-- The original Gauss-sum shift calculation, for the same root of unity.
Quadraticity identifies the inverse character with the original character. -/
theorem gauss_map {K : Type} [Field K]
    {p : ℕ} [Fact p.Prime] {x : K} (hx : x ^ p = 1)
    (σ : K →+* K) (v : ℕ) (hσ : σ x = x ^ v) (hv : v.Coprime p) :
    σ (gauss p hx) = ((quadraticChar (ZMod p) (v : ZMod p) : ℤ) : K) *
      gauss p hx := by
  let w : (ZMod p)ˣ := ZMod.unitOfCoprime v hv
  have hwv : (w : ZMod p) = (v : ZMod p) := ZMod.coe_unitOfCoprime v hv
  have hψ : ∀ a : ZMod p, σ (AddChar.zmodChar p hx a) =
      AddChar.zmodChar p hx ((w : ZMod p) * a) := by
    intro a
    rw [AddChar.zmodChar_apply, map_pow, hσ, ← pow_mul]
    have hwa : (w : ZMod p) * a = ((v * a.val : ℕ) : ZMod p) := by
      push_cast
      rw [hwv, ZMod.natCast_zmod_val]
    rw [hwa, AddChar.zmodChar_apply']
  have hχ : ∀ a : ZMod p, σ (chi p K a) = chi p K a := by
    intro a
    simp only [chi, MulChar.ringHomComp_apply]
    exact map_intCast σ _
  have hmap : σ (gauss p hx) = gaussSum (chi p K)
      (AddChar.mulShift (AddChar.zmodChar p hx) (w : ZMod p)) := by
    simp only [gauss, gaussSum, map_sum, map_mul, hψ, hχ, AddChar.mulShift_apply]
  have hquadratic : (chi p K).IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod p)).comp _
  have hcoeff : chi p K (w : ZMod p) =
      ((quadraticChar (ZMod p) (v : ZMod p) : ℤ) : K) :=
    congrArg (fun a : ZMod p => ((quadraticChar (ZMod p) a : ℤ) : K)) hwv
  calc
    _ = gaussSum (chi p K)
        (AddChar.mulShift (AddChar.zmodChar p hx) (w : ZMod p)) := hmap
    _ = (chi p K)⁻¹ (w : ZMod p) * gauss p hx :=
      gaussSum_mulShift_eq (chi p K) (AddChar.zmodChar p hx) w
    _ = _ := congrArg (fun a : K => a * gauss p hx)
      ((congrArg (fun χ : MulChar (ZMod p) K => χ (w : ZMod p))
        hquadratic.inv).trans hcoeff)

/-- The actual native local character is evaluated on the same residue. -/
theorem legU_val {N p : ℕ} [NeZero N] [Fact p.Prime]
    (hp : p ∣ N) (u : (ZMod N)ˣ) :
    ((alpogeNativeLegU N p hp u : ℤˣ) : ℤ) =
      quadraticChar (ZMod p) (((u : ZMod N).val : ℕ) : ZMod p) := by
  rw [alpogeNativeLegU, MonoidHom.comp_apply, MulChar.coe_toUnitHom,
    ZMod.unitsMap_val, ZMod.cast_eq_val]

/-- Decode the existing additive sign bit without changing its convention. -/
theorem sign2_decode (s : ℤˣ) :
    (s : ℤ) = if (alpogeNativeSign2 s).toAdd = 0 then 1 else -1 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;>
    norm_num [alpogeNativeSign2]

end NativeQuadraticRoot

/-- The original Gauss-sum construction, in the literal native cyclotomic field. -/
def alpogeNativeCyclotomicQuadraticRoot
    (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hp : p ∣ alpogeNativeHostN e q d) : AlpogeNativeCyclotomic e q d :=
  NativeQuadraticRoot.gauss p
    ((alpogeNativeCyclotomicZeta_spec e q d).pow
      (NeZero.pos (alpogeNativeHostN e q d)) (Nat.div_mul_cancel hp).symm).pow_eq_one

theorem alpogeNativeCyclotomicQuadraticRoot_sq
    (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hp : p ∣ alpogeNativeHostN e q d) (hp4 : p % 4 = 3) :
    alpogeNativeCyclotomicQuadraticRoot e q d p hp ^ 2 =
      -(p : AlpogeNativeCyclotomic e q d) :=
  NativeQuadraticRoot.gauss_sq hp4
    ((alpogeNativeCyclotomicZeta_spec e q d).pow
      (NeZero.pos (alpogeNativeHostN e q d)) (Nat.div_mul_cancel hp).symm)

/-- The Galois action on the constructed sum is the actual local quadratic
character of the original cyclotomic residue, with no action premise. -/
theorem alpogeNativeCyclotomicQuadraticRoot_apply
    (e q d p : ℕ) [Fact q.Prime] [Fact d.Prime] [Fact p.Prime]
    (hp : p ∣ alpogeNativeHostN e q d)
    (τ : AlpogeNativeCyclotomic e q d ≃ₐ[ℚ] AlpogeNativeCyclotomic e q d) :
    τ (alpogeNativeCyclotomicQuadraticRoot e q d p hp) =
      (((alpogeNativeLegU (alpogeNativeHostN e q d) p hp
        (alpogeNativeCyclotomicGalEquiv e q d τ) : ℤˣ) : ℤ) :
          AlpogeNativeCyclotomic e q d) *
        alpogeNativeCyclotomicQuadraticRoot e q d p hp := by
  let x := alpogeNativeCyclotomicZeta e q d ^ (alpogeNativeHostN e q d / p)
  have hx : IsPrimitiveRoot x p :=
    (alpogeNativeCyclotomicZeta_spec e q d).pow
      (NeZero.pos (alpogeNativeHostN e q d)) (Nat.div_mul_cancel hp).symm
  have hxN : x ^ alpogeNativeHostN e q d = 1 := by
    dsimp [x]
    rw [← pow_mul, mul_comm, pow_mul,
      (alpogeNativeCyclotomicZeta_spec e q d).pow_eq_one, one_pow]
  have hτ : τ x = x ^ (alpogeNativeCyclotomicGalEquiv e q d τ :
      ZMod (alpogeNativeHostN e q d)).val :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq _ _ τ hxN
  have hcop : (alpogeNativeCyclotomicGalEquiv e q d τ :
      ZMod (alpogeNativeHostN e q d)).val.Coprime p :=
    (ZMod.val_coe_unit_coprime (alpogeNativeCyclotomicGalEquiv e q d τ)).coprime_dvd_right hp
  change τ (NativeQuadraticRoot.gauss p hx.pow_eq_one) =
    (((alpogeNativeLegU (alpogeNativeHostN e q d) p hp
      (alpogeNativeCyclotomicGalEquiv e q d τ) : ℤˣ) : ℤ) :
        AlpogeNativeCyclotomic e q d) * NativeQuadraticRoot.gauss p hx.pow_eq_one
  rw [NativeQuadraticRoot.legU_val]
  exact NativeQuadraticRoot.gauss_map hx.pow_eq_one τ _ hτ hcop

/-- For p=d, the character just proved is the FIRST native sign bit. -/
theorem alpogeNativeCyclotomicQuadraticRoot_d_apply
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (τ : AlpogeNativeCyclotomic e q d ≃ₐ[ℚ] AlpogeNativeCyclotomic e q d) :
    τ (alpogeNativeCyclotomicQuadraticRoot e q d d (alpogeNativeD_dvd_hostN e q d)) =
      ((if (alpogeNativeCyclotomicRecMap e q d τ).toAdd.1.1 = 0
        then (1 : ℤ) else -1) : AlpogeNativeCyclotomic e q d) *
        alpogeNativeCyclotomicQuadraticRoot e q d d (alpogeNativeD_dvd_hostN e q d) := by
  rw [alpogeNativeCyclotomicQuadraticRoot_apply]
  simpa only [apply_ite, Int.cast_one, Int.cast_neg] using
    congrArg (fun a : ℤ => (a : AlpogeNativeCyclotomic e q d) *
    alpogeNativeCyclotomicQuadraticRoot e q d d (alpogeNativeD_dvd_hostN e q d))
    (NativeQuadraticRoot.sign2_decode
      (alpogeNativeLegU (alpogeNativeHostN e q d) d (alpogeNativeD_dvd_hostN e q d)
        (alpogeNativeCyclotomicGalEquiv e q d τ)))

/-- The original reciprocity kernel fixes the constructed d-Gauss sum. -/
theorem alpogeNativeCyclotomicQuadraticRoot_d_mem
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    alpogeNativeCyclotomicQuadraticRoot e q d d (alpogeNativeD_dvd_hostN e q d) ∈
      alpogeNativeHostField e q d := by
  rw [alpogeNativeHostField, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  rw [alpogeNativeCyclotomicQuadraticRoot_d_apply, MonoidHom.mem_ker.mp hτ]
  simp

/-- A named, concretely constructed square root, in the SAME native host field. -/
def alpogeNativeSqrtD (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    alpogeNativeHostField e q d :=
  ⟨alpogeNativeCyclotomicQuadraticRoot e q d d (alpogeNativeD_dvd_hostN e q d),
    alpogeNativeCyclotomicQuadraticRoot_d_mem e q d⟩

theorem alpogeNativeSqrtD_sq
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hd4 : d % 4 = 3) :
    alpogeNativeSqrtD e q d ^ 2 = -(d : alpogeNativeHostField e q d) := by
  apply Subtype.ext
  exact alpogeNativeCyclotomicQuadraticRoot_sq e q d d
    (alpogeNativeD_dvd_hostN e q d) hd4

/-- The action of the actual fixed-field Galois group is its first native bit. -/
theorem alpogeNativeSqrtD_galois_apply
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) :
    σ (alpogeNativeSqrtD e q d) =
      ((if (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ).toAdd.1.1 = 0
        then (1 : ℤ) else -1) : alpogeNativeHostField e q d) *
        alpogeNativeSqrtD e q d := by
  obtain ⟨τ, hτ⟩ := alpogeNativeCyclotomicRecMap_surjective e q d hq2 hd2 hqd
    (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ)
  apply Subtype.ext
  have hrestrict := alpogeNativeHostGalEquiv_symm_apply e q d hq2 hd2 hqd τ
    (alpogeNativeSqrtD e q d)
  change (((alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).symm
      (alpogeNativeCyclotomicRecMap e q d τ) (alpogeNativeSqrtD e q d) :
        alpogeNativeHostField e q d) : AlpogeNativeCyclotomic e q d) =
      τ (alpogeNativeSqrtD e q d) at hrestrict
  rw [hτ, MulEquiv.symm_apply_apply] at hrestrict
  rw [hrestrict]
  have hroot := alpogeNativeCyclotomicQuadraticRoot_d_apply e q d τ
  rw [hτ] at hroot
  by_cases hbit : (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ).toAdd.1.1 = 0 <;>
    simpa [alpogeNativeSqrtD, hbit] using hroot

/-- The original `HostRaw.sqd` witness, with its exact quadratic action. -/
theorem alpogeNativeHostField_exists_sqrtD
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d) (hd4 : d % 4 = 3) :
    ∃ y : alpogeNativeHostField e q d, y ^ 2 = -(d : alpogeNativeHostField e q d) ∧
      ∀ σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d,
        σ y = ((if (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ).toAdd.1.1 = 0
          then (1 : ℤ) else -1) : alpogeNativeHostField e q d) * y :=
  ⟨alpogeNativeSqrtD e q d, alpogeNativeSqrtD_sq e q d hd4,
    alpogeNativeSqrtD_galois_apply e q d hq2 hd2 hqd⟩

end RHLean.Analysis

end
