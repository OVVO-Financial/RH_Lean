import RHLean.Analysis.AlpogeNativeCyclotomicHost
import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN

/-!
# The constructed native field satisfies the original principal field predicate

The native fixed field is proved to satisfy `UpperTheory.Top.IsChiField` for
the principal base character. The ambient field, conductor, embedding and
primitive root are the ones already constructed from the same `e,q,d`.
There is no new field witness or hypothesis asserting its fixed subgroup.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AutomorphicArithmetic/CharacterBoxes/IsChiField.lean`,
and the elementary quotient calculation `Formalism.HC.Der.Rd.hcl_eq_one`
in `src/Formalism/SharpRestriction/RamificationFrobenius/`
`TotientGaloisClasses/InertiaGaloisSymmetry/DvdDiscrOfInertia.lean`.

This is a field-identification theorem. It does not supply the cohomological
window estimate quantified over fields by `VAt`, or identify ideal inertia
with the native finite modular-unit inertia without a further proof.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Analysis.AlpogeThin

private theorem nativeDyadicSign_zero_iff (s : ℤˣ) :
    Multiplicative.toAdd (alpogeNativeSign2 s) = 0 ↔ (s : ℤ) = 1 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;>
    norm_num [alpogeNativeSign2]

private theorem nativeDyadicLegU_nat
    (N p a : ℕ) [Fact p.Prime] (hp : p ∣ N) (ha : a.Coprime N) :
    ((alpogeNativeLegU N p hp (ZMod.unitOfCoprime a ha) : ℤˣ) : ℤ) =
      jacobiSym (a : ℤ) p := by
  change (((quadraticChar (ZMod p)).toUnitHom
    (ZMod.unitsMap hp (ZMod.unitOfCoprime a ha)) : ℤˣ) : ℤ) = _
  rw [MulChar.coe_toUnitHom, ZMod.unitsMap_val, ZMod.coe_unitOfCoprime,
    ZMod.cast_natCast hp, ← jacobiSym.legendreSym.to_jacobiSym]
  simp only [legendreSym, Int.cast_natCast]

private theorem nativeDyadicClass_eq_one_iff
    (e : ℕ) (v : (ZMod (2 ^ (e + 2)))ˣ) :
    (QuotientGroup.mk v : (ZMod (2 ^ (e + 2)))ˣ ⧸
      Subgroup.zpowers (-1)) = 1 ↔ v = 1 ∨ v = -1 := by
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← hk, ← two_mul, zpow_mul]
      simp
    · right
      rw [← hk, zpow_add, zpow_mul]
      simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers (-1)

private theorem nativeDyadicClass_zero_iff_nat
    (e N a : ℕ) (hN : 2 ^ (e + 2) ∣ N) (ha : a.Coprime N) :
    (Additive.ofMul (QuotientGroup.mk
      (ZMod.unitsMap hN (ZMod.unitOfCoprime a ha))) : AlpogeNativeDyadicH e) = 0 ↔
      (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) := by
  change (QuotientGroup.mk (ZMod.unitsMap hN (ZMod.unitOfCoprime a ha)) :
      (ZMod (2 ^ (e + 2)))ˣ ⧸ Subgroup.zpowers (-1)) = 1 ↔ _
  rw [nativeDyadicClass_eq_one_iff]
  have hval : ((ZMod.unitsMap hN (ZMod.unitOfCoprime a ha) :
      (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = a := by
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hN]
  have hone : ZMod.unitsMap hN (ZMod.unitOfCoprime a ha) = 1 ↔
      a ≡ 1 [MOD 2 ^ (e + 2)] := by
    rw [Units.ext_iff, hval, Units.val_one]
    exact ZMod.natCast_eq_natCast_iff a 1 (2 ^ (e + 2))
  have hneg : ZMod.unitsMap hN (ZMod.unitOfCoprime a ha) = -1 ↔
      a + 1 ≡ 0 [MOD 2 ^ (e + 2)] := by
    rw [Units.ext_iff, hval, Units.val_neg, Units.val_one,
      ← add_eq_zero_iff_eq_neg]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      (ZMod.natCast_eq_natCast_iff (a + 1) 0 (2 ^ (e + 2)))
  rw [hone, hneg]

/-- The native reciprocity kernel is precisely the original dyadic ±1
condition and the two Jacobi conditions, on a single residue representative.
The native coordinate order d,q is explicitly rearranged in the result. -/
theorem nativeDyadicRecMap_unitOfCoprime_eq_one_iff
    (e q d a : ℕ) [Fact q.Prime] [Fact d.Prime]
    (ha : a.Coprime (alpogeNativeHostN e q d)) :
    alpogeNativeRecMap e q d (ZMod.unitOfCoprime a ha) = 1 ↔
      (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧
        jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1 := by
  change
    ((Multiplicative.toAdd (alpogeNativeSign2
        (alpogeNativeLegU _ d (alpogeNativeD_dvd_hostN e q d)
          (ZMod.unitOfCoprime a ha))),
      Multiplicative.toAdd (alpogeNativeSign2
        (alpogeNativeLegU _ q (alpogeNativeQ_dvd_hostN e q d)
          (ZMod.unitOfCoprime a ha)))),
      (Additive.ofMul (QuotientGroup.mk
        (ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d)
          (ZMod.unitOfCoprime a ha))) : AlpogeNativeDyadicH e)) = ((0, 0), 0) ↔ _
  rw [Prod.mk.injEq, Prod.mk.injEq, nativeDyadicSign_zero_iff,
    nativeDyadicSign_zero_iff, nativeDyadicLegU_nat, nativeDyadicLegU_nat,
    nativeDyadicClass_zero_iff_nat]
  tauto

/-- The fixed field of the existing native dyadic residue map is an actual
`IsChiField` for the principal base character, with the original conductor.
No oddness/distinctness assumption is needed for this kernel identity;
those hypotheses enter the separate full-degree and CM theorems. -/
theorem nativeDyadicHostField_isChiField
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    UpperTheory.Top.IsChiField Formalism.HC.PChar.one e q d
      (alpogeNativeHostField e q d) := by
  let N := alpogeNativeHostN e q d
  let ζ := alpogeNativeCyclotomicZeta e q d
  have hζ : IsPrimitiveRoot ζ N := alpogeNativeCyclotomicZeta_spec e q d
  refine ⟨N, inferInstance, (alpogeNativeHostField e q d).val, ζ,
    alpogeNativeTwo_dvd_hostN e q d, ?_, alpogeNativeQ_dvd_hostN e q d,
    alpogeNativeD_dvd_hostN e q d, hζ, ?_⟩
  · exact one_dvd _
  · intro τ a hτ
    have hprim : IsPrimitiveRoot (ζ ^ a) N := by
      rw [← hτ]
      exact hζ.map_of_injective τ.injective
    have ha : a.Coprime N := (hζ.pow_iff_coprime (NeZero.pos N) a).mp hprim
    let u := ZMod.unitOfCoprime a ha
    have hτu : τ ζ = ζ ^ (u : ZMod N).val := by
      have hv : (u : ZMod N).val = a % N := by
        simp only [u, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      rw [hτ, hv]
      conv_lhs => rw [← Nat.mod_add_div a N]
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    have hcyc : alpogeNativeCyclotomicGalEquiv e q d τ = u :=
      alpogeNativeCyclotomicGalEquiv_eq_of_zeta_pow e q d u τ hτu
    have hprincipal : Formalism.HC.PChar.one.val a = 1 := by
      change (1 : DirichletCharacter ℂ 1) (a : ZMod 1) = 1
      rw [show (a : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
    have hker := nativeDyadicRecMap_unitOfCoprime_eq_one_iff e q d a ha
    change alpogeNativeRecMap e q d u = 1 ↔ _ at hker
    rw [← hcyc] at hker
    exact (alpogeNativeCyclotomic_fixes_hostField_iff e q d τ).trans
      (by simpa only [hprincipal, true_and] using hker)

end RHLean.Analysis.AlpogeThin

end
