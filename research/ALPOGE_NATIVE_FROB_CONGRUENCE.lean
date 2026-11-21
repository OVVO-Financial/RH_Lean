import RHLean.Analysis.AlpogeNativeSharpASKBalance

/-! The actual Frobenius unit and its inertia cosets, before and after the host map. -/

set_option autoImplicit false
noncomputable section
namespace RHLean.Analysis

private theorem frobValIff {N p : ℕ} [NeZero N] (u : (ZMod N)ˣ) :
    alpogeNativeIsFrobUnit N p u ↔
      (u : ZMod N).val ≡ p [MOD ordCompl[p] N] ∧ (u : ZMod N).val ≡ 1 [MOD ordProj[p] N] := by
  have hc (c k : ℕ) : ((u : ZMod N).cast : ZMod c) = (k : ZMod c) ↔
      (u : ZMod N).val ≡ k [MOD c] := by
    rw [← ZMod.natCast_val, ZMod.natCast_eq_natCast_iff]
  exact and_congr (hc _ p) (by simpa only [Nat.cast_one] using hc (ordProj[p] N) 1)

/-- The fallback in the native choice is unreachable for a prime and a nonzero modulus. -/
theorem alpogeNativeFrobUnit_spec (N p : ℕ) (hN : N ≠ 0) (hp : p.Prime) :
    alpogeNativeIsFrobUnit N p (alpogeNativeFrobUnit N p) ∧
      ∀ u, alpogeNativeIsFrobUnit N p u → u = alpogeNativeFrobUnit N p := by
  have : NeZero N := ⟨hN⟩
  have hB := Nat.coprime_ordCompl hp hN
  have hAB : (ordProj[p] N).Coprime (ordCompl[p] N) := hB.pow_left _
  let k := Nat.chineseRemainder hAB 1 p
  have ha : k.val.Coprime (ordProj[p] N) := k.property.1.gcd_eq.trans (Nat.gcd_one_left _)
  have hb : k.val.Coprime (ordCompl[p] N) := k.property.2.gcd_eq.trans hB.gcd_eq_one
  have hk : k.val.Coprime N := by
    simpa only [Nat.ordProj_mul_ordCompl_eq_self] using ha.mul_right hb
  have hex : ∃ u, alpogeNativeIsFrobUnit N p u := by
    refine ⟨ZMod.unitOfCoprime k.val hk, ?_, ?_⟩
    · rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.ordCompl_dvd N p)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 k.property.2
    · rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.ordProj_dvd N p)]
      exact ((ZMod.natCast_eq_natCast_iff _ 1 _).2 k.property.1).trans Nat.cast_one
  have hs : alpogeNativeIsFrobUnit N p (alpogeNativeFrobUnit N p) := by
    rw [alpogeNativeFrobUnit, dite_eq_left hex]
    exact hex.choose_spec
  refine ⟨hs, ?_⟩
  intro u hu
  have a := (frobValIff u).1 hu
  have b := (frobValIff _).1 hs
  have he := (Nat.modEq_and_modEq_iff_modEq_mul hAB).1
    ⟨a.2.trans b.2.symm, a.1.trans b.1.symm⟩
  rw [Nat.ordProj_mul_ordCompl_eq_self] at he
  apply Units.ext
  simpa only [ZMod.natCast_zmod_val] using (ZMod.natCast_eq_natCast_iff _ _ N).2 he

/-- All powers, including exponent zero, on the unreduced group of modular units. -/
theorem alpogeNativeFrobUnit_coset_iff (N p i : ℕ) (hN : N ≠ 0) (hp : p.Prime)
    (u : (ZMod N)ˣ) : u / (alpogeNativeFrobUnit N p) ^ i ∈ alpogeNativeLocalUnits N p ↔
      ((u : ZMod N).cast : ZMod (ordCompl[p] N)) = (p : ZMod (ordCompl[p] N)) ^ i := by
  change (ZMod.unitsMap (Nat.ordCompl_dvd N p)) (u / (alpogeNativeFrobUnit N p) ^ i) = 1 ↔ _
  simp only [map_div, map_pow, div_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val,
    ZMod.unitsMap_val, (alpogeNativeFrobUnit_spec N p hN hp).1.1]

/-- After the host map, the congruence is existential in a lift; injectivity is not required. -/
theorem alpogeNativeFrobUnit_image_iff {G : Type*} [Group G] (N p i : ℕ)
    (hN : N ≠ 0) (hp : p.Prime) (r : (ZMod N)ˣ →* G) (g : G) :
    g / r (alpogeNativeFrobUnit N p) ^ i ∈ (alpogeNativeLocalUnits N p).map r ↔
      ∃ u : (ZMod N)ˣ, r u = g ∧
        ((u : ZMod N).cast : ZMod (ordCompl[p] N)) = (p : ZMod (ordCompl[p] N)) ^ i := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨v * (alpogeNativeFrobUnit N p) ^ i, ?_, (alpogeNativeFrobUnit_coset_iff N p i hN hp _).1 ?_⟩
    · rw [map_mul, map_pow, he, div_mul_cancel]
    · rwa [mul_div_cancel_right]
  · rintro ⟨u, rfl, hu⟩
    exact ⟨u / (alpogeNativeFrobUnit N p) ^ i, (alpogeNativeFrobUnit_coset_iff N p i hN hp u).2 hu,
      by rw [map_div, map_pow]⟩

/-- The actual inertia kernel detects exactly the primes of the primitive conductor.

In Crossley’s example the quadratic characters of conductors 547 and 727 are each twisted by the four powers of an even quartic character modulo 16. This test selects two of the eight characters at 2 and four at each of 547 and 727. Evaluating the surviving primitive characters gives the Euler denominators `1 - T^2`, `1 - T^4` and `(1 - T^2)^2`, respectively. [Calculation at the ramified primes](https://github.com/leecrossley/theta-race-finite-euler-readout/blob/b01619cac6e661a66587a45af435413592d368d0/PROOF.md#L63) and [archived paper](https://doi.org/10.5281/zenodo.24413208).
-/
theorem alpogeNativeLocalUnits_le_ker_iff (N p : ℕ) (hN : N ≠ 0) (hp : p.Prime)
    (χ : DirichletCharacter ℂ N) :
    alpogeNativeLocalUnits N p ≤ χ.toUnitHom.ker ↔ ¬ p ∣ χ.conductor := by
  have : NeZero N := ⟨hN⟩
  calc
    alpogeNativeLocalUnits N p ≤ χ.toUnitHom.ker ↔ χ.FactorsThrough (ordCompl[p] N) :=
      (DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ) (Nat.ordCompl_dvd N p)).symm
    _ ↔ χ.conductor ∣ ordCompl[p] N :=
      DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ (Nat.ordCompl_dvd N p)
    _ ↔ ¬ p ∣ χ.conductor :=
      ⟨fun hd h => Nat.not_dvd_ordCompl hp hN (h.trans hd),
       Nat.dvd_ordCompl_of_dvd_not_dvd χ.conductor_dvd_level⟩

end RHLean.Analysis
