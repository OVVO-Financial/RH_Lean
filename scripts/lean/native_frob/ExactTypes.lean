import «research.ALPOGE_NATIVE_FROB_CONGRUENCE»

set_option autoImplicit false
open RHLean.Analysis

example (N p : ℕ) (hn : N ≠ 0) (hp : p.Prime) :
    alpogeNativeIsFrobUnit N p (alpogeNativeFrobUnit N p) ∧
      ∀ w, alpogeNativeIsFrobUnit N p w → w = alpogeNativeFrobUnit N p :=
  alpogeNativeFrobUnit_spec N p hn hp

example (N p i : ℕ) (hn : N ≠ 0) (hp : p.Prime) (u : (ZMod N)ˣ) :
    u / alpogeNativeFrobUnit N p ^ i ∈ alpogeNativeLocalUnits N p ↔
      ((u : ZMod N).cast : ZMod (ordCompl[p] N)) = (p : ZMod (ordCompl[p] N)) ^ i :=
  alpogeNativeFrobUnit_coset_iff N p i hn hp u

example {G : Type*} [Group G] (N p i : ℕ) (hn : N ≠ 0) (hp : p.Prime)
    (r : (ZMod N)ˣ →* G) (g : G) :
    g / r (alpogeNativeFrobUnit N p) ^ i ∈ (alpogeNativeLocalUnits N p).map r ↔
      ∃ u : (ZMod N)ˣ, r u = g ∧
        ((u : ZMod N).cast : ZMod (ordCompl[p] N)) = (p : ZMod (ordCompl[p] N)) ^ i :=
  alpogeNativeFrobUnit_image_iff N p i hn hp r g

example (N p : ℕ) (hn : N ≠ 0) (hp : p.Prime) (χ : DirichletCharacter ℂ N) :
    alpogeNativeLocalUnits N p ≤ χ.toUnitHom.ker ↔ ¬ p ∣ χ.conductor :=
  alpogeNativeLocalUnits_le_ker_iff N p hn hp χ

example : alpogeNativeFrobUnit 12 2 = ZMod.unitOfCoprime 5 (by decide) := by
  symm
  apply (alpogeNativeFrobUnit_spec 12 2 (by decide) Nat.prime_two).2
  have hB : ordCompl[2] 12 = 3 :=
    Nat.ordCompl_pow_mul_of_not_dvd (m := 3) 2 Nat.prime_two (by decide)
  have hA : ordProj[2] 12 = 4 := by
    have h := Nat.ordProj_mul_ordCompl_eq_self 12 2
    rw [hB] at h
    omega
  constructor
  · simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.ordCompl_dvd 12 2), hB]
      using (show (5 : ZMod 3) = 2 by decide)
  · simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.ordProj_dvd 12 2), hA]
      using (show (5 : ZMod 4) = 1 by decide)
