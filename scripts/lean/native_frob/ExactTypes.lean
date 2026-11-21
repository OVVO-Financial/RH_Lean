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

example : alpogeNativeFrobUnit 12 2 = ZMod.unitOfCoprime 5 (by decide) := by
  symm
  apply (alpogeNativeFrobUnit_spec 12 2 (by decide) Nat.prime_two).2
  constructor <;> decide
