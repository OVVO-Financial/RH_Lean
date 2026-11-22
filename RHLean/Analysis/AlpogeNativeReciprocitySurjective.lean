import RHLean.Analysis.AlpogeNativeSharpASKBalance

/-!
# Surjectivity of the actual native dyadic reciprocity map

The two sign coordinates are the quadratic characters at the original odd
primes q,d. The third coordinate is the full dyadic unit quotient already
defined in RH_Lean. Three-factor CRT realizes all three coordinates at once.

This proves the missing onto property of `alpogeNativeRecMap`; it does not
replace the native host by an abstract surjective map or a one-point host.
The finite argument follows the CRT/sign mechanism of Alpöge's
`art0_surjective` in ArtinMapSecondEqJacobiSymOfModEq.lean at
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
directly on the existing RH_Lean residue map.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Analysis

/-- The genuine conductor is nonzero for the selected prime factors. -/
@[instance] theorem alpogeNativeHostN_neZero (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    NeZero (alpogeNativeHostN e q d) :=
  ⟨mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
      (show q.Prime from Fact.out).ne_zero)
    (show d.Prime from Fact.out).ne_zero⟩

private theorem nativeUnits_crt
    {N a b : ℕ} (hN : N = a * b) (hab : a.Coprime b)
    (ha : a ∣ N) (hb : b ∣ N)
    (x : (ZMod a)ˣ) (y : (ZMod b)ˣ) :
    ∃ u : (ZMod N)ˣ,
      ZMod.unitsMap ha u = x ∧ ZMod.unitsMap hb u = y := by
  subst hN
  let E := ZMod.chineseRemainder hab
  refine ⟨Units.map E.symm.toMonoidHom
    (MulEquiv.prodUnits.symm (x, y)), ?_, ?_⟩
  · apply Units.ext
    change ((E.symm ((x : ZMod a), (y : ZMod b))).cast : ZMod a) = x
    have h3 : ∀ z : ZMod (a * b), (E z).1 = (z.cast : ZMod a) :=
      fun z => Prod.fst_zmod_cast z
    rw [← h3, E.apply_symm_apply]
  · apply Units.ext
    change ((E.symm ((x : ZMod a), (y : ZMod b))).cast : ZMod b) = y
    have h3 : ∀ z : ZMod (a * b), (E z).2 = (z.cast : ZMod b) :=
      fun z => Prod.snd_zmod_cast z
    rw [← h3, E.apply_symm_apply]

private theorem nativeQuadraticSign_exists
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (b : ZMod 2) :
    ∃ u : (ZMod p)ˣ,
      Multiplicative.toAdd
        (alpogeNativeSign2 ((quadraticChar (ZMod p)).toUnitHom u)) = b := by
  have hb : b = 0 ∨ b = 1 := by
    have hall : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact hall b
  rcases hb with rfl | rfl
  · refine ⟨1, ?_⟩
    simp only [map_one]
    rfl
  · obtain ⟨u, hu⟩ := quadraticChar_exists_neg_one'
      (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp2)
    have hunit : (quadraticChar (ZMod p)).toUnitHom u = -1 := by
      apply Units.ext
      simpa only [MulChar.coe_toUnitHom, Units.val_neg, Units.val_one] using hu
    refine ⟨u, ?_⟩
    rw [hunit]
    change (if (-1 : ℤˣ) = 1 then (0 : ZMod 2) else 1) = 1
    exact ite_eq_right (by decide)

/-- The full dyadic arithmetic reciprocity map is onto for distinct odd
primes. Both independent quadratic bits and every dyadic quotient class are
realized by one actual unit of the original conductor modulus. -/
theorem alpogeNativeRecMap_surjective
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d) :
    Function.Surjective (alpogeNativeRecMap e q d) := by
  have hq : q.Prime := Fact.out
  have hd : d.Prime := Fact.out
  have h2q : (2 ^ (e + 2)).Coprime q :=
    ((Nat.coprime_primes Nat.prime_two hq).2 hq2.symm).pow_left _
  have h2d : (2 ^ (e + 2)).Coprime d :=
    ((Nat.coprime_primes Nat.prime_two hd).2 hd2.symm).pow_left _
  have hcqd : q.Coprime d := (Nat.coprime_primes hq hd).2 hqd
  intro g
  obtain ⟨v2, hv2⟩ := QuotientGroup.mk_surjective (Additive.toMul g.toAdd.2)
  obtain ⟨vq, hvq⟩ := nativeQuadraticSign_exists q hq2 g.toAdd.1.2
  obtain ⟨vd, hvd⟩ := nativeQuadraticSign_exists d hd2 g.toAdd.1.1
  obtain ⟨u12, h12two, h12q⟩ := nativeUnits_crt
    (N := 2 ^ (e + 2) * q) rfl h2q
    (dvd_mul_right _ _) (dvd_mul_left _ _) v2 vq
  have h12N : 2 ^ (e + 2) * q ∣ alpogeNativeHostN e q d :=
    dvd_mul_right (2 ^ (e + 2) * q) d
  obtain ⟨u, hu12, hud⟩ := nativeUnits_crt
    (N := alpogeNativeHostN e q d) rfl (h2d.mul_left hcqd)
    h12N (alpogeNativeD_dvd_hostN e q d) u12 vd
  have hu2 : ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) u = v2 := by
    calc
      _ = ZMod.unitsMap (dvd_mul_right (2 ^ (e + 2)) q)
          (ZMod.unitsMap h12N u) := by
        exact DFunLike.congr_fun
          (ZMod.unitsMap_comp (dvd_mul_right (2 ^ (e + 2)) q) h12N).symm u
      _ = v2 :=
        (congrArg (ZMod.unitsMap (dvd_mul_right (2 ^ (e + 2)) q)) hu12).trans h12two
  have huq : ZMod.unitsMap (alpogeNativeQ_dvd_hostN e q d) u = vq := by
    calc
      _ = ZMod.unitsMap (dvd_mul_left q (2 ^ (e + 2)))
          (ZMod.unitsMap h12N u) := by
        exact DFunLike.congr_fun
          (ZMod.unitsMap_comp (dvd_mul_left q (2 ^ (e + 2))) h12N).symm u
      _ = vq :=
        (congrArg (ZMod.unitsMap (dvd_mul_left q (2 ^ (e + 2)))) hu12).trans h12q
  refine ⟨u, ?_⟩
  apply Multiplicative.ext
  apply Prod.ext
  · apply Prod.ext
    · change Multiplicative.toAdd
        (alpogeNativeSign2 ((quadraticChar (ZMod d)).toUnitHom
          (ZMod.unitsMap (alpogeNativeD_dvd_hostN e q d) u))) = g.toAdd.1.1
      rw [hud]
      exact hvd
    · change Multiplicative.toAdd
        (alpogeNativeSign2 ((quadraticChar (ZMod q)).toUnitHom
          (ZMod.unitsMap (alpogeNativeQ_dvd_hostN e q d) u))) = g.toAdd.1.2
      rw [huq]
      exact hvq
  · change Additive.ofMul
      (QuotientGroup.mk (ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d) u)) =
        g.toAdd.2
    rw [hu2]
    exact congrArg Additive.ofMul hv2

end RHLean.Analysis
