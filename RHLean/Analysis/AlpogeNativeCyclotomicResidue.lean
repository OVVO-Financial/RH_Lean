import RHLean.Analysis.AlpogeNativePrimeLift

/-!
# Residue arithmetic of the actual cyclotomic field

The prime-to-residue-characteristic part of the primitive root retains its
exact order in the residue field. This proves the actual ring-of-integers
inertia criterion and constructs arithmetic Frobenius from the original
cyclotomic exponent, including at ramified primes.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/RootEqOfSubMem.lean`,
`Der.{root_eq_of_sub_mem,val_modEq_iff,val_modEq_one_iff,exists_unit_modEq,`
`zO,zO_prim,tauN_zO,ringHom_ext_zO,charP_quot,zO_sub_mem_iff,`
`tauN_inertia_iff,tauN_frob}`, and `CycBasic.lean`, `Der.{tauN,tauN_root}`.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Ideal
open scoped BigOperators Pointwise

namespace RHLean.Analysis.NativeCyclotomicResidue

abbrev Cyc (N : ℕ) := CyclotomicField N ℚ

def zeta (N : ℕ) [NeZero N] : Cyc N :=
  IsCyclotomicExtension.zeta N ℚ (Cyc N)

theorem zeta_spec (N : ℕ) [NeZero N] : IsPrimitiveRoot (zeta N) N :=
  IsCyclotomicExtension.zeta_spec N ℚ (Cyc N)

def tauN (N : ℕ) [NeZero N] : (ZMod N)ˣ ≃* (Cyc N ≃ₐ[ℚ] Cyc N) :=
  (IsCyclotomicExtension.Rat.galEquivZMod N (Cyc N)).symm

theorem tauN_root (N : ℕ) [NeZero N] (u : (ZMod N)ˣ)
    (w : Cyc N) (hw : w ^ N = 1) : tauN N u w = w ^ (u : ZMod N).val := by
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N (Cyc N) _ hw,
    tauN, MulEquiv.apply_symm_apply]

theorem root_eq_of_sub_mem {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) [hP : P.IsPrime] {m : ℕ}
    (hm : (m : S) ∉ P) {x y : S} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ P) : x = y := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hgeom := geom_sum₂_mul x y m
  rw [hx, hy, sub_self] at hgeom
  rcases mul_eq_zero.1 hgeom with hG | hG
  · exfalso
    have hq : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y := Ideal.Quotient.eq.2 hxy
    have h1 := congrArg (Ideal.Quotient.mk P) hG
    rw [map_sum, map_zero] at h1
    simp only [map_mul, map_pow, hq] at h1
    have h2 : ∀ i ∈ Finset.range m, (Ideal.Quotient.mk P y) ^ i * (Ideal.Quotient.mk P y) ^ (m - 1 - i) =
        (Ideal.Quotient.mk P y) ^ (m - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      rw [Finset.mem_range] at hi
      omega
    rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h3 | h3
    · apply hm
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact h3
    · have h4 : (Ideal.Quotient.mk P y) ^ m = 1 := by rw [← map_pow, hy, map_one]
      have h5 : (Ideal.Quotient.mk P y) ^ m = 0 := by
        rw [show m = m - 1 + 1 by omega, pow_succ, h3, zero_mul]
      rw [h4] at h5
      exact one_ne_zero h5
  · exact sub_eq_zero.1 hG

theorem val_modEq_iff {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) (x : ℕ) :
    (u : ZMod N).val ≡ x [MOD M] ↔ ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = (x : ZMod M) := by
  rw [show ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = ((u : ZMod N).val : ZMod M) from
    ZMod.cast_eq_val _, ZMod.natCast_eq_natCast_iff]

theorem val_modEq_one_iff {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) :
    (u : ZMod N).val ≡ 1 [MOD M] ↔ ZMod.unitsMap h u = 1 := by
  rw [val_modEq_iff h u 1, Nat.cast_one, Units.val_eq_one]

theorem exists_unit_modEq {M N : ℕ} [NeZero N] (h : M ∣ N) (x : ℕ) (hx : x.Coprime M) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ x [MOD M] := by
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective h (ZMod.unitOfCoprime x hx)
  exact ⟨u, (val_modEq_iff h u x).2 (by rw [hu, ZMod.coe_unitOfCoprime])⟩

section Cyc

variable (N : ℕ) [NeZero N]

def zO : 𝓞 (Cyc N) := (zeta_spec N).toInteger

theorem zO_prim : IsPrimitiveRoot (zO N) N := by
  exact (zeta_spec N).toInteger_isPrimitiveRoot

theorem tauN_zO (u : (ZMod N)ˣ) : tauN N u • zO N = zO N ^ (u : ZMod N).val := by
  apply RingOfIntegers.ext
  show (tauN N u) ((zO N : 𝓞 (Cyc N)) : Cyc N) =
    (((zO N) ^ (u : ZMod N).val : 𝓞 (Cyc N)) : Cyc N)
  push_cast
  exact tauN_root N u _ (zeta_spec N).pow_eq_one

theorem ringHom_ext_zO {R : Type*} [CommRing R] (f g : 𝓞 (Cyc N) →+* R) (h : f (zO N) = g (zO N))
    (x : 𝓞 (Cyc N)) : f x = g x := by
  have hx : x ∈ Algebra.adjoin ℤ {zO N} := by
    rw [show Algebra.adjoin ℤ {zO N} = ⊤ from IsCyclotomicExtension.Rat.adjoin_singleton_eq_top (zeta_spec N)]
    exact Algebra.mem_top
  refine Algebra.adjoin_induction (p := fun x _ => f x = g x) (fun y hy => ?_) (fun r => ?_)
    (fun y z _ _ h1 h2 => ?_) (fun y z _ _ h1 h2 => ?_) hx
  · rw [Set.mem_singleton_iff.1 hy]
    exact h
  · simp only [algebraMap_int_eq, eq_intCast, map_intCast]
  · rw [map_add, map_add, h1, h2]
  · rw [map_mul, map_mul, h1, h2]

variable (l : ℕ) [Fact l.Prime] (Q : Ideal (𝓞 (Cyc N))) [Q.IsPrime] [Q.LiesOver (span {(l : ℤ)})]

theorem charP_quot : CharP (𝓞 (Cyc N) ⧸ Q) l := by
  constructor
  intro x
  have hu : Q.under ℤ = span {(l : ℤ)} := (Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)})).symm
  rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem,
    show ((x : ℕ) : 𝓞 (Cyc N)) = algebraMap ℤ (𝓞 (Cyc N)) (x : ℤ) by simp, ← Ideal.mem_comap]
  change (x : ℤ) ∈ Q.under ℤ ↔ _
  rw [hu, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

theorem zO_sub_mem_iff (a b : ℕ) : zO N ^ a - zO N ^ b ∈ Q ↔ a ≡ b [MOD ordCompl[l] N] := by
  let _ := charP_quot N l Q
  have hl : l.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  have hnN : ordProj[l] N * ordCompl[l] N = N := Nat.ordProj_mul_ordCompl_eq_self N l
  have hN'0 : 0 < ordCompl[l] N := Nat.ordCompl_pos l hN0
  have hζ := zO_prim N
  have key1 : ∀ c, Ideal.Quotient.mk Q (zO N ^ (ordCompl[l] N * c)) = 1 := by
    intro c
    have h1 : (Ideal.Quotient.mk Q (zO N ^ (ordCompl[l] N * c)) - 1) ^ (ordProj[l] N) = 0 := by
      rw [sub_pow_char_pow, ← map_pow, ← pow_mul, one_pow,
        show ordCompl[l] N * c * l ^ N.factorization l = N * c by
          rw [mul_right_comm, mul_comm (ordCompl[l] N), hnN],
        pow_mul, hζ.pow_eq_one, one_pow, map_one, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero)).1 h1)
  rw [← Ideal.Quotient.eq]
  constructor
  · intro h
    have h1 : (zO N ^ (ordProj[l] N)) ^ a = (zO N ^ (ordProj[l] N)) ^ b := by
      apply root_eq_of_sub_mem Q (m := ordCompl[l] N)
      · intro hmem
        have h2 : ((ordCompl[l] N : ℕ) : 𝓞 (Cyc N) ⧸ Q) = 0 := by
          rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
          exact hmem
        rw [CharP.cast_eq_zero_iff _ l] at h2
        exact Nat.not_dvd_ordCompl hl hN0 h2
      · have ex : ordProj[l] N * (a * ordCompl[l] N) = N * a := by
          rw [mul_left_comm, hnN, mul_comm]
        rw [← pow_mul, ← pow_mul, ex, pow_mul, hζ.pow_eq_one, one_pow]
      · have ex : ordProj[l] N * (b * ordCompl[l] N) = N * b := by
          rw [mul_left_comm, hnN, mul_comm]
        rw [← pow_mul, ← pow_mul, ex, pow_mul, hζ.pow_eq_one, one_pow]
      · rw [← Ideal.Quotient.eq]
        have e1 : (zO N ^ (ordProj[l] N)) ^ a = (zO N ^ a) ^ (ordProj[l] N) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
        have e2 : (zO N ^ (ordProj[l] N)) ^ b = (zO N ^ b) ^ (ordProj[l] N) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
        rw [e1, e2, map_pow (Ideal.Quotient.mk Q) (zO N ^ a), map_pow (Ideal.Quotient.mk Q) (zO N ^ b), h]
    have hprim : IsPrimitiveRoot (zO N ^ (ordProj[l] N)) (ordCompl[l] N) :=
      hζ.pow_of_dvd (pow_ne_zero _ hl.ne_zero) (Nat.ordProj_dvd N l)
    have e : ∀ c, (zO N ^ (ordProj[l] N)) ^ c = (zO N ^ (ordProj[l] N)) ^ (c % ordCompl[l] N) := fun c => by
      conv_lhs => rw [← Nat.mod_add_div c (ordCompl[l] N), pow_add, pow_mul, hprim.pow_eq_one, one_pow, mul_one]
    rw [e a, e b] at h1
    exact hprim.pow_inj (Nat.mod_lt _ hN'0) (Nat.mod_lt _ hN'0) h1
  · intro h
    rcases le_total b a with hab | hab
    · obtain ⟨c, hc⟩ : ordCompl[l] N ∣ a - b := (Nat.modEq_iff_dvd' hab).1 h.symm
      have hac : a = b + ordCompl[l] N * c := by omega
      rw [hac, pow_add, map_mul, key1, mul_one]
    · obtain ⟨c, hc⟩ : ordCompl[l] N ∣ b - a := (Nat.modEq_iff_dvd' hab).1 h
      have hbc : b = a + ordCompl[l] N * c := by omega
      rw [hbc, pow_add, map_mul, key1, mul_one]

theorem tauN_inertia_iff (u : (ZMod N)ˣ) :
    (∀ y : 𝓞 (Cyc N), tauN N u • y - y ∈ Q) ↔ (u : ZMod N).val ≡ 1 [MOD ordCompl[l] N] := by
  constructor
  · intro h
    have h1 : zO N ^ (u : ZMod N).val - zO N ^ 1 ∈ Q := by
      rw [pow_one, ← tauN_zO]
      exact h _
    exact (zO_sub_mem_iff N l Q _ 1).1 h1
  · intro hu y
    have hfg := ringHom_ext_zO N ((Ideal.Quotient.mk Q).comp (MulSemiringAction.toRingHom _ _ (tauN N u)))
      (Ideal.Quotient.mk Q) ?_ y
    · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply] at hfg
      exact Ideal.Quotient.eq.1 hfg
    · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
      rw [tauN_zO]
      have h1 := (zO_sub_mem_iff N l Q _ 1).2 hu
      rw [pow_one] at h1
      exact Ideal.Quotient.eq.2 h1

theorem tauN_frob (u : (ZMod N)ˣ) (hu : (u : ZMod N).val ≡ l [MOD ordCompl[l] N]) : IsArithFrobAt ℤ (tauN N u) Q := by
  let _ := charP_quot N l Q
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = l := by
    rw [← Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)}),
      Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]
  unfold IsArithFrobAt
  intro y
  rw [hcard]
  simp only [MulSemiringAction.toAlgHom_apply]
  have hfg := ringHom_ext_zO N ((Ideal.Quotient.mk Q).comp (MulSemiringAction.toRingHom _ _ (tauN N u)))
    ((frobenius (𝓞 (Cyc N) ⧸ Q) l).comp (Ideal.Quotient.mk Q)) ?_ y
  · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, frobenius_def, ← map_pow] at hfg
    exact Ideal.Quotient.eq.1 hfg
  · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, frobenius_def, ← map_pow]
    rw [tauN_zO]
    exact Ideal.Quotient.eq.2 ((zO_sub_mem_iff N l Q _ l).2 hu)

end Cyc

end RHLean.Analysis.NativeCyclotomicResidue

end
