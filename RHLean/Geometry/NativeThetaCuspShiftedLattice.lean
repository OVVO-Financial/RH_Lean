import RHLean.Geometry.NativeThetaCuspAmbient
import RHLean.Geometry.NativeThetaCuspSplitLevel

/-!
# The actual conjugate-level shift is self-dual

The shifted lattice is literally `{x | conjugate(m) * x ⊆ m * L}` in the
original E-space. Its self-duality is proved from the same rational trace
pairing. The native application constructs m from the fixed five-level and
uses the actual inverse-half-different lattice, including every negative
diagonal coordinate. Neither a shifted self-duality premise nor a principal
replacement for the projective coefficient module is introduced.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/
LevelStructureProperties.lean (`cop_iff`, `exists_gen`, `selfD_idq`), and
Definitions/SpanningFamilies/IsSystem.lean (`idq`, `SelfD`). Only their
ring-theoretic proof cut is used. The source mirror states no license;
attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField Module
open scoped Pointwise nonZeroDivisors BigOperators

namespace RHLean.Geometry.NativeTheta.Cusp.ShiftedLattice

section Ring

variable {O : Type} [CommRing O] {a b : Ideal O} {s t : O}

private theorem cop_iff : IsCoprime (Ideal.span {s}) a ↔
    ∃ c, ∃ m ∈ a, c * s + m = 1 := by
  rw [Ideal.isCoprime_iff_exists]
  constructor
  · rintro ⟨x, hx, m, hm, h⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact ⟨c, m, hm, h⟩
  · rintro ⟨c, m, hm, h⟩
    exact ⟨_, Ideal.mem_span_singleton'.2 ⟨c, rfl⟩, m, hm, h⟩

private theorem cop_ne_zero (ha : a ≠ ⊤)
    (hs : IsCoprime (Ideal.span {s}) a) : s ≠ 0 := by
  rintro rfl
  obtain ⟨c, m, hm, h⟩ := cop_iff.1 hs
  exact ha ((Ideal.eq_top_iff_one _).2 (by rw [← h]; simpa using hm))

private theorem exists_gen [IsDedekindDomain O]
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hb' : b ≠ ⊤) :
    ∃ p ∈ a, p ≠ 0 ∧ ∃ t, IsCoprime (Ideal.span {t}) b ∧
      ∀ z ∈ a, ∃ c, t * z = p * c := by
  obtain ⟨p, hp⟩ := IsDedekindDomain.exists_sup_span_eq
    (I := a * b) (J := a) Ideal.mul_le_left (mul_ne_zero ha hb)
  have hle : Ideal.span {p} ≤ a := le_sup_right.trans hp.le
  obtain ⟨c, hc⟩ := Ideal.dvd_iff_le.2 hle
  have h1 : b ⊔ c = ⊤ := by
    apply mul_left_cancel₀ ha
    rw [Ideal.mul_sup, ← hc, hp, Ideal.mul_top]
  obtain ⟨m, hm, t, ht, e⟩ := Submodule.mem_sup.1
    (h1 ▸ Submodule.mem_top : (1 : O) ∈ b ⊔ c)
  have hcop : IsCoprime (Ideal.span {t}) b :=
    cop_iff.2 ⟨1, m, hm, by linear_combination e⟩
  have key : ∀ z ∈ a, ∃ d, t * z = p * d := fun z hz => by
    have : z * t ∈ Ideal.span {p} := hc ▸ Ideal.mul_mem_mul hz ht
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨d, by linear_combination -hd⟩
  refine ⟨p, hle (Ideal.mem_span_singleton_self p), ?_, t, hcop, key⟩
  rintro rfl
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
  obtain ⟨d, hd⟩ := key z hz
  exact mul_ne_zero (cop_ne_zero hb' hcop) hz0 (by simpa using hd)

variable {M : Type} [AddCommGroup M] [Module O M]

/-- The source ideal quotient on the unchanged ambient module. -/
def idq (a b : Ideal O) (L : Submodule O M) : Submodule O M where
  carrier := {v | ∀ c ∈ b, c • v ∈ a • L}
  add_mem' := fun hu hv c hc => by
    rw [smul_add]
    exact add_mem (hu c hc) (hv c hc)
  zero_mem' := fun c _ => by rw [smul_zero]; exact zero_mem _
  smul_mem' := fun c _ hv d hd => by
    rw [smul_comm]
    exact Submodule.smul_mem _ c (hv d hd)

theorem smul_le_idq (a b : Ideal O) (L : Submodule O M) :
    a • L ≤ idq a b L := fun _ hv c _ => Submodule.smul_mem _ c hv

private theorem mem_of_coprime_multiple {L : Submodule O M} {v : M}
    (hv : v ∈ L) (hs : IsCoprime (Ideal.span {s}) a)
    (hsv : s • v ∈ a • L) : v ∈ a • L := by
  obtain ⟨c, m, hm, e⟩ := cop_iff.1 hs
  rw [← one_smul O v, ← e, add_smul, mul_smul]
  exact add_mem ((a • L).smul_mem _ hsv) (Submodule.smul_mem_smul hm hv)

end Ring

open RHLean.Analysis.AlpogeThin
open Formalism.HC Formalism.FrobeniusOrbits NativeRawHostPolarization
open NativePrescribedHermitian

variable {φ : Frame} (H : HostRaw φ)

/-- The actual integral conjugation induced by the native Galois element. -/
def bar : 𝓞 H.E →+* 𝓞 H.E :=
  (MulSemiringAction.toRingEquiv _ (𝓞 H.E) H.conj).toRingHom

@[simp] theorem coe_bar (a : 𝓞 H.E) : ((bar H a : 𝓞 H.E) : H.E) = H.conj (a : H.E) := rfl

@[simp] theorem bar_bar (a : 𝓞 H.E) : bar H (bar H a) = a :=
  Subtype.ext (conj_conj H (a : H.E))

theorem mem_conjugate {P : Ideal (𝓞 H.E)} {a : 𝓞 H.E} :
    a ∈ H.conj • P ↔ bar H a ∈ P := by
  have hc : H.conj⁻¹ = H.conj := by
    apply mul_left_cancel (a := H.conj)
    rw [mul_inv_cancel, NativeRawHostDifferent.conj_sq]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, hc]
  rfl

/-- Finite generation and exact integral trace self-duality in the original
field ambient. -/
def SelfDual {N : ℕ} (neg : Fin N → Bool)
    (L : Submodule (𝓞 H.E) (Fin N → H.E)) : Prop :=
  L.FG ∧ ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, Ambient.pair H neg x y = k

/-- Conjugate ideal quotients preserve the actual self-dual trace lattice. -/
theorem selfDual_idq {N : ℕ} (neg : Fin N → Bool)
    {P : Ideal (𝓞 H.E)} (h0 : P ≠ ⊥) (h1 : P ≠ ⊤)
    (hc : IsCoprime P (H.conj • P))
    {L : Submodule (𝓞 H.E) (Fin N → H.E)} (hL : SelfDual H neg L) :
    SelfDual H neg (idq P (H.conj • P) L) := by
  have hb {a : 𝓞 H.E} (ha : a ∈ P) : bar H a ∈ H.conj • P :=
    (mem_conjugate H).2 (by rwa [bar_bar])
  obtain ⟨p, hp, hp0, t, ht, hgen⟩ := exists_gen h0 h0 h1
  have hp0' : (p : H.E) ≠ 0 := by simpa using hp0
  refine ⟨?_, fun x => ⟨fun hx y hy => ?_, fun h b hb' => ?_⟩⟩
  · have hq : bar H p ≠ 0 := fun e => hp0 (by rw [← bar_bar H p, e, map_zero])
    refine Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 H.E) _ (bar H p))
      (LinearMap.lsmul_injective hq) ?_
    refine Submodule.FG.of_le hL.1 ?_
    rintro _ ⟨v, hv, rfl⟩
    exact Submodule.smul_le_right (hv _ (hb hp))
  · obtain ⟨m, hm, m', hm', e⟩ := Ideal.isCoprime_iff_exists.1 hc
    have k1 : ∀ z ∈ P • L, ∃ k : ℤ, Ambient.pair H neg x z = k := fun z hz => by
      refine Submodule.smul_induction_on hz (fun a ha l hl => ?_) ?_
      · rw [← bar_bar H a, ← Ambient.pair_adjoint]
        exact (hL.2 _).1 (Submodule.smul_le_right (hx _ (hb ha))) l hl
      · rintro u v ⟨k, hk⟩ ⟨l, hl⟩
        exact ⟨k + l, by rw [Ambient.pair_add_right, hk, hl, Int.cast_add]⟩
    have k2 : ∀ z ∈ P • L, ∃ k : ℤ, Ambient.pair H neg z y = k := fun z hz => by
      refine Submodule.smul_induction_on hz (fun a ha l hl => ?_) ?_
      · rw [Ambient.pair_adjoint]
        exact (hL.2 _).1 hl _ (Submodule.smul_le_right (hy _ (hb ha)))
      · rintro u v ⟨k, hk⟩ ⟨l, hl⟩
        exact ⟨k + l, by rw [Ambient.pair_add_left, hk, hl, Int.cast_add]⟩
    obtain ⟨k, hk⟩ := k1 _ (hy _ (hb hm))
    obtain ⟨l, hl⟩ := k2 _ (hx _ hm')
    refine ⟨k + l, ?_⟩
    rw [← one_smul (𝓞 H.E) x, ← e, add_smul, Ambient.pair_add_left,
      Ambient.pair_adjoint, hk, hl, Int.cast_add]
  · have hm := (mem_conjugate H).1 hb'
    have hz : b • x ∈ L := (hL.2 _).2 fun l hl => by
      rw [Ambient.pair_adjoint]
      exact h _ (smul_le_idq _ _ _ (Submodule.smul_mem_smul hm hl))
    apply mem_of_coprime_multiple hz ht
    have hw : ((t : H.E) * b / p) • x ∈ L := (hL.2 _).2 fun l hl => by
      rw [Ambient.pair_adjoint_field]
      refine h _ fun a ha => ?_
      obtain ⟨c, hc⟩ := hgen _ ((mem_conjugate H).1 ha)
      have he : a • H.conj ((t : H.E) * b / p) • l = bar H b • bar H c • l := by
        have e : (t : H.E) * H.conj (a : H.E) = p * c := by
          rw [← coe_bar]
          exact_mod_cast congrArg (fun z : 𝓞 H.E => (z : H.E)) hc
        change (a : H.E) • H.conj ((t : H.E) * b / p) • l =
          ((bar H b : 𝓞 H.E) : H.E) • ((bar H c : 𝓞 H.E) : H.E) • l
        rw [smul_smul, smul_smul, coe_bar, coe_bar]
        congr 1
        have e2 : (c : H.E) = t * H.conj (a : H.E) / p := by rw [e]; field_simp
        rw [e2]
        simp only [map_mul, map_div₀, conj_conj]
        ring
      rw [he]
      exact Submodule.smul_mem_smul hm (L.smul_mem _ hl)
    have he : t • b • x = p • ((t : H.E) * b / p) • x := by
      change (t : H.E) • (b : H.E) • x = (p : H.E) • ((t : H.E) * b / p) • x
      rw [smul_smul, smul_smul]
      congr 1
      field_simp
    rw [he]
    exact Submodule.smul_mem_smul hp hw

attribute [local instance] NativeRawHostPolarization.conjugationStar

private theorem pair_single_signed {N : ℕ} (neg : Fin N → Bool)
    (x : Fin N → H.E) (i : Fin N) (y : H.E) :
    Ambient.pair H neg x (Pi.single i ((sgn (neg i) : H.E) * y)) =
      Algebra.trace ℚ H.E (xi H * H.conj (x i) * y) := by
  have he : diagForm N neg x (Pi.single i ((sgn (neg i) : H.E) * y)) =
      H.conj (x i) * y := by
    simp only [diagForm_apply, Pi.single_apply, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change H.conj (x i) * sgn (neg i) * (sgn (neg i) * y) = _
    rw [mul_assoc, ← mul_assoc (sgn (neg i) : H.E), sgn_mul_self, one_mul]
  rw [Ambient.pair, he, mul_assoc]

/-- Self-duality of the unchanged projective coefficient lattice in every
original signed coordinate follows from the proved coefficient duality. -/
theorem twisted_selfDual (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) : SelfDual H neg (twistedLattice H B N) := by
  have := twistedLattice_finite H B N
  refine ⟨Module.Finite.iff_fg.mp inferInstance, fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩⟩
  · exact ⟨twistedTraceForm H B hB neg ⟨x, hx⟩ ⟨y, hy⟩,
      (twistedTraceForm_cast H B hB neg ⟨x, hx⟩ ⟨y, hy⟩).symm⟩
  · apply (mem_twistedLattice H B N x).2
    intro i
    apply (mem_coefficientIdeal_iff H B hB (x i)).2
    intro y hy
    have htest : Pi.single i ((sgn (neg i) : H.E) * y) ∈ twistedLattice H B N := by
      apply (mem_twistedLattice H B N _).2
      intro j
      by_cases hj : j = i
      · subst j
        simpa only [Pi.single_eq_same, Algebra.smul_def, map_sgn] using
          (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).smul_mem
            (sgn (neg i) : 𝓞 H.E) hy
      · simpa only [Pi.single_eq_of_ne hj] using
          (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).zero_mem
    obtain ⟨z, hz⟩ := hx _ htest
    rw [pair_single_signed] at hz
    exact ⟨z, hz.symm⟩

/-- A literal self-dual shifted lattice at the fixed native five-level,
with its original properness, coprimality and oddness conditions. -/
theorem exists_five_shifted_selfDual
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (N : ℕ) (neg : Fin N → Bool) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ m : Ideal (𝓞 H.E), m ≠ ⊤ ∧ m ≠ ⊥ ∧
      IsCoprime m (H.conj • m) ∧ IsCoprime m (Ideal.span {(2 : 𝓞 H.E)}) ∧
      m * (H.conj • m) = Ideal.span {(5 : 𝓞 H.E)} ∧
      SelfDual H neg (idq m (H.conj • m) (twistedLattice H B N)) := by
  let H := nativeDyadicHostRaw e q d he hH
  obtain ⟨m, hm1, hm0, hc, ho, hprod⟩ := SplitLevel.exists_five_split_level e q d he hH
  exact ⟨m, hm1, hm0, hc, ho, hprod,
    selfDual_idq H neg hm0 hm1 hc (twisted_selfDual H B hB neg)⟩

end RHLean.Geometry.NativeTheta.Cusp.ShiftedLattice
