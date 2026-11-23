import RHLean.Analysis.AlpogeNativeQuadraticSignRoot
import RHLean.Analysis.AlpogeNativeCMUnramified
import RHLean.Analysis.AlpogeThin.NativeDyadicHostPrimes
import RHLean.Analysis.AlpogeThin.NativeDyadicHostSideConditions

/-!
# The original CM and character fields on the constructed raw host

The full original CM type, its half-degree cardinality, the two sign actions,
the second nonzero quadratic root and the Artin character identities are
proved for the SAME native raw host. The field degree and CM involution come
from the already constructed fixed field; the q-sign root is its actual
q-Gauss sum, not an element of a separately chosen quadratic field.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/CycAll.lean`, `Der.{I_sqrt_ne_zero,emb_sqd,cmType_iff,`
`cmType,ps_root}`, `CycBasic.lean`, `Der.art_ch`, and `CycGrp.lean`, `Der.ps_d`.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits

namespace NativeRawHostCore

theorem sqd_ne_zero {φ : Frame} (H : HostRaw φ) : H.sqd ≠ 0 := by
  intro h
  have hs := H.sqd_sq
  rw [h] at hs
  have hd : H.d = 0 := by simpa using hs.symm
  exact H.hyp.2.1.ne_zero hd

theorem gal_mem_Psi_iff {φ : Frame} (H : HostRaw φ) (σ : H.E ≃ₐ[ℚ] H.E) :
    H.gal σ ∈ φ.Psi ↔ σ H.sqd = H.sqd := by
  rw [H.gal_sqd σ]
  change (H.gal σ).1.2 = 1 ↔ _
  rcases Int.units_eq_one_or (H.gal σ).1.2 with h | h <;> rw [h]
  · simp
  · constructor
    · intro h2
      exact absurd h2 (by decide)
    · intro h2
      exfalso
      apply sqd_ne_zero H
      have hsign : ((((-1 : ℤˣ) : ℤ) : H.E)) = -1 := by simp
      rw [hsign] at h2
      have hzero : (2 : H.E) * H.sqd = 0 := by linear_combination -h2
      exact (mul_eq_zero.mp hzero).resolve_left two_ne_zero

theorem I_sqrt_ne_zero {φ : Frame} (H : HostRaw φ) :
    Complex.I * (Real.sqrt H.d : ℂ) ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hd).ne')

theorem emb_sqd {φ : Frame} (H : HostRaw φ) (ψ : H.E →+* ℂ) :
    ψ H.sqd = Complex.I * (Real.sqrt H.d : ℂ) ∨
      ψ H.sqd = -(Complex.I * (Real.sqrt H.d : ℂ)) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  have hs : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = (H.d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), Complex.ofReal_natCast]
  rw [← map_pow, H.sqd_sq, map_neg, map_natCast, mul_pow, Complex.I_sq, hs, neg_one_mul]

theorem cmType_iff {φ : Frame} (H : HostRaw φ) (ψ : H.E →+* ℂ) :
    ψ ∈ H.cmType ↔ (starRingEnd ℂ).comp ψ ∉ H.cmType := by
  have hc : starRingEnd ℂ (Complex.I * (Real.sqrt H.d : ℂ)) =
      -(Complex.I * (Real.sqrt H.d : ℂ)) := by simp
  have hneg : -(Complex.I * (Real.sqrt H.d : ℂ)) ≠
      Complex.I * (Real.sqrt H.d : ℂ) := by
    intro h
    apply I_sqrt_ne_zero H
    linear_combination (-1 / 2 : ℂ) * h
  change ψ H.sqd = _ ↔ ¬ starRingEnd ℂ (ψ H.sqd) = _
  constructor
  · intro h hconj
    rw [h, hc] at hconj
    exact hneg hconj
  · intro hconj
    exact (emb_sqd H ψ).resolve_right fun h =>
      hconj (by rw [h, map_neg, hc, neg_neg])

/-- The source CM-type cardinality follows from the actual field degree.
The final native theorem below supplies that degree from the fixed field. -/
theorem cmType {φ : Frame} (H : HostRaw φ)
    (hfin : Module.finrank ℚ H.E = 4 * φ.ord) :
    (∀ ψ : H.E →+* ℂ, ψ ∈ H.cmType ↔ (starRingEnd ℂ).comp ψ ∉ H.cmType) ∧
      H.cmType.ncard = 2 * φ.ord ∧
      ∀ ψ ∈ H.cmType, ∀ σ : H.E ≃ₐ[ℚ] H.E,
        ψ.comp (σ : H.E →+* H.E) ∈ H.cmType ↔ H.gal σ ∈ φ.Psi := by
  refine ⟨cmType_iff H, ?_, fun ψ hψ σ => ?_⟩
  · have hinv : Function.Involutive (fun ψ : H.E →+* ℂ => (starRingEnd ℂ).comp ψ) := by
      intro ψ
      ext x
      simp
    have hcompl : H.cmTypeᶜ = (fun ψ : H.E →+* ℂ => (starRingEnd ℂ).comp ψ) '' H.cmType := by
      ext ψ
      constructor
      · intro h
        refine ⟨_, (cmType_iff H ((starRingEnd ℂ).comp ψ)).mpr ?_, hinv ψ⟩
        exact Eq.mpr (congrArg (fun χ : H.E →+* ℂ => χ ∉ H.cmType) (hinv ψ)) h
      · rintro ⟨χ, hχ, rfl⟩
        exact (cmType_iff H χ).mp hχ
    have hcard := Set.ncard_add_ncard_compl H.cmType
    rw [hcompl, Set.ncard_image_of_injective _ hinv.injective,
      Nat.card_eq_fintype_card, Embeddings.card, hfin] at hcard
    omega
  · rw [gal_mem_Psi_iff]
    have hvalue : ψ H.sqd = _ := hψ
    show ψ (σ H.sqd) = _ ↔ _
    rw [← hvalue]
    exact ψ.injective.eq_iff

end NativeRawHostCore

theorem nativeDyadicHostRaw_art_surj
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    Function.Surjective (nativeDyadicHostRaw e q d he hH).art := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  exact nativeDyadicArt_surjective e q d (by omega) (by omega) (by omega)

theorem nativeDyadicHostRaw_cm
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    IsCMField (nativeDyadicHostRaw e q d he hH).E := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  exact alpogeNativeHostField_isCMField e q d
    (by omega) (by omega) (by omega) (by omega) (by omega)

theorem nativeDyadicHostRaw_finrank_E
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    Module.finrank ℚ (nativeDyadicHostRaw e q d he hH).E =
      4 * (nativeDyadicFrame e).ord := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  rw [nativeDyadicFrame_ord]
  exact alpogeNativeHostField_finrank e q d (by omega) (by omega) (by omega)

theorem nativeDyadicHostRaw_conj_iff
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (ψ : H.E →+* ℂ) (σ : H.E ≃ₐ[ℚ] H.E),
      (∀ x, ψ (σ x) = starRingEnd ℂ (ψ x)) ↔ H.gal σ = (nativeDyadicFrame e).cc := by
  dsimp only
  intro ψ σ
  let H := nativeDyadicHostRaw e q d he hH
  constructor
  · intro h
    have hσ : σ = H.conj := by
      rw [nativeDyadicHostRaw_conj]
      exact AlgEquiv.ext fun x => ψ.injective
        ((h x).trans (alpogeNativeHostConj_apply e q d ψ x).symm)
    rw [hσ, HostRaw.conj, MulEquiv.apply_symm_apply]
  · intro h
    have hσ : σ = H.conj := H.gal.injective
      (h.trans (H.gal.apply_symm_apply (nativeDyadicFrame e).cc).symm)
    rw [hσ, nativeDyadicHostRaw_conj]
    exact alpogeNativeHostConj_apply e q d ψ

theorem nativeDyadicHostRaw_mem_F
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ x : H.E, x ∈ H.F ↔ H.conj x = x := by
  dsimp only
  rw [nativeDyadicHostRaw_conj e q d he hH]
  change ∀ x : alpogeNativeHostField e q d,
    x ∈ maximalRealSubfield (alpogeNativeHostField e q d) ↔
      alpogeNativeHostConj e q d x = x
  let _ : IsCMField (alpogeNativeHostField e q d) :=
    nativeDyadicHostRaw_cm e q d he hH
  intro x
  rw [← alpogeNativeHostConj_complexConj e q d x]
  exact (IsCMField.complexConj_eq_self_iff (alpogeNativeHostField e q d) x).symm

theorem nativeDyadicHostRaw_cmType
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    (∀ ψ : H.E →+* ℂ, ψ ∈ H.cmType ↔ (starRingEnd ℂ).comp ψ ∉ H.cmType) ∧
      H.cmType.ncard = 2 * (nativeDyadicFrame e).ord ∧
      ∀ ψ ∈ H.cmType, ∀ σ : H.E ≃ₐ[ℚ] H.E,
        ψ.comp (σ : H.E →+* H.E) ∈ H.cmType ↔ H.gal σ ∈ (nativeDyadicFrame e).Psi :=
  NativeRawHostCore.cmType (nativeDyadicHostRaw e q d he hH)
    (nativeDyadicHostRaw_finrank_E e q d he hH)

theorem nativeDyadicFullHostEquiv_chQ_val
    (e : ℕ) (g : Multiplicative (AlpogeNativeE0 × AlpogeNativeDyadicH e)) :
    (((nativeDyadicFullHostEquiv e g).1.1 : ℤˣ) : ℤ) =
      if g.toAdd.1.2 = 0 then 1 else -1 :=
  nativeDyadicSignEquiv_symm_val _

/-- The original q-sign witness is the actual q-Gauss root in the same E. -/
theorem nativeDyadicHostRaw_ps_root
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ a : H.E, a ≠ 0 ∧ ∀ σ : H.E ≃ₐ[ℚ] H.E,
      σ a = ((((H.gal σ).1.1 : ℤˣ) : ℤ) : H.E) * a := by
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hqd : q ≠ d := by omega
  change ∃ a : alpogeNativeHostField e q d, a ≠ 0 ∧
    ∀ σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d,
      σ a = ((((nativeDyadicFieldGal e q d hq2 hd2 hqd σ).1.1 : ℤˣ) : ℤ) :
        alpogeNativeHostField e q d) * a
  refine ⟨alpogeNativeSqrtQ e q d, alpogeNativeSqrtQ_ne_zero e q d (by omega), ?_⟩
  intro σ
  rw [nativeDyadicFieldGal_apply, nativeDyadicFullHostEquiv_chQ_val]
  simpa only [Int.cast_ite, Int.cast_one, Int.cast_neg] using
    alpogeNativeSqrtQ_galois_apply e q d hq2 hd2 hqd σ

theorem nativeDyadicHostRaw_art_ch
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ u : (ZMod H.condN)ˣ,
      (((H.art u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d := by
  change ∀ u : (ZMod (alpogeNativeHostN e q d))ˣ,
    (((nativeDyadicArt e q d u).1.2 : ℤˣ) : ℤ) =
      jacobiSym (((u : ZMod (alpogeNativeHostN e q d)).val : ℕ) : ℤ) d
  intro u
  rw [nativeDyadicArt_apply, NativeQuadraticRoot.legU_val,
    ← jacobiSym.legendreSym.to_jacobiSym]
  simp only [legendreSym, Int.cast_natCast]

theorem nativeDyadicHostRaw_ps_d
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ H.d [MOD H.QS * H.q] →
      (H.art u).1.1 = -1 := by
  change ∀ u : (ZMod (alpogeNativeHostN e q d))ˣ,
    (u : ZMod (alpogeNativeHostN e q d)).val ≡ d [MOD 2 ^ (e + 2) * q] →
      (nativeDyadicArt e q d u).1.1 = -1
  intro u hu
  have hqmod := hH.2.2.1
  have hq4 : q % 4 = 3 := by omega
  have hqodd : Odd q := by rw [Nat.odd_iff]; omega
  have hjneg := hH.2.2.2.2
  rw [jacobiSym.neg _ hqodd, ZMod.χ₄_nat_three_mod_four hq4] at hjneg
  have hj : jacobiSym (d : ℤ) q = -1 := by linarith
  have huq : (u : ZMod (alpogeNativeHostN e q d)).val ≡ d [MOD q] :=
    hu.of_dvd (dvd_mul_left q (2 ^ (e + 2)))
  apply Units.ext
  change (((nativeDyadicArt e q d u).1.1 : ℤˣ) : ℤ) = (-1 : ℤ)
  calc
    _ = jacobiSym (((u : ZMod (alpogeNativeHostN e q d)).val : ℕ) : ℤ) q :=
      nativeDyadicHostRaw_psQ e q d he hH u
    _ = jacobiSym (d : ℤ) q := jacobiSym.mod_left' (by exact_mod_cast huq)
    _ = -1 := hj

end RHLean.Analysis.AlpogeThin

end
