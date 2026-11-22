import RHLean.Analysis.AlpogeNativeQuadraticRoot

/-!
# The second quadratic sign has an actual root in the same native field

The q-Gauss sum is built in the unchanged cyclotomic field with conductor
`2^(e+2)*q*d`. Its second native sign character shows that the same reciprocity
kernel fixes it. This supplies the original `HostDer.ps_root` witness without
swapping q and d into a differently presented fixed field.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/CycAll.lean`, `Der.ps_root`; the explicit Gauss-sum
supplier is the already reconstructed `CharData.exists_root` in `OfChar.lean`
and `Cond.gs_sq` in `Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/`
`EqZeroOfNegEq.lean`. Attribution is retained; the archive/mirror states no license.
-/

set_option autoImplicit false

noncomputable section

open NumberField IntermediateField

namespace RHLean.Analysis

/-- The q-Gauss sum transforms by the SECOND native quadratic sign. -/
theorem alpogeNativeCyclotomicQuadraticRoot_q_apply
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (τ : AlpogeNativeCyclotomic e q d ≃ₐ[ℚ] AlpogeNativeCyclotomic e q d) :
    τ (alpogeNativeCyclotomicQuadraticRoot e q d q (alpogeNativeQ_dvd_hostN e q d)) =
      ((if (alpogeNativeCyclotomicRecMap e q d τ).toAdd.1.2 = 0
        then (1 : ℤ) else -1) : AlpogeNativeCyclotomic e q d) *
        alpogeNativeCyclotomicQuadraticRoot e q d q (alpogeNativeQ_dvd_hostN e q d) := by
  rw [alpogeNativeCyclotomicQuadraticRoot_apply]
  exact congrArg (fun a : ℤ => (a : AlpogeNativeCyclotomic e q d) *
    alpogeNativeCyclotomicQuadraticRoot e q d q (alpogeNativeQ_dvd_hostN e q d))
    (NativeQuadraticRoot.sign2_decode
      (alpogeNativeLegU (alpogeNativeHostN e q d) q (alpogeNativeQ_dvd_hostN e q d)
        (alpogeNativeCyclotomicGalEquiv e q d τ)))

/-- The existing kernel fixes the second Gauss sum as well as the first. -/
theorem alpogeNativeCyclotomicQuadraticRoot_q_mem
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    alpogeNativeCyclotomicQuadraticRoot e q d q (alpogeNativeQ_dvd_hostN e q d) ∈
      alpogeNativeHostField e q d := by
  rw [alpogeNativeHostField, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  rw [alpogeNativeCyclotomicQuadraticRoot_q_apply, MonoidHom.mem_ker.mp hτ]
  simp

def alpogeNativeSqrtQ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] :
    alpogeNativeHostField e q d :=
  ⟨alpogeNativeCyclotomicQuadraticRoot e q d q (alpogeNativeQ_dvd_hostN e q d),
    alpogeNativeCyclotomicQuadraticRoot_q_mem e q d⟩

theorem alpogeNativeSqrtQ_sq
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hq4 : q % 4 = 3) :
    alpogeNativeSqrtQ e q d ^ 2 = -(q : alpogeNativeHostField e q d) := by
  apply Subtype.ext
  exact alpogeNativeCyclotomicQuadraticRoot_sq e q d q
    (alpogeNativeQ_dvd_hostN e q d) hq4

theorem alpogeNativeSqrtQ_ne_zero
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (hq4 : q % 4 = 3) :
    alpogeNativeSqrtQ e q d ≠ 0 := by
  intro h
  have hq0 : (q : alpogeNativeHostField e q d) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  apply neg_ne_zero.mpr hq0
  calc
    -(q : alpogeNativeHostField e q d) = alpogeNativeSqrtQ e q d ^ 2 :=
      (alpogeNativeSqrtQ_sq e q d hq4).symm
    _ = 0 := by rw [h, zero_pow two_ne_zero]

/-- The same fixed-field Galois action is the second native sign bit. -/
theorem alpogeNativeSqrtQ_galois_apply
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (σ : alpogeNativeHostField e q d ≃ₐ[ℚ] alpogeNativeHostField e q d) :
    σ (alpogeNativeSqrtQ e q d) =
      ((if (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ).toAdd.1.2 = 0
        then (1 : ℤ) else -1) : alpogeNativeHostField e q d) *
        alpogeNativeSqrtQ e q d := by
  obtain ⟨τ, hτ⟩ := alpogeNativeCyclotomicRecMap_surjective e q d hq2 hd2 hqd
    (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ)
  apply Subtype.ext
  have hrestrict := alpogeNativeHostGalEquiv_symm_apply e q d hq2 hd2 hqd τ
    (alpogeNativeSqrtQ e q d)
  change (((alpogeNativeHostGalEquiv e q d hq2 hd2 hqd).symm
      (alpogeNativeCyclotomicRecMap e q d τ) (alpogeNativeSqrtQ e q d) :
        alpogeNativeHostField e q d) : AlpogeNativeCyclotomic e q d) =
      τ (alpogeNativeSqrtQ e q d) at hrestrict
  rw [hτ, MulEquiv.symm_apply_apply] at hrestrict
  rw [hrestrict]
  change τ (alpogeNativeCyclotomicQuadraticRoot e q d q
      (alpogeNativeQ_dvd_hostN e q d)) =
    ((if (alpogeNativeHostGalEquiv e q d hq2 hd2 hqd σ).toAdd.1.2 = 0
      then (1 : ℤ) else -1) : AlpogeNativeCyclotomic e q d) *
      alpogeNativeCyclotomicQuadraticRoot e q d q (alpogeNativeQ_dvd_hostN e q d)
  rw [alpogeNativeCyclotomicQuadraticRoot_q_apply, hτ]

end RHLean.Analysis

end
