import RHLean.Analysis.AlpogeNativeRootOfUnityInertia
import RHLean.Analysis.AlpogeThin.NativeDyadicHostDifferent

/-!
# Norm one for roots of unity in the SAME native host

The actual d-inertia group has at most two elements, so a primitive d-th
root would contradict its ideal-theoretic ramification bound. Reduction
at a prime above d then proves that the actual d-inertia involution fixes
every root of unity. Multiplying that involution by actual CM conjugation
gives a fixed-point-free pairing of relative automorphisms over the
literal quadratic subfield. Each pair contributes one to the norm.

No `HostDer`, roots-of-unity classification, norm condition, inertia bound,
or chosen pairing witness is assumed for the constructed native host.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/KcEqOfPowEqOne.lean`,
`Der.{kc_no_root_d,kc_iod_fix,kc_conj_mul_self,norm_mu}`.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open NativeRootOfUnityInertia

/-- Actual d-inertia excludes primitive d-th roots in the native field. -/
theorem nativeDyadicHostRaw_no_primitive_d
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ η : H.E, IsPrimitiveRoot η H.d → False := by
  let H := nativeDyadicHostRaw e q d he hH
  intro η hη
  have : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have : IsGalois ℚ H.E := H.galois
  obtain ⟨⟨Q, hQp, hQl⟩⟩ :
      Nonempty ((span {(H.d : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  have hge := mu_le_ram H.d Q (H.d - 1) (mu_mem_pow H.d Q η hη)
  have hle := mu_card_le_two (L := H.E) H.gal H.gal.injective
    (nativeDyadicFrame e).iod (Q.inertia (H.E ≃ₐ[ℚ] H.E))
    (fun σ hσ => (nativeDyadicHostRaw_inertia_d e q d he hH Q σ).mp
      (AddSubgroup.mem_inertia.mp hσ))
  rw [card_inertia H.d Q] at hle
  have hd := H.hyp.2.2.2.1
  omega

/-- The constructed d-inertia involution fixes every root of unity. -/
theorem nativeDyadicHostRaw_iod_fix_rootOfUnity
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (σ : H.E ≃ₐ[ℚ] H.E), H.gal σ = (nativeDyadicFrame e).iod →
      ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → σ x = x := by
  let H := nativeDyadicHostRaw e q d he hH
  intro σ hσ x hx
  obtain ⟨n, hn, hxn⟩ := hx
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hxn⟩
  have hmpos : 0 < orderOf x := orderOf_pos_iff.mpr hfin
  have hprim : IsPrimitiveRoot x (orderOf x) := IsPrimitiveRoot.orderOf x
  have hd : ¬ H.d ∣ orderOf x := by
    rintro ⟨k, hk⟩
    exact nativeDyadicHostRaw_no_primitive_d e q d he hH _
      (hprim.pow hmpos (by rw [hk, mul_comm]))
  have : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  obtain ⟨⟨P, hPp, hPl⟩⟩ :
      Nonempty ((span {(H.d : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  have hin := (nativeDyadicHostRaw_inertia_d e q d he hH P σ).mpr (Or.inr hσ)
  let X : 𝓞 H.E := ⟨x, hprim.isIntegral hmpos⟩
  have hX : X ^ orderOf x = 1 := by
    apply RingOfIntegers.ext
    exact hprim.pow_eq_one
  have hX' : (σ • X) ^ orderOf x = 1 := by rw [← smul_pow', hX, smul_one]
  have hm : ((orderOf x : ℕ) : 𝓞 H.E) ∉ P := by
    intro h0
    have h1 := (intCast_mem_iff H.d P ((orderOf x : ℕ) : ℤ)).mp
      (by exact_mod_cast h0)
    exact hd (by exact_mod_cast h1)
  have hfix := eq_of_pow_eq_one P hm hX' hX (hin X)
  exact congrArg (fun y : 𝓞 H.E => (y : H.E)) hfix

/-- Actual CM conjugation sends every root of unity to its inverse. -/
theorem nativeDyadicHostRaw_rootOfUnity_mul_conj
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → x * H.conj x = 1 := by
  let H := nativeDyadicHostRaw e q d he hH
  intro x hx
  obtain ⟨n, hn, hxn⟩ := hx
  let ψ : H.E →+* ℂ := Classical.choice inferInstance
  apply ψ.injective
  have h1 : ‖ψ x‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hxn, map_one]) hn.ne'
  rw [map_mul, (nativeDyadicHostRaw_conj_iff e q d he hH ψ H.conj).mpr
    (NativeRawHostDifferent.gal_conj H), Complex.mul_conj', h1, map_one]
  simp

/-- The original HostDer norm-mu clause, proved for the actual native host. -/
theorem nativeDyadicHostRaw_norm_mu
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm H.K x = 1 := by
  classical
  let H := nativeDyadicHostRaw e q d he hH
  intro x hx
  have : IsGalois ℚ H.E := H.galois
  have : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ _ _
  obtain ⟨ι, hι⟩ := H.gal.surjective (nativeDyadicFrame e).iod
  set s₀ := H.conj * ι with hs₀
  have hg : H.gal s₀ = (nativeDyadicFrame e).sg := by
    rw [hs₀, map_mul, NativeRawHostDifferent.gal_conj, hι]
    exact Prod.ext (show c0 * ((1, -1) : G0) = (-1, 1) by decide) (mul_one _)
  have hΨ : H.gal s₀ ∈ (nativeDyadicFrame e).Psi := by rw [hg]; rfl
  let s : H.E ≃ₐ[H.K] H.E := AlgEquiv.ofRingEquiv (f := s₀.toRingEquiv)
    (fun y => NativeRawHostDifferent.fix_K H s₀ hΨ y)
  have hs : ∀ y, s y = s₀ y := fun _ => rfl
  have hsx : x * s x = 1 := by
    rw [hs, hs₀, AlgEquiv.mul_apply,
      nativeDyadicHostRaw_iod_fix_rootOfUnity e q d he hH ι hι x hx]
    exact nativeDyadicHostRaw_rootOfUnity_mul_conj e q d he hH x hx
  have hss0 : s₀ * s₀ = 1 := by
    apply H.gal.injective
    rw [map_mul, hg, map_one]
    exact Prod.ext (show ((-1, 1) : G0) * (-1, 1) = 1 by decide) (mul_one _)
  have hss : s * s = 1 := AlgEquiv.ext fun y => DFunLike.congr_fun hss0 y
  have hs1 : s ≠ 1 := by
    intro h1
    have h2 : s₀ = 1 := AlgEquiv.ext fun y => DFunLike.congr_fun h1 y
    rw [h2, map_one] at hg
    exact absurd (congrArg (fun g : (nativeDyadicFrame e).GG => g.1) hg)
      (show ¬ (1 : G0) = (-1, 1) by decide)
  apply (algebraMap H.K H.E).injective
  rw [Algebra.norm_eq_prod_automorphisms, map_one]
  refine Finset.prod_involution (fun σ _ => σ * s) (fun σ _ => ?_)
    (fun σ _ _ => ?_) (fun _ _ => Finset.mem_univ _) (fun σ _ => ?_)
  · rw [AlgEquiv.mul_apply, ← map_mul, hsx, map_one]
  · exact fun h1 => hs1 (mul_eq_left.mp h1)
  · rw [mul_assoc, hss, mul_one]

end RHLean.Analysis.AlpogeThin

end
