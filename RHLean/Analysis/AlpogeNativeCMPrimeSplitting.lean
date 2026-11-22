import Mathlib

/-!
# Actual prime splitting in a quadratic CM extension

The two automorphisms over the maximal real subfield are identity and
complex conjugation. The actual Galois action on prime ideals identifies
splitting with conjugation moving the chosen prime. For an unramified CM
extension, the fundamental degree identity gives the original split-or-inert
alternative. The native application supplies the unramifiedness class by
the already proved different calculation.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/NcardEqTwoIff.lean`,
`Eta.{cases,card_gal,split_or_inert,ncard_eq_two_iff}`. The split-or-inert
proof uses the actual `Algebra.Unramified` class directly; the splitting
criterion does not require an unramifiedness premise.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Ideal
open scoped Pointwise

namespace RHLean.Analysis.NativeCMPrimeSplitting

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

theorem card_gal : Nat.card (K ≃ₐ[K⁺] K) = 2 := by
  rw [IsGalois.card_aut_eq_finrank]
  exact Algebra.IsQuadraticExtension.finrank_eq_two _ _

theorem aut_cases (g : K ≃ₐ[K⁺] K) : g = 1 ∨ g = IsCMField.complexConj K := by
  classical
  by_contra hne
  push_neg at hne
  have h2 := card_gal K
  let : Fintype (K ≃ₐ[K⁺] K) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at h2
  have h3 : ({1, IsCMField.complexConj K, g} : Finset (K ≃ₐ[K⁺] K)).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, IsCMField.complexConj K, g,
      (IsCMField.complexConj_ne_one K).symm, hne.1.symm, hne.2.symm, rfl⟩
  have h4 := Finset.card_le_univ ({1, IsCMField.complexConj K, g} : Finset (K ≃ₐ[K⁺] K))
  omega

/-- The actual quadratic degree and unramifiedness force the complete
split-or-inert alternative at every nonzero prime of the real subfield. -/
theorem split_or_inert [Algebra.Unramified (𝓞 K⁺) (𝓞 K)]
    (𝔭 : Ideal (𝓞 K⁺)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    (primesOver 𝔭 (𝓞 K)).ncard = 2 ∨
      ((primesOver 𝔭 (𝓞 K)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 K) = 2) := by
  classical
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty (primesOver 𝔭 (𝓞 K)) := inferInstance
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 P
  have hp0 : P.under (𝓞 K⁺) ≠ ⊥ :=
    fun h0 => hP0 (Ideal.eq_bot_of_comap_eq_bot h0)
  have : Finite ((𝓞 K⁺) ⧸ P.under (𝓞 K⁺)) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hp0
  have he : P.ramificationIdx (𝓞 K⁺) = 1 :=
    Ideal.ramificationIdx_eq_one_iff.mpr
      ((Algebra.unramified_iff_forall.mp
        (inferInstance : Algebra.Unramified (𝓞 K⁺) (𝓞 K))) ⟨P, hPp⟩)
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    𝔭 (𝓞 K) (K ≃ₐ[K⁺] K)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭 P (K ≃ₐ[K⁺] K),
    he, one_mul, card_gal K] at h1
  rw [Ideal.inertiaDegIn_eq_inertiaDeg 𝔭 P (K ≃ₐ[K⁺] K)] at h1 ⊢
  have hfpos : 0 < P.inertiaDeg (𝓞 K⁺) := Ideal.inertiaDeg_pos P (𝓞 K⁺)
  generalize (𝔭.primesOver (𝓞 K)).ncard = n at h1 ⊢
  generalize P.inertiaDeg (𝓞 K⁺) = f at h1 hfpos ⊢
  have hn : n ≤ 2 := by nlinarith
  interval_cases n
  · omega
  · right; exact ⟨rfl, by omega⟩
  · left; rfl

/-- Splitting over the real subfield is exactly the actual conjugate prime
being distinct; no abstract decomposition matching is assumed. -/
theorem ncard_eq_two_iff (P : Ideal (𝓞 K)) [P.IsPrime] (hP0 : P ≠ ⊥) :
    (primesOver (P.under (𝓞 K⁺)) (𝓞 K)).ncard = 2 ↔
      IsCMField.complexConj K • P ≠ P := by
  classical
  have hp0 : P.under (𝓞 K⁺) ≠ ⊥ :=
    fun h0 => hP0 (Ideal.eq_bot_of_comap_eq_bot h0)
  have : Finite ((𝓞 K⁺) ⧸ P.under (𝓞 K⁺)) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hp0
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (P.under (𝓞 K⁺)) (𝓞 K) (K ≃ₐ[K⁺] K)
  have h2 := Ideal.card_stabilizer_eq (G := K ≃ₐ[K⁺] K) (P.under (𝓞 K⁺)) P
  rw [← h2, card_gal K] at h1
  have hmem : ∀ g : K ≃ₐ[K⁺] K,
      g ∈ MulAction.stabilizer (K ≃ₐ[K⁺] K) P ↔ g • P = P :=
    fun g => MulAction.mem_stabilizer_iff
  constructor
  · intro h hcP
    have hne : MulAction.stabilizer (K ≃ₐ[K⁺] K) P ≠ ⊥ := by
      intro hb
      have hc : IsCMField.complexConj K ∈ MulAction.stabilizer (K ≃ₐ[K⁺] K) P :=
        (hmem _).mpr hcP
      rw [hb, Subgroup.mem_bot] at hc
      exact IsCMField.complexConj_ne_one K hc
    have h3 : Nat.card (MulAction.stabilizer (K ≃ₐ[K⁺] K) P) ≠ 1 :=
      fun h' => hne (Subgroup.card_eq_one.mp h')
    rw [h] at h1
    omega
  · intro hcP
    have hb : MulAction.stabilizer (K ≃ₐ[K⁺] K) P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      rcases aut_cases K g with hg1 | hg1
      · exact hg1
      · exfalso
        apply hcP
        rw [← hg1]
        exact (hmem g).mp hg
    rw [hb, Subgroup.card_bot, mul_one] at h1
    exact h1

end RHLean.Analysis.NativeCMPrimeSplitting

end
