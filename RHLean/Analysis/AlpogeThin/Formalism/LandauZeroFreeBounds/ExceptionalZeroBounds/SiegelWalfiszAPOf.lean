import RHLean.Analysis.AlpogeThin.Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszAPOf.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelWalfiszAPOf.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Complex Finset ArithmeticFunction

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma chebyshev_progression_orthogonality (q a : ℕ) [NeZero q] (ha : Nat.Coprime a q) (x : ℝ) :
    (q.totient : ℂ) * ((psiAP q a x : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * psiChi χ x := by
  have hu : IsUnit ((a : ZMod q)) := (ZMod.isUnit_iff_coprime a q).mpr ha
  unfold psiAP psiChi
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q,
      χ ((a : ZMod q)⁻¹) * (((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) =
      ((Λ n : ℝ) : ℂ) * (if (a : ZMod q) = n then (q.totient : ℂ) else 0) := by
    intro n
    rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (n : ZMod q), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun χ _ => by ring)
  simp_rw [key]
  rw [Complex.ofReal_sum, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hiff : (n ≡ a [MOD q]) ↔ (a : ZMod q) = n := by
    rw [eq_comm, ZMod.natCast_eq_natCast_iff]
  by_cases h : n ≡ a [MOD q]
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]; ring
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]; simp

lemma principal_character_orthogonality_term (q a : ℕ) [NeZero q] (ha : Nat.Coprime a q) (x : ℝ) :
    ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * (if χ = 1 then (x : ℂ) else 0) = (x : ℂ) := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a q).mpr ha
  rw [← hu, ZMod.inv_coe_unit]
  simp [mul_ite, mul_zero, Finset.sum_ite_eq', MulChar.one_apply (Units.isUnit _)]

lemma card_dirichletCharacter_eq_totient (q : ℕ) [NeZero q] :
    ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) = (q.totient : ℝ) := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

end Formalism.ZeroFreeDirichlet

end RHLean.Analysis.AlpogeThin
