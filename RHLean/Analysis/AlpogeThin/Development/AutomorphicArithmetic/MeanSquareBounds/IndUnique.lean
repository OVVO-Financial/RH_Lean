import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Development/AutomorphicArithmetic/MeanSquareBounds/IndUnique.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/IndUnique.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem ind_unique :
    ∀ (N N' M : ℕ) [NeZero N] [NeZero N'] (ψ : DirichletCharacter ℂ N) (ψ' : DirichletCharacter ℂ N'), M ≠ 0 →
      ψ.IsPrimitive → ψ'.IsPrimitive → (∀ n : ℕ, n.Coprime M → ψ (n : ZMod N) = ψ' (n : ZMod N')) →
      (⟨N, ψ⟩ : Σ n : ℕ, DirichletCharacter ℂ n) = ⟨N', ψ'⟩ := by
  intro N N' M _ _ ψ ψ' hM hψ hψ' h
  have hN : N ≠ 0 := NeZero.ne N
  have hN' : N' ≠ 0 := NeZero.ne N'
  have : NeZero (N * N' * M) := ⟨mul_ne_zero (mul_ne_zero hN hN') hM⟩
  have : NeZero (N * N') := ⟨mul_ne_zero hN hN'⟩
  have : NeZero (N' * N) := ⟨mul_ne_zero hN' hN⟩
  have hL1 : N ∣ N * N' * M := (Nat.dvd_mul_right N N').mul_right M
  have hL2 : N' ∣ N * N' * M := (Nat.dvd_mul_left N' N).mul_right M
  have hLM : M ∣ N * N' * M := Nat.dvd_mul_left M _
  have hA : N * N' ∣ N * N' * M := Nat.dvd_mul_right _ _
  have hB : N' * N ∣ N * N' * M := ⟨M, by ring⟩
  have key : ψ.changeLevel hL1 = ψ'.changeLevel hL2 := by
    ext a
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd]
    have hc : ((a : ZMod (N * N' * M)).val).Coprime (N * N' * M) := ZMod.val_coe_unit_coprime a
    rw [← ZMod.natCast_zmod_val (a : ZMod (N * N' * M)), ZMod.cast_natCast hL1,
      ZMod.cast_natCast hL2]
    exact h _ (Nat.Coprime.coprime_dvd_right hLM hc)
  have k1 : ψ.changeLevel (Nat.dvd_mul_right N N') = ψ'.changeLevel (Nat.dvd_mul_left N' N) := by
    apply DirichletCharacter.changeLevel_injective hA
    rw [← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]
    exact key
  have k2 : ψ'.changeLevel (Nat.dvd_mul_right N' N) = ψ.changeLevel (Nat.dvd_mul_left N N') := by
    apply DirichletCharacter.changeLevel_injective hB
    rw [← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]
    exact key.symm
  have f1 := DirichletCharacter.factorsThrough_gcd ψ ψ' k1
  have f2 := DirichletCharacter.factorsThrough_gcd ψ' ψ k2
  have e1 : ψ.conductor = N := hψ
  have e2 : ψ'.conductor = N' := hψ'
  have c1 : ψ.conductor ≤ N.gcd N' := Nat.sInf_le f1
  have c2 : ψ'.conductor ≤ N'.gcd N := Nat.sInf_le f2
  rw [e1] at c1
  rw [e2] at c2
  have g1 : N.gcd N' = N := le_antisymm (Nat.gcd_le_left _ (Nat.pos_of_ne_zero hN)) c1
  have g2 : N'.gcd N = N' := le_antisymm (Nat.gcd_le_left _ (Nat.pos_of_ne_zero hN')) c2
  have hEq : N = N' := by rw [← g1, Nat.gcd_comm, g2]
  subst hEq
  have : ψ = ψ' := DirichletCharacter.changeLevel_injective (Nat.dvd_mul_right N N) k1
  subst this
  rfl

end QH

end RHLean.Analysis.AlpogeThin
