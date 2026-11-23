import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.CharacterBoxes.PairGood

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Development/AutomorphicArithmetic/CharacterBoxes/TwistForm.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/CharacterBoxes/TwistForm.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

noncomputable section

namespace UpperTheory.Top

open Formalism.HC

def KerChi (ψ : PChar) {φ : Frame} (H : HostRaw φ) : Prop :=
  ψ.N ∣ H.QS ∧ ∀ (a : ℕ) (h : a.Coprime H.condN), H.art (ZMod.unitOfCoprime a h) = 1 ↔
    (a ≡ 1 [MOD 2 ^ (φ.e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (φ.e + 2)]) ∧ ψ.val a = 1 ∧
      jacobiSym (a : ℤ) H.q = 1 ∧ jacobiSym (a : ℤ) H.d = 1

def TwistForm (ψ : PChar) {φ : Frame} (H : HostRaw φ) : Prop :=
  ∀ θ : φ.Char, Frame.TrivialOnFirstFactor θ → ∃ ξ ∈ Subgroup.zpowers ψ.χ, ∃ i j : Fin 2,
    θ φ.iod = (-1) ^ (j : ℕ) ∧
      ∀ a : ℕ, a.Coprime H.condN → H.dirAt θ a = tw (fun b => ξ (b : ZMod ψ.N)) H.q H.d i j a

structure WinDatum (ψ : PChar) (eps J c x Y : ℝ) (q d e : ℕ) : Prop where
  lo : x ^ (1 / J) ≤ Y
  up : Y ≤ x
  good : PairGood ψ.N eps Y x q d
  n_lo : x ^ (2 + 8 * eps) ≤ c * 2 ^ e
  n_up : c * 2 ^ e ≤ 2 * x ^ (2 + 8 * eps)
  bound : ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E →
    VVle E ⌊x ^ (400 : ℝ)⌋₊ (Real.sqrt (Real.exp (x ^ eps)))

end UpperTheory.Top

end

end RHLean.Analysis.AlpogeThin
