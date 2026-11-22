import Mathlib
import RHLean.Analysis.AlpogeThin.Formalism.TameInertiaTowers.StatementGroup

/-!
# Reconstructed same-host thin-source dependency

Mathematical source: Levent Alpöge (with Claude).
Source: src/Formalism/TameInertiaTowers/StatementField.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/TameInertiaTowers/StatementField.lean

This local proof reconstruction adapts the module/namespace boundary to native
RH_Lean. No upstream compiled artifact or terminal RH theorem is imported.
The source archive/mirror states no license; this notice preserves attribution
without assigning a new license to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace RHLean.Analysis.AlpogeThin

open NumberField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.TwoAdicCyclotomicDecomposition

def IsLayer (n q d : ℕ) {L : Type*} [Field L] [Algebra ℚ L] (ζ a b : L) : Prop :=
  IsPrimitiveRoot ζ (2 ^ n) ∧ a ^ 2 = -(q : L) ∧ b ^ 2 = -(d : L) ∧
    IntermediateField.adjoin ℚ {ζ, a, b} = ⊤

open Classical in

def sgn {L : Type*} [Field L] [Algebra ℚ L] (σ : Gal(L/ℚ)) (x : L) : ℤˣ :=
  if σ x = x then 1 else -1

def galMap {n : ℕ} {L : Type*} [Field L] [Algebra ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ n))
    (a b : L) (σ : Gal(L/ℚ)) : GalL n :=
  (hζ.autToPow ℚ σ, sgn σ a, sgn σ b)

def HypOdd (q d : ℕ) : Prop := q.Prime ∧ d.Prime ∧ q ≠ d ∧ q ≠ 2 ∧ d ≠ 2

def HypQD (q d : ℕ) : Prop := q.Prime ∧ d.Prime ∧ q % 8 = 3 ∧ d % 8 = 7

theorem HypQD.toHypOdd {q d : ℕ} (h : HypQD q d) : HypOdd q d := by
  obtain ⟨hq, hd, h3, h7⟩ := h
  refine ⟨hq, hd, ?_, ?_, ?_⟩ <;> omega

def LayerExists : Prop :=
  ∀ n q d : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ζ a b : L), IsLayer n q d ζ a b

def LayerGalois : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b),
    IsGalois ℚ L ∧ Module.finrank ℚ L = 2 ^ (n + 1) ∧
    (∀ σ τ : Gal(L/ℚ), galMap h.1 a b (σ * τ) = galMap h.1 a b σ * galMap h.1 a b τ) ∧
    Function.Bijective (galMap h.1 a b)

def LayerConj : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b)
    (φ : L →+* ℂ) (σ : Gal(L/ℚ)),
    (∀ x : L, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galMap h.1 a b σ = JJ n

def LayerReal : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b),
    IsCMField L ∧
    (∀ x : L, x ∈ maximalRealSubfield L ↔
      ∀ σ : Gal(L/ℚ), galMap h.1 a b σ = JJ n → σ x = x) ∧
    Module.finrank ℚ (maximalRealSubfield L) = 2 ^ n

def LayerDecompTwo : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypQD q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] (σ : Gal(L/ℚ)),
    σ ∈ MulAction.stabilizer Gal(L/ℚ) P ↔ galMap h.1 a b σ ∈ D2 n

def LayerInertiaTwo : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypQD q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] (σ : Gal(L/ℚ)),
    (∀ x : 𝓞 L, σ • x - x ∈ P) ↔ galMap h.1 a b σ ∈ I2 n

def LayerInertiaTame : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b),
    (∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(q : ℤ)})] (σ : Gal(L/ℚ)),
      (∀ x : 𝓞 L, σ • x - x ∈ P) ↔ galMap h.1 a b σ ∈ Iq n) ∧
    (∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(d : ℤ)})] (σ : Gal(L/ℚ)),
      (∀ x : 𝓞 L, σ • x - x ∈ P) ↔ galMap h.1 a b σ ∈ Id n)

def LayerFrob : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b)
    (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
    ∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∃ σ : Gal(L/ℚ), IsArithFrobAt ℤ σ P) ∧
      ∀ σ : Gal(L/ℚ), IsArithFrobAt ℤ σ P ↔
        (((galMap h.1 a b σ).1 : ZMod (2 ^ n)) = (p : ZMod (2 ^ n)) ∧
          (((galMap h.1 a b σ).2.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
          (((galMap h.1 a b σ).2.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p)

def LayerEFGTwo : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypQD q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer n q d ζ a b →
    (span {(2 : ℤ)}).ramificationIdxIn (𝓞 L) = 2 ^ (n - 1) ∧
    (span {(2 : ℤ)}).inertiaDegIn (𝓞 L) = 2 ∧
    (primesOver (span {(2 : ℤ)}) (𝓞 L)).ncard = 2 ∧
    (primesOver (span {(2 : ℤ)}) (𝓞 (maximalRealSubfield L))).ncard = 1 ∧
    (span {(2 : ℤ)}).ramificationIdxIn (𝓞 (maximalRealSubfield L)) = 2 ^ (n - 1) ∧
    (span {(2 : ℤ)}).inertiaDegIn (𝓞 (maximalRealSubfield L)) = 2

end Formalism.TwoAdicCyclotomicDecomposition

end

end RHLean.Analysis.AlpogeThin
