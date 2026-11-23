import RHLean.Geometry.NativeThetaSpanningFamily
import RHLean.Geometry.NativeThetaJetEvaluation
import RHLean.Geometry.NativeThetaLatticeNormalization

/-!
# Evaluate the same constructed harmonic family by the theta jet formula

The finite integral HHa family is constructed from the original self-dual
lattice. Its explicit ShortValAt formula has the same span as evaluating
every polynomial in HHa. This uses the proved full harmonic generation and
the concrete fixed-degree jet operator; neither span nor theta linearity is
an endpoint hypothesis. The original lattice, independent coefficient field,
polynomial coefficient bound and finite-family count are preserved.
The constructor derives finite generation from the source's unimodularity
and admissible level. Its denominator index and translation-count index are
the literal indices of that same lattice and level.

The norm lemma records every coefficient, column-jet and normalizing factor.
It does not assert the geometric Petersson or theta supremum bound. A formal
germ supplied to this formula still has to be constructed from an actual
section and shown to be compatible with its chart. Existence and descent of
those section germs, and the cusp-density theorem, remain geometric tasks.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/
ShortThetaValueLinearInPolynomial.lean, ShortValueLinear.formula_linear;
ShortThetaRuleLinearInHarmonicPolynomial.lean, eq_sum_of_isShortRule; and
Proofs/DivisorProofs/PolynomialCoefficientEmbeddingNormLeOfL1Bound.lean,
CovGmin.PrismSpan.cusp_sub_span_short and harm_short. This file supplies the
finite polynomial-evaluation algebra of those consumers, not the remaining
geometric rule construction or cusp-density argument.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField

namespace RHLean.Geometry.NativeTheta.JetEvaluation

section ImageSpan

variable {T K A Q J : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
  [Field K] [CommRing A] [Algebra K A] [Fintype Q] [Fintype J]

/-- The finite evaluation lemma consumed by the constructed-family theorem
below. Its span input is the already-proved polynomial span, not a span of
theta sections or a cusp-density premise. -/
theorem span_rawShortValue_family
    (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (S : Finset (MvPolynomial (Letter T r n) K))
    (hspan : (Submodule.span K
      (S : Set (MvPolynomial (Letter T r n) K))).carrier = HHa r n K cc isX a)
    (β : K) (index N : ℕ) (w : Q → K)
    (jet : Q → J → Fin n → (Row T r →₀ ℕ) → A) :
    Submodule.span K (rawShortValue β index N w jet '' (S : Set _)) =
      Submodule.span K (rawShortValue β index N w jet '' HHa r n K cc isX a) := by
  let L := shortValueLinear β index N (∑ t, ∑ i : Fin (r t), a t i) w jet
  have hL (P : MvPolynomial (Letter T r n) K) (hP : P ∈ HHa r n K cc isX a) :
      rawShortValue β index N w jet P = L P :=
    rawShortValue_eq_linear_of_mem_HHa cc isX a β index N w jet P hP
  have hS : rawShortValue β index N w jet '' (S : Set _) = L '' (S : Set _) :=
    Set.image_congr fun P hP => hL P (by
      rw [← hspan]
      exact Submodule.subset_span hP)
  have hH : rawShortValue β index N w jet '' HHa r n K cc isX a =
      L '' HHa r n K cc isX a := Set.image_congr hL
  rw [hS, hH, ← Submodule.map_span L (S : Set _),
    ← Submodule.map_span L (HHa r n K cc isX a), ← hspan, Submodule.span_eq]

theorem span_shortValueOfFormalGerms_family [Algebra ℚ A] {d : ℕ}
    (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (S : Finset (MvPolynomial (Letter T r n) K))
    (hspan : (Submodule.span K
      (S : Set (MvPolynomial (Letter T r n) K))).carrier = HHa r n K cc isX a)
    (β : K) (index N : ℕ) (w : Q → K)
    (F : Fin d → Series A 2 d) (actW0 : Fin d → Series A 1 d)
    (h : Series A 2 d) (u : Row T r → Fin d → A)
    (germ : Q → J → Fin n → Series A 1 d) :
    Submodule.span K
        (shortValueOfFormalGerms β index N w F actW0 h u germ '' (S : Set _)) =
      Submodule.span K
        (shortValueOfFormalGerms β index N w F actW0 h u germ '' HHa r n K cc isX a) :=
  span_rawShortValue_family cc isX a S hspan β index N w _

end ImageSpan

section Norm

variable {T K Q J : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
  [Field K] [Algebra K ℂ] [Fintype Q] [Fintype J]

/-- The direct triangle bound on the literal theta expression. In particular
the normalization and every column derivative cost remain visible. -/
theorem norm_rawShortValue_le
    (β : K) (index N : ℕ) (w : Q → K)
    (jet : Q → J → Fin n → (Row T r →₀ ℕ) → ℂ)
    (P : MvPolynomial (Letter T r n) K) :
    ‖rawShortValue β index N w jet P‖ ≤
      ‖algebraMap K ℂ (shortNormalizer (Q := Q) β index N P.totalDegree)‖ *
        ∑ q, ‖algebraMap K ℂ (w q)‖ *
          ∑ j, ∑ m ∈ P.support, ‖algebraMap K ℂ (P.coeff m)‖ *
            ∏ b, ‖jet q j b (columnExponent m b)‖ := by
  classical
  rw [rawShortValue, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, norm_prod]

end Norm

end RHLean.Geometry.NativeTheta.JetEvaluation

namespace RHLean.Geometry.NativeTheta.Paired

open JetEvaluation

/-- Construct the short integral family and evaluate that same family using
the source's literal lattice indices in the formal-jet expression. Full
harmonic generation, finite generation and the rational short-vector basis
are supplied by their native constructions. -/
theorem exists_short_integral_HHa_evaluation_family
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    {ι : Type} [Fintype ι] {σ : ι → ι} {Ψ : ι → Prop} {dim : ι → ℕ}
    [Fintype {t // Ψ t}] {n p q : ℕ}
    (hσ : Function.Involutive σ) (hΨ : ∀ t, ¬ Ψ t ↔ Ψ (σ t))
    (hp : ∀ t, Ψ t → dim t = p) (hq : ∀ t, Ψ t → dim (σ t) = q)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hU : Lattice.Unimodular Λ)
    (N : ℕ) (hN0 : N ≠ 0)
    (hN : Lattice.levelLattice E n N ≤ Lattice.intersection Λ)
    (hn : 0 < n) (hpq : p + q ≤ n)
    (a : ι → ℕ → ℕ) (ha : ∀ t, Antitone fun i : Fin (dim t) => a t i)
    (hD : 1 ≤ ∑ t, ∑ i : Fin (dim t), a t i)
    (K : Type) [Field K] [NumberField K] (τ : {t // Ψ t} → E →+* K)
    (hτ : Function.Injective fun s : {t // Ψ t} × Bool => fun x : E =>
      τ s.1 (if s.2 then IsCMField.complexConj E x else x))
    (A : Type) [CommRing A] [Algebra K A] [Algebra ℚ A]
    {Q : Type} [Fintype Q] {d : ℕ}
    (β : K) (w : Q → K)
    (F : Fin d → Series A 2 d) (actW0 : Fin d → Series A 1 d)
    (h : Series A 2 d) (u : Row ι dim → Fin d → A)
    (germ : Q → Fin (Lattice.translationCount Λ N (p + q)) →
      Fin n → Series A 1 d) :
    let r := 2 * NativeHermitianLattice.halfDegree E * n
    let ρ := shortVectorRadius E n
    let D := ∑ t, ∑ i : Fin (dim t), a t i
    let dg := (2 * (p + q) + 1) * D
    let R := (r : ℝ) * dg * ρ
    let B := (((p + q : ℕ) : ℝ) * Real.sqrt n *
      (((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1))) ^ D
    let e := typeLetterEquiv hσ hΨ hp hq n
    ∃ S : Finset (MvPolynomial (RHLean.Geometry.NativeTheta.Letter ι dim n) K),
      (∀ P ∈ S, P ∈ RHLean.Geometry.NativeTheta.HHa dim n K σ Ψ a ∧
        rename e P ∈ latticePolynomials (p := p) (q := q) τ Λ ∧
        P.IsHomogeneous D ∧
        (∀ ν : K →+* ℂ, ∑ m ∈ P.support, ‖ν (P.coeff m)‖ ≤ B) ∧
        CoeffNorm.allEmbeddingNorm P ≤ Real.sqrt (Module.finrank ℚ K) * B) ∧
      (Submodule.span K
        (S : Set (MvPolynomial (RHLean.Geometry.NativeTheta.Letter ι dim n) K))).carrier =
        RHLean.Geometry.NativeTheta.HHa dim n K σ Ψ a ∧
      S.card ≤ (dg + 1) ^ (r * (2 * p + q)) ∧
      Submodule.span K
          (shortValueOfFormalGerms β (Lattice.normalizationIndex Λ N (p + q))
            N w F actW0 h u germ '' (S : Set _)) =
        Submodule.span K
          (shortValueOfFormalGerms β (Lattice.normalizationIndex Λ N (p + q))
            N w F actW0 h u germ ''
            RHLean.Geometry.NativeTheta.HHa dim n K σ Ψ a) := by
  have hfg := Lattice.fg_of_level Λ hU hN0 hN
  have hself := (Lattice.unimodular_iff Λ).mp hU
  obtain ⟨S, hS, hspan, hcard⟩ := exists_short_integral_HHa_spanning_family
    hσ hΨ hp hq Λ hfg (fun x hx => (hself x).mp hx)
      (fun x hx => (hself x).mpr hx) hn hpq a ha hD K τ hτ
  exact ⟨S, hS, hspan, hcard,
    span_shortValueOfFormalGerms_family σ Ψ a S hspan β
      (Lattice.normalizationIndex Λ N (p + q)) N w F actW0 h u germ⟩

end RHLean.Geometry.NativeTheta.Paired

end
