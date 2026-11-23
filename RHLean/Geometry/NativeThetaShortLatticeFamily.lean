import RHLean.Geometry.NativeHermitianShortVectors
import RHLean.Geometry.NativeThetaFiniteFamily

/-!
# The finite theta family from the original self-dual lattice

This composes the constructed short vectors with the finite integral harmonic
family on the same lattice. The vector family, its rational basis property,
all-embedding length bounds, the polynomial family and its coefficient bounds
are all conclusions. The polynomial span is identified with the constructed
parameter image; its identification with the entire highest-weight space is
a separate algebraic theorem.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`TraceHermNondegenerate.lean`, `GlobalTheory.exists_short_vectors`, composed
with the finite-grid construction in `ExistsShortHarmonicFamilyLinear.lean`.
The source archive/mirror states no license; attribution is retained
without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField

namespace RHLean.Geometry.NativeTheta.Paired

open NativeHermitianLattice

/-- The original all-embedding radius supplied by trace transference. -/
def shortVectorRadius (E : Type) [Field E] [NumberField E] (n : ℕ) : ℝ :=
  2 * (halfDegree E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rootDiscr E

theorem one_le_shortVectorRadius (E : Type) [Field E] [NumberField E] [IsCMField E]
    {n : ℕ} (hn : 0 < n) : 1 ≤ shortVectorRadius E n := by
  have hfin : Module.finrank ℚ E = 2 * halfDegree E := ShortVectors.finrank_eq
  have hf : 0 < halfDegree E := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    omega
  have hf1 : (1 : ℝ) ≤ halfDegree E := by exact_mod_cast Nat.succ_le_of_lt hf
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn
  have hdisc : (1 : ℝ) ≤ |(discr E : ℝ)| := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  have hrd : 1 ≤ rootDiscr E := by
    rw [rootDiscr_def, Int.cast_abs]
    exact Real.one_le_rpow hdisc (by positivity)
  have hpow : (1 : ℝ) ≤ (halfDegree E : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.one_le_rpow hf1 (by norm_num)
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  unfold shortVectorRadius
  calc
    (1 : ℝ) ≤ 2 * 1 * 1 * 1 := by norm_num
    _ ≤ 2 * (halfDegree E : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ 2 * rootDiscr E := by
      gcongr

/-- Construct both the short basis and the finite harmonic family on the SAME
lattice, with the original degree, discriminant, dimension and grid costs. -/
theorem exists_short_lattice_family
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n p q : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y)) → x ∈ Λ)
    (hn : 0 < n) {T : Type} [Fintype T]
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (ha : 1 ≤ typeDegree c c')
    (K : Type) [Field K] [NumberField K] (τ : T → E →+* K) :
    let r := 2 * halfDegree E * n
    let ρ := shortVectorRadius E n
    let dg := (2 * (p + q) + 1) * typeDegree c c'
    let R := (r : ℝ) * dg * ρ
    let B := (((p + q : ℕ) : ℝ) * Real.sqrt n *
      (((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1))) ^ typeDegree c c'
    ∃ (v : Fin r → Fin n → E) (S : Finset (Poly K T p q (Fin n))),
      (∀ i, v i ∈ Λ) ∧ LinearIndependent ℚ v ∧
      Submodule.span ℚ (Set.range v) = ⊤ ∧
      (∀ i (σ : E →+* ℂ), ∑ k, ‖σ (v i k)‖ ^ 2 ≤ ρ ^ 2) ∧
      (∀ P ∈ S, P ∈ rowHighest K c c' ∧
        P ∈ latticePolynomials (p := p) (q := q) τ Λ ∧
        P.IsHomogeneous (typeDegree c c') ∧
        (∀ σ : K →+* ℂ, ∑ m ∈ P.support, ‖σ (P.coeff m)‖ ≤ B) ∧
        CoeffNorm.allEmbeddingNorm P ≤ Real.sqrt (Module.finrank ℚ K) * B) ∧
      Submodule.span K (S : Set _) =
        Submodule.span K (Set.range (coordProd c c'
          (fun t i k => τ t (IsCMField.complexConj E (v i k)))
          (fun t i k => τ t (v i k)))) ∧
      S.card ≤ (dg + 1) ^ (r * (2 * p + q)) := by
  classical
  obtain ⟨v, hvΛ, hvli, hvspan, hvlen⟩ := exists_short_vectors Λ hfg hint hdual
  have hfin : Module.finrank ℚ E = 2 * halfDegree E := ShortVectors.finrank_eq
  have hf : 0 < halfDegree E := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    omega
  have : Nonempty (Fin (2 * halfDegree E * n)) :=
    ⟨⟨0, Nat.mul_pos (Nat.mul_pos (by decide) hf) hn⟩⟩
  obtain ⟨S, hS, hspan, hcard⟩ := exists_finite_integral_harmonic_family Λ hint v hvΛ
    (one_le_shortVectorRadius E hn) hvlen c c' ha K τ
  refine ⟨v, S, hvΛ, hvli, hvspan, hvlen, ?_, hspan, ?_⟩
  · simpa only [Fintype.card_fin] using hS
  · simpa only [Fintype.card_fin] using hcard

end RHLean.Geometry.NativeTheta.Paired

end
