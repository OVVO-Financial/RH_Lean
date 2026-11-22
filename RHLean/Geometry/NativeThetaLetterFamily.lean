import RHLean.Geometry.NativeThetaFiniteFamily
import RHLean.Geometry.NativeThetaLetterDictionary

/-!
# The constructed integral family in the existing native harmonic space

This endpoint constructs the same bounded integer grid and writes its output
in the existing native theta letters. Every polynomial belongs to native HHa;
renaming back retains the literal original lattice symmetric algebra. The
degree, finite-grid span, cardinality and coefficient norm travel with the
same witness, with no further scale factor.

The full harmonic-space generation theorem and construction of the initial
short lattice vectors remain separate dependencies. Neither is supplied as
an assumption claiming the desired family or target span.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`ExistsShortHarmonicFamilyUnimodular.lean`, the inverse-renaming, coefficient
norm and finite-span transport in `exists_short_harmL_family`.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MvPolynomial NumberField

namespace RHLean.Geometry.NativeTheta.Paired

/-- Construct native HHa polynomials from the same actual integral lattice
vectors. The displayed span is exactly the constructed parameter image. -/
theorem exists_finite_integral_HHa_family
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    {I ι : Type} [Fintype I] [Nonempty I] [Fintype ι]
    {σ : ι → ι} {Ψ : ι → Prop} {dim : ι → ℕ} [Fintype {t // Ψ t}]
    {n p q : ℕ} (hσ : Function.Involutive σ) (hΨ : ∀ t, ¬ Ψ t ↔ Ψ (σ t))
    (hp : ∀ t, Ψ t → dim t = p) (hq : ∀ t, Ψ t → dim (σ t) = q)
    (Λ : Submodule (𝓞 E) (Fin n → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y))
    (v : I → Fin n → E) (hvΛ : ∀ i, v i ∈ Λ)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hvlen : ∀ i (ν : E →+* ℂ), ∑ k, ‖ν (v i k)‖ ^ 2 ≤ ρ ^ 2)
    (a : ι → ℕ → ℕ) (ha : ∀ t, Antitone fun i : Fin (dim t) => a t i)
    (hD : 1 ≤ ∑ t, ∑ i : Fin (dim t), a t i)
    (K : Type) [Field K] [NumberField K] (τ : {t // Ψ t} → E →+* K) :
    let c := fun t : {t // Ψ t} => diffOf fun i : Fin p => a t.1 i
    let c' := fun t : {t // Ψ t} => diffOf fun i : Fin q => a (σ t.1) i
    let D := ∑ t, ∑ i : Fin (dim t), a t i
    let dg := (2 * (p + q) + 1) * D
    let R := (Fintype.card I : ℝ) * dg * ρ
    let B := (((p + q : ℕ) : ℝ) * Real.sqrt n *
      (((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1))) ^ D
    let e := typeLetterEquiv hσ hΨ hp hq n
    ∃ S : Finset (MvPolynomial (RHLean.Geometry.NativeTheta.Letter ι dim n) K),
      (∀ P ∈ S, P ∈ RHLean.Geometry.NativeTheta.HHa dim n K σ Ψ a ∧
        rename e P ∈ latticePolynomials (p := p) (q := q) τ Λ ∧
        P.IsHomogeneous D ∧
        (∀ ν : K →+* ℂ, ∑ m ∈ P.support, ‖ν (P.coeff m)‖ ≤ B) ∧
        CoeffNorm.allEmbeddingNorm P ≤ Real.sqrt (Module.finrank ℚ K) * B) ∧
      Submodule.span K (S : Set _) =
        Submodule.map (rename (R := K) e.symm).toLinearMap
          (Submodule.span K (Set.range (coordProd c c'
            (fun t i k => τ t (IsCMField.complexConj E (v i k)))
            (fun t i k => τ t (v i k))))) ∧
      S.card ≤ (dg + 1) ^ (Fintype.card I * (2 * p + q)) := by
  classical
  let c := fun t : {t // Ψ t} => diffOf fun i : Fin p => a t.1 i
  let c' := fun t : {t // Ψ t} => diffOf fun i : Fin q => a (σ t.1) i
  let D := ∑ t, ∑ i : Fin (dim t), a t i
  let e := typeLetterEquiv hσ hΨ hp hq n
  have hdeg : typeDegree c c' = D := typeDegree_diffOf_eq hσ hΨ hp hq a ha
  have hpos : 1 ≤ typeDegree c c' := by rw [hdeg]; exact hD
  obtain ⟨S, hS, hspan, hcard⟩ :=
    exists_finite_integral_harmonic_family Λ hint v hvΛ hρ hvlen c c' hpos K τ
  rw [hdeg] at hS hcard
  have hre (P : Poly K {t // Ψ t} p q (Fin n)) :
      rename e (rename e.symm P) = P := by
    rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
  refine ⟨S.image (rename e.symm), ?_, ?_, Finset.card_image_le.trans hcard⟩
  · intro Q hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨hrow, hlat, hhom, hemb, hnorm⟩ := hS P hP
    refine ⟨?_, ?_, hhom.rename_isHomogeneous, ?_, ?_⟩
    · apply (mem_HHa_iff_rowHighest_of_antitone hσ hΨ hp hq a ha _).mpr
      change rename e (rename e.symm P) ∈ rowHighest K c c'
      rw [hre]
      exact hrow
    · rw [hre]
      exact hlat
    · intro ν
      exact (CoeffNorm.sum_coeff_rename_of_injective e.symm.injective
        (fun c => ‖ν c‖) P).trans_le (hemb ν)
    · rw [CoeffNorm.allEmbeddingNorm_rename_of_injective e.symm.injective]
      exact hnorm
  · rw [Finset.coe_image, ← Submodule.map_span (f := (rename (R := K) (⇑e.symm)).toLinearMap), hspan]

end RHLean.Geometry.NativeTheta.Paired

end
