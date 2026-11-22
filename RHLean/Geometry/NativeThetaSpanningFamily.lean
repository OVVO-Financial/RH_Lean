import RHLean.Geometry.NativeThetaShortLatticeFamily
import RHLean.Geometry.NativeThetaOrbitSpanClosure
import RHLean.Geometry.NativeThetaLetterDictionary

/-!
# A constructed short integral family spanning the full native harmonic space

The same integral self-dual lattice supplies the short rational basis, the
bounded integer parameter grid and its integral polynomial family. The
proved column-orbit generation theorem identifies its span with the full
harmonic row space, and the literal variable equivalence transports this
family to the existing native HHa letters.

Neither the short lattice vectors nor harmonic generation are hypotheses.
The coefficient field K remains independent of E, as required for the
original cover field. Distinctness of the positive and conjugate coefficient
embeddings is explicit; `injective_liftedCMEmbeddings` proves it from their
actual complex realizations and the disjointness of a CM type.

This constructs harmonic polynomials. Theta evaluation, its geometric
spanning argument and the good-cover constructor remain separate steps.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`ExistsShortHarmonicFamilyUnimodular.lean`,
`injective_embF_inPsi` and the dominant positive-degree branch of
`exists_short_harmL_family`, with the actual short-vector supplier from
`TraceHermNondegenerate.lean` and the proved full-span construction from
`RowHighestLeSpanColWordComplex.lean`.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MvPolynomial NumberField

namespace RHLean.Geometry.NativeTheta.Paired

/-- Actual coefficient-field lifts of distinct complex embeddings preserve
the distinct positive/conjugate embedding pairs of a CM type. -/
theorem injective_liftedCMEmbeddings
    {E K : Type} [Field E] [NumberField E] [IsCMField E] [Field K]
    (Ψ : (E →+* ℂ) → Prop)
    (hΨ : ∀ τ, ¬ (Ψ τ ∧ Ψ (ComplexEmbedding.conjugate τ)))
    (j : K →+* ℂ) (τK : (E →+* ℂ) → E →+* K)
    (hτK : ∀ τ x, j (τK τ x) = τ x) :
    Function.Injective fun s : {τ : E →+* ℂ // Ψ τ} × Bool =>
      fun x : E => τK s.1.1 (if s.2 then IsCMField.complexConj E x else x) := by
  rintro ⟨⟨τ, hτ⟩, b⟩ ⟨⟨τ', hτ'⟩, b'⟩ h
  have hx : ∀ x : E, (if b then ComplexEmbedding.conjugate τ else τ) x =
      (if b' then ComplexEmbedding.conjugate τ' else τ') x := by
    intro x
    have he := congrArg j (congrFun h x)
    simp only [hτK] at he
    cases b <;> cases b'
    · exact he
    · change τ x = Complex.conj (τ' x)
      rw [← IsCMField.complexEmbedding_complexConj]
      exact he
    · change Complex.conj (τ x) = τ' x
      rw [← IsCMField.complexEmbedding_complexConj]
      exact he
    · change Complex.conj (τ x) = Complex.conj (τ' x)
      rw [← IsCMField.complexEmbedding_complexConj,
        ← IsCMField.complexEmbedding_complexConj]
      exact he
  have hf : (if b then ComplexEmbedding.conjugate τ else τ) =
      (if b' then ComplexEmbedding.conjugate τ' else τ') := RingHom.ext hx
  cases b <;> cases b'
  · change τ = τ' at hf
    subst hf
    rfl
  · change τ = ComplexEmbedding.conjugate τ' at hf
    exact absurd ⟨hτ', by rw [← hf]; exact hτ⟩ (hΨ τ')
  · change ComplexEmbedding.conjugate τ = τ' at hf
    exact absurd ⟨hτ, by rw [hf]; exact hτ'⟩ (hΨ τ)
  · change ComplexEmbedding.conjugate τ = ComplexEmbedding.conjugate τ' at hf
    have he := (ComplexEmbedding.involutive_conjugate E).injective hf
    subst he
    rfl

/-- Construct a finite integral family spanning all of native HHa from the
original self-dual lattice, preserving the original all-embedding radius,
finite-grid count and coefficient norm in the independent cover field. -/
theorem exists_short_integral_HHa_spanning_family
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    {ι : Type} [Fintype ι] {σ : ι → ι} {Ψ : ι → Prop} {dim : ι → ℕ}
    [Fintype {t // Ψ t}] {n p q : ℕ}
    (hσ : Function.Involutive σ) (hΨ : ∀ t, ¬ Ψ t ↔ Ψ (σ t))
    (hp : ∀ t, Ψ t → dim t = p) (hq : ∀ t, Ψ t → dim (σ t) = q)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y)) → x ∈ Λ)
    (hn : 0 < n) (hpq : p + q ≤ n)
    (a : ι → ℕ → ℕ) (ha : ∀ t, Antitone fun i : Fin (dim t) => a t i)
    (hD : 1 ≤ ∑ t, ∑ i : Fin (dim t), a t i)
    (K : Type) [Field K] [NumberField K] (τ : {t // Ψ t} → E →+* K)
    (hτ : Function.Injective fun s : {t // Ψ t} × Bool => fun x : E =>
      τ s.1 (if s.2 then IsCMField.complexConj E x else x)) :
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
      (Submodule.span K (S : Set _) : Set _) =
        RHLean.Geometry.NativeTheta.HHa dim n K σ Ψ a ∧
      S.card ≤ (dg + 1) ^ (r * (2 * p + q)) := by
  classical
  let c := fun t : {t // Ψ t} => diffOf fun i : Fin p => a t.1 i
  let c' := fun t : {t // Ψ t} => diffOf fun i : Fin q => a (σ t.1) i
  let D := ∑ t, ∑ i : Fin (dim t), a t i
  let e := typeLetterEquiv hσ hΨ hp hq n
  have hdeg : typeDegree c c' = D := typeDegree_diffOf_eq hσ hΨ hp hq a ha
  have hpos : 1 ≤ typeDegree c c' := by rw [hdeg]; exact hD
  obtain ⟨v, S, _, _, hvspan, _, hS, hspan, hcard⟩ :=
    exists_short_lattice_family Λ hfg hint hdual hn c c' hpos K τ
  have hgen := span_range_coordProd_eq_rowHighest τ hτ hpq v hvspan c c'
  rw [hgen] at hspan
  rw [hdeg] at hS hcard
  have hre (P : Poly K {t // Ψ t} p q (Fin n)) :
      rename e (rename e.symm P) = P := by
    rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
  have hre' (P : MvPolynomial (RHLean.Geometry.NativeTheta.Letter ι dim n) K) :
      rename e.symm (rename e P) = P := by
    rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]
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
      rw [CoeffNorm.sum_coeff_rename_of_injective e.symm.injective]
      exact hemb ν
    · rw [CoeffNorm.allEmbeddingNorm_rename_of_injective e.symm.injective]
      exact hnorm
  · rw [Finset.coe_image, ← Submodule.map_span (f := (rename (R := K) (⇑e.symm)).toLinearMap), hspan]
    ext P
    rw [mem_HHa_iff_rowHighest_of_antitone hσ hΨ hp hq a ha]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      change rename e (rename e.symm Q) ∈ rowHighest K c c'
      rw [hre]
      exact hQ
    · intro hP
      exact ⟨rename e P, hP, hre' P⟩

end RHLean.Geometry.NativeTheta.Paired

end
