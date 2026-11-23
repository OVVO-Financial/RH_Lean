import RHLean.Geometry.NativeThetaLatticeGridBounds
import RHLean.Geometry.NativeThetaRowHighest

/-!
# An explicit finite integral harmonic family with the original grid cost

The family is the image of the literal bounded integer coefficient grid under
the determinant-adjugate perpendicular construction. Every returned polynomial
has the prescribed harmonicity, row degrees and row invariance and belongs
to the symmetric algebra of the SAME lattice. Its
coefficient norm, cardinality and finite-grid span are proved. The coefficient
number field K remains independent of the CM field E.

The span conclusion is the full polynomial parameter image constructed here.
The source's separate highest-weight theorem identifying that image with the
entire prescribed harmonic space, and the source construction of a short
spanning lattice basis, remain further dependencies. Neither is assumed as a
hypothesis asserting the target harmonic span.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`ExistsShortHarmonicFamilyFewColumnsLinear.lean`, the literal finite grid,
perpendicular membership, size and counting arguments; and
`PushLettersIntCastOfIsHomogeneous.lean`, symO/minorProd_mem_symO.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField MvPolynomial Matrix

namespace RHLean.Geometry.NativeTheta.Paired

open GridBounds CoeffNorm

theorem one_le_add_of_one_le_typeDegree {T : Type*} [Fintype T] {p q : ℕ}
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} (ha : 1 ≤ typeDegree c c') :
    1 ≤ p + q := by
  by_contra hpq
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
  simp [typeDegree, partSize] at ha

/-- Construct the source's actual finite orthogonal vector grid. The norm
input concerns the initial lattice vectors, not the resulting polynomial
family. Interpolation proves the displayed span for every coefficient field. -/
theorem exists_integral_perpendicular_grid
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    {ι : Type} [Fintype ι] [Nonempty ι] {n p q : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y))
    (v : ι → Fin n → E) (hvΛ : ∀ i, v i ∈ Λ)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hvlen : ∀ i (σ : E →+* ℂ), ∑ k, ‖σ (v i k)‖ ^ 2 ≤ ρ ^ 2)
    {T : Type} [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ha : 1 ≤ typeDegree c c') :
    let dg := (2 * (p + q) + 1) * typeDegree c c'
    let R := (Fintype.card ι : ℝ) * dg * ρ
    ∃ S : Finset ((Fin p → Fin n → E) × (Fin q → Fin n → E)),
      (∀ s ∈ S, (∀ a, s.1 a ∈ Λ) ∧ (∀ b, s.2 b ∈ Λ) ∧
        ∀ a b, hermPairing E n (s.2 b) (s.1 a) = 0) ∧
      (∀ (K : Type) [Field K] [CharZero K] (τ : T → E →+* K),
        Submodule.span K ((fun s : (Fin p → Fin n → E) × (Fin q → Fin n → E) =>
          minorProd c c' (fun t a k => τ t (IsCMField.complexConj E (s.1 a k)))
            fun t b k => τ t (s.2 b k)) '' (S : Set _)) =
          Submodule.span K (Set.range (coordProd c c'
            (fun t i k => τ t (v i k))
            (fun t i k => τ t (IsCMField.complexConj E (v i k)))))) ∧
      (∀ (τ : T → E →+* ℂ), ∀ s ∈ S,
        l1Norm (minorProd c c'
          (fun t a k => τ t (IsCMField.complexConj E (s.1 a k)))
          fun t b k => τ t (s.2 b k)) ≤
            (((p + q : ℕ) : ℝ) * Real.sqrt n *
              (((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1))) ^
                typeDegree c c') ∧
      S.card ≤ (dg + 1) ^ (Fintype.card ι * (2 * p + q)) := by
  classical
  let dg := (2 * (p + q) + 1) * typeDegree c c'
  let R : ℝ := (Fintype.card ι : ℝ) * dg * ρ
  have hdg1 : 1 ≤ dg := Nat.mul_pos (Nat.succ_pos _) ha
  have hR1 : 1 ≤ R := by
    have hm : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hdg : (1 : ℝ) ≤ dg := by exact_mod_cast hdg1
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hm hdg) hρ
  let h := hermPairing E n
  have hh : ∀ x y, h x y = ∑ k, x k * IsCMField.complexConj E (y k) := fun _ _ => rfl
  have hcomb : ∀ A : ι → ℕ, ∑ i, (A i : E) • v i ∈ Λ := fun A =>
    Λ.sum_mem fun i _ => by rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hvΛ i) _
  have hlen : ∀ (σ : E →+* ℂ) (A : ι → ℕ), (∀ i, A i ≤ dg) →
      ∑ k, ‖σ ((∑ i, (A i : E) • v i) k)‖ ^ 2 ≤ R ^ 2 := by
    intro σ A hA
    exact sum_sq_combination_le σ v (fun i => hvlen i σ) A hA
  let comb : (ι → ℕ) → Fin n → E := fun A => ∑ i, (A i : E) • v i
  let F : (Fin p → ι → ℕ) × (Fin p → ι → ℕ) × (Fin q → ι → ℕ) →
      (Fin p → Fin n → E) × (Fin q → Fin n → E) :=
    fun x => (fun a => comb (x.1 a),
      fun b => perpVec h (fun a => comb (x.1 a))
        (fun a => comb (x.2.1 a)) (comb (x.2.2 b)))
  let G := (Fintype.piFinset fun _ : Fin p => Fintype.piFinset fun _ : ι =>
      Finset.range (dg + 1)) ×ˢ (Fintype.piFinset fun _ : Fin p =>
      Fintype.piFinset fun _ : ι => Finset.range (dg + 1)) ×ˢ
      (Fintype.piFinset fun _ : Fin q => Fintype.piFinset fun _ : ι =>
      Finset.range (dg + 1))
  have hG : ∀ x ∈ G, (∀ a i, x.1 a i ≤ dg) ∧
      (∀ a i, x.2.1 a i ≤ dg) ∧ (∀ b i, x.2.2 b i ≤ dg) := by
    intro x hx
    simp only [G, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range] at hx
    exact ⟨fun a i => Nat.lt_succ_iff.mp (hx.1 a i),
      fun a i => Nat.lt_succ_iff.mp (hx.2.1 a i),
      fun b i => Nat.lt_succ_iff.mp (hx.2.2 b i)⟩
  refine ⟨G.image F, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hs
    refine ⟨fun a => hcomb _, fun b => perpVec_hermPairing_mem hint
      (fun a => hcomb _) (fun a => hcomb _) (hcomb _), fun a b => ?_⟩
    exact perpVec_apply_eq_zero h _ _ _ a
  · intro K _ _ τ
    rw [← span_grid_perpVec_eq_span_range_coordProd τ h hh v c c'
      (show (2 * p + 1) * typeDegree c c' ≤ dg from
        Nat.mul_le_mul_right _ (by omega))]
    congr 1
    rw [Finset.coe_image, ← Set.image_comp]
    ext P
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h1, h2, h3⟩ := hG x hx
      exact ⟨x.1, x.2.1, x.2.2, h1, h2, h3, rfl⟩
    · rintro ⟨A, A', B, h1, h2, h3, rfl⟩
      refine ⟨(A, A', B), ?_, rfl⟩
      simp only [G, Finset.coe_product, Set.mem_prod, Finset.mem_coe,
        Fintype.mem_piFinset, Finset.mem_range]
      exact ⟨fun a i => Nat.lt_succ_of_le (h1 a i),
        fun a i => Nat.lt_succ_of_le (h2 a i),
        fun b i => Nat.lt_succ_of_le (h3 b i)⟩
  · intro τ s hs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hA, hA', hB⟩ := hG x hx
    have hR0 : 0 ≤ R := by linarith
    have hRR : R ≤ ((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1) := by
      have h1 : (1 : ℝ) ≤ ((p + q + 1).factorial : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h2 : R ≤ R ^ (2 * (p + q) + 1) := by
        simpa using pow_le_pow_right₀ hR1 (Nat.le_add_left 1 (2 * (p + q)))
      calc R ≤ R ^ (2 * (p + q) + 1) := h2
        _ = 1 * R ^ (2 * (p + q) + 1) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 (pow_nonneg hR0 _)
    have hR'0 : 0 ≤ ((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1) := by linarith
    refine l1Norm_rowBlockLeadingMinorProduct_le c c' _ _ hR'0 ?_ ?_
      (Nat.le_add_right p q) (Nat.le_add_left q p)
    · intro t a
      have := hlen ((τ t).comp (IsCMField.complexConj E : E →+* E))
        (x.1 a) (hA a)
      exact this.trans (pow_le_pow_left₀ hR0 hRR 2)
    · intro t b
      have := sum_sq_perpVec_le (τ t) h hh
        (fun a => comb (x.1 a)) (fun a => comb (x.2.1 a)) (comb (x.2.2 b))
        (R := R) (fun a => hlen _ _ (hA a))
        (fun a => hlen _ _ (hA' a)) (hlen _ _ (hB b))
      refine this.trans (pow_le_pow_left₀ (mul_nonneg (by positivity) (pow_nonneg hR0 _)) ?_ 2)
      have h1 : ((p + 1).factorial : ℝ) ≤ ((p + q + 1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega)
      have h2 : R ^ (2 * p + 1) ≤ R ^ (2 * (p + q) + 1) :=
        pow_le_pow_right₀ hR1 (by omega)
      exact mul_le_mul h1 h2 (pow_nonneg hR0 _) (by positivity)
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    simp only [G, Finset.card_product, Fintype.card_piFinset, Finset.card_range,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring

/-- The original lattice symmetric algebra over the independent coefficient
field, with a literal vector of the same lattice in every generator. -/
def latticePolynomials
    {E K : Type} [Field E] [NumberField E] [IsCMField E] [Field K] [NumberField K]
    {T : Type} {p q n : ℕ} (τ : T → E →+* K)
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Subalgebra (𝓞 K) (Poly K T p q (Fin n)) :=
  Algebra.adjoin (𝓞 K)
    ({P | ∃ t a v, v ∈ Λ ∧ P = xForm t a (fun k => τ t (v k))} ∪
     {P | ∃ t b v, v ∈ Λ ∧ P = yForm t b
       (fun k => τ t (IsCMField.complexConj E (v k)))})

/-- The displayed minor product belongs to that same lattice algebra. -/
theorem minorProd_mem_latticePolynomials
    {E K : Type} [Field E] [NumberField E] [IsCMField E] [Field K] [NumberField K]
    {T : Type} [Fintype T] {p q n : ℕ} (τ : T → E →+* K)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (e : Fin p → Fin n → E) (f : Fin q → Fin n → E)
    (he : ∀ a, e a ∈ Λ) (hf : ∀ b, f b ∈ Λ) :
    minorProd c c' (fun t a k => τ t (e a k))
      (fun t b k => τ t (IsCMField.complexConj E (f b k))) ∈
        latticePolynomials (p := p) (q := q) τ Λ := by
  unfold minorProd
  refine Subalgebra.prod_mem _ fun t _ => Subalgebra.mul_mem _
    (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
  · exact det_mem_of_forall_mem _ _ fun a b =>
      Algebra.subset_adjoin (Or.inl ⟨t, _, e _, he _, rfl⟩)
  · exact det_mem_of_forall_mem _ _ fun a b =>
      Algebra.subset_adjoin (Or.inr ⟨t, _, f _, hf _, rfl⟩)

/-- The actual finite harmonic family over K. The same constructed polynomials
retain their lattice membership, homogeneous degree, coefficient norm and
finite-grid span; no free polynomial or target-span hypothesis occurs. -/
theorem exists_finite_integral_harmonic_family
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    {ι : Type} [Fintype ι] [Nonempty ι] {n p q : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y))
    (v : ι → Fin n → E) (hvΛ : ∀ i, v i ∈ Λ)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hvlen : ∀ i (σ : E →+* ℂ), ∑ k, ‖σ (v i k)‖ ^ 2 ≤ ρ ^ 2)
    {T : Type} [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ha : 1 ≤ typeDegree c c') (K : Type) [Field K] [NumberField K]
    (τ : T → E →+* K) :
    let dg := (2 * (p + q) + 1) * typeDegree c c'
    let R := (Fintype.card ι : ℝ) * dg * ρ
    let B := (((p + q : ℕ) : ℝ) * Real.sqrt n *
      (((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1))) ^ typeDegree c c'
    ∃ S : Finset (Poly K T p q (Fin n)),
      (∀ P ∈ S, P ∈ rowHighest K c c' ∧
        P ∈ latticePolynomials (p := p) (q := q) τ Λ ∧
        P.IsHomogeneous (typeDegree c c') ∧
        (∀ σ : K →+* ℂ, ∑ m ∈ P.support, ‖σ (P.coeff m)‖ ≤ B) ∧
        CoeffNorm.allEmbeddingNorm P ≤ Real.sqrt (Module.finrank ℚ K) * B) ∧
      Submodule.span K (S : Set _) =
        Submodule.span K (Set.range (coordProd c c'
          (fun t i k => τ t (IsCMField.complexConj E (v i k)))
          (fun t i k => τ t (v i k)))) ∧
      S.card ≤ (dg + 1) ^ (Fintype.card ι * (2 * p + q)) := by
  classical
  let dg := (2 * (p + q) + 1) * typeDegree c c'
  let R : ℝ := (Fintype.card ι : ℝ) * dg * ρ
  let B := (((p + q : ℕ) : ℝ) * Real.sqrt n *
    (((p + q + 1).factorial : ℝ) * R ^ (2 * (p + q) + 1))) ^ typeDegree c c'
  have hρ0 : 0 ≤ ρ := by linarith
  have hB : 0 ≤ B := by
    dsimp only [B, R]
    positivity
  obtain ⟨S, hS, hspan, hnorm, hcard⟩ :=
    exists_integral_perpendicular_grid Λ hint v hvΛ hρ hvlen c c' ha
  let Q : ((Fin p → Fin n → E) × (Fin q → Fin n → E)) → Poly K T p q (Fin n) :=
    fun s => minorProd c c' (fun t a k => τ t (s.1 a k))
      fun t b k => τ t (IsCMField.complexConj E (s.2 b k))
  let τbar : T → E →+* K := fun t =>
    (τ t).comp (IsCMField.complexConj E : E →+* E)
  have hτbar_apply (t : T) (x : E) :
      τbar t x = τ t (IsCMField.complexConj E x) := rfl
  have hτbar_conj (t : T) (x : E) :
      τbar t (IsCMField.complexConj E x) = τ t x := by
    change τ t (IsCMField.complexConj E (IsCMField.complexConj E x)) = τ t x
    rw [IsCMField.complexConj_apply_apply]
  have hQ : ∀ s, minorProd c c'
      (fun t a k => τbar t (IsCMField.complexConj E (s.1 a k)))
      (fun t b k => τbar t (s.2 b k)) = Q s := by
    intro s
    exact congrArg₂ (minorProd c c')
      (funext fun t => funext fun a => funext fun k => hτbar_conj t (s.1 a k))
      (funext fun t => funext fun b => funext fun k => hτbar_apply t (s.2 b k))
  refine ⟨S.image Q, ?_, ?_, Finset.card_image_le.trans hcard⟩
  · intro P hP
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨he, hf, hef⟩ := hS s hs
    have hperp : IsPerp (fun t a k => τ t (s.1 a k))
        (fun t b k => τ t (IsCMField.complexConj E (s.2 b k))) := by
      intro t a b
      have h := congrArg (τbar t) (hef a b)
      simp only [hermPairing_apply, map_sum, map_mul, map_zero] at h
      change (∑ k, τ t (s.1 a k) * τ t (IsCMField.complexConj E (s.2 b k))) = 0
      calc
        _ = ∑ k, τbar t (s.2 b k) *
            τbar t (IsCMField.complexConj E (s.1 a k)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hτbar_conj, hτbar_apply, mul_comm]
        _ = 0 := h
    have hemb : ∀ σ : K →+* ℂ, ∑ m ∈ (Q s).support, ‖σ ((Q s).coeff m)‖ ≤ B := by
      intro σ
      have hmap : MvPolynomial.map σ (Q s) = minorProd c c'
          (fun t a k => (σ.comp (τbar t)) (IsCMField.complexConj E (s.1 a k)))
          (fun t b k => (σ.comp (τbar t)) (s.2 b k)) := by
        dsimp only [Q]
        rw [map_minorProd]
        apply congrArg₂ (minorProd c c')
        · funext t a k
          change σ (τ t (s.1 a k)) = σ (τbar t (IsCMField.complexConj E (s.1 a k)))
          rw [hτbar_conj]
        · funext t b k
          change σ (τ t (IsCMField.complexConj E (s.2 b k))) = σ (τbar t (s.2 b k))
          rw [hτbar_apply]
      rw [← CoeffNorm.l1Norm_map, hmap]
      exact hnorm (fun t => σ.comp (τbar t)) s hs
    exact ⟨minorProd_mem_rowHighest c c' hperp,
      minorProd_mem_latticePolynomials τ Λ c c' _ _ he hf,
      minorProd_isHomogeneous c c' _ _, hemb,
      CoeffNorm.allEmbeddingNorm_le_of_l1Bound (Q s) B hB hemb⟩
  · rw [Finset.coe_image]
    have h := hspan K τbar
    have hfun : (fun s => minorProd c c'
        (fun t a k => τbar t (IsCMField.complexConj E (s.1 a k)))
        (fun t b k => τbar t (s.2 b k))) = Q := funext hQ
    rw [hfun] at h
    simpa only [hτbar_apply, IsCMField.complexConj_apply_apply] using h

end RHLean.Geometry.NativeTheta.Paired

end
