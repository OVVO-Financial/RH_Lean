import RHLean.Geometry.NativePolarizationComplexCoordinates
import RHLean.Geometry.NativePrescribedPolarizationRealization

/-!
# The actual positive complex structure on the same prescribed lattice

The real-linear map J is transported through the proved coordinate
realization of the literal inverse-half-different lattice. In the standard
frame it is the explicit diagonal i*sgn operator. Its square is -1 and it
preserves the existing alternating integer form after real base change.
Positivity is EF(J x,x)>0: the native Hermitian form conjugates its FIRST
argument, and the actual coefficient xi has positive imaginary part on the
original CM type. No positivity or domain premise is introduced.

The original coefficient action is retained, together with both real trace
identities and their prescribed positive/negative multiplicities. The
native endpoint supplies canonical CM conjugation on the same fixed field.
It does not construct or assume the separate finite-adelic comparison, nor
identify this proved real block with a complete D7/Datum before that data
has been constructed.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Formalism/LocalToGlobal/ProjectiveLattices/DatProofs.lean,
efR_formula, thW_AW, AW_comm, trace_AW, trace_K_AW, domFor_pm;
HalfOneAddSqrtNegIsIntegral.lean, DomFor and sgnW. The source mirror states
no license; attribution is preserved without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField ComplexConjugate Matrix
open scoped BigOperators Classical TensorProduct Pointwise nonZeroDivisors

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry.NativePrescribedHermitian
open RHLean.Geometry.NativePolarizationComplexCoordinates

namespace NativeRawHostPolarization

attribute [local instance] conjugationStar

variable {φ : Frame} (H : HostRaw φ)

/-- The same actual diagonal Hermitian form at a compatible complex embedding. -/
theorem diagonalForm_embedding
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    {N : ℕ} (neg : Fin N → Bool) (τ : H.E →+* ℂ) (x y : Fin N → H.E) :
    τ (diagForm N neg x y) =
      star (fun i => τ (x i)) ⬝ᵥ (diagonalGram neg *ᵥ fun i => τ (y i)) := by
  change τ (∑ i, H.conj (x i) * sgn (neg i) * y i) = _
  simp only [map_sum, map_mul, map_sgn, hconj, dotProduct, Pi.star_apply,
    Complex.star_def, diagonalGram_apply]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- Exact real trace formula for the previously constructed integer form. -/
theorem twistedTraceForm_realFormula (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    {N : ℕ} (neg : Fin N → Bool) (x y : ℝ ⊗[ℤ] twistedLattice H B N) :
    (twistedTraceForm H B hB neg).baseChange ℝ x y =
      ∑ τ : cmTypeFinset H, 2 * ((τ : H.E →+* ℂ) (xi H) *
        (star (twistedRealCoordinates H B N x τ) ⬝ᵥ
          (diagonalGram neg *ᵥ twistedRealCoordinates H B N y τ))).re := by
  induction x using TensorProduct.inductionOn with
  | add x1 x2 h1 h2 =>
    rw [map_add, LinearMap.add_apply, h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [map_add, Pi.add_apply, star_add, add_dotProduct, mul_add, Complex.add_re]
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | add y1 y2 h1 h2 =>
      rw [map_add, h1, h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [map_add, Pi.add_apply, mulVec_add, dotProduct_add, mul_add, Complex.add_re]
    | tmul a' w =>
      rw [LinearMap.BilinForm.baseChange_tmul, twistedRealCoordinates_tmul,
        twistedRealCoordinates_tmul]
      simp only [dot_smul_real, ← diagonalForm_embedding H hconj]
      rw [zsmul_eq_mul]
      have hq : ((twistedTraceForm H B hB neg v w : ℤ) : ℝ) =
          ∑ τ ∈ cmTypeFinset H,
            2 * (τ (xi H * diagForm N neg (v : Fin N → H.E) w)).re := by
        rw [← trace_eq_sum_psi (cmTypeFinset H) (cmTypeFinset_conjugate H)]
        have h := congrArg (fun q : ℚ => (q : ℝ))
          (twistedTraceForm_cast H B hB neg v w)
        simpa only [Rat.cast_intCast] using h
      rw [hq, ← Finset.sum_coe_sort (cmTypeFinset H), Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul]
      have he : (τ : H.E →+* ℂ) (xi H) *
          (((a * a' : ℝ) : ℂ) * (τ : H.E →+* ℂ)
            (diagForm N neg (v : Fin N → H.E) w)) =
          (((a * a' : ℝ) : ℂ) * ((τ : H.E →+* ℂ) (xi H) *
            (τ : H.E →+* ℂ) (diagForm N neg (v : Fin N → H.E) w))) := by ring
      rw [he, Complex.re_ofReal_mul]
      ring

/-- Explicit diagonal J transported through the proved SAME-lattice realization. -/
def twistedComplexStructure (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) :
    (ℝ ⊗[ℤ] twistedLattice H B N) →ₗ[ℝ] (ℝ ⊗[ℤ] twistedLattice H B N) :=
  (twistedRealEquiv H B hB N).symm.toLinearMap ∘ₗ
    blk (fun _ : cmTypeFinset H => diagonalJ neg) ∘ₗ
      (twistedRealEquiv H B hB N).toLinearMap

theorem twistedRealCoordinates_complexStructure (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) (x : ℝ ⊗[ℤ] twistedLattice H B N) :
    twistedRealCoordinates H B N (twistedComplexStructure H B hB neg x) =
      blk (fun _ : cmTypeFinset H => diagonalJ neg) (twistedRealCoordinates H B N x) := by
  change (twistedRealEquiv H B hB N)
      ((twistedRealEquiv H B hB N).symm
        (blk (fun _ : cmTypeFinset H => diagonalJ neg) (twistedRealEquiv H B hB N x))) = _
  exact (twistedRealEquiv H B hB N).apply_symm_apply _

theorem twistedComplexStructure_sq (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) (x : ℝ ⊗[ℤ] twistedLattice H B N) :
    twistedComplexStructure H B hB neg (twistedComplexStructure H B hB neg x) = -x := by
  apply (twistedRealEquiv H B hB N).injective
  change twistedRealCoordinates H B N
      (twistedComplexStructure H B hB neg (twistedComplexStructure H B hB neg x)) =
    twistedRealCoordinates H B N (-x)
  rw [twistedRealCoordinates_complexStructure, twistedRealCoordinates_complexStructure, map_neg]
  funext τ
  exact diagonalJ_sq neg (twistedRealCoordinates H B N x τ)

theorem twistedComplexStructure_isometry (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    {N : ℕ} (neg : Fin N → Bool) (x y : ℝ ⊗[ℤ] twistedLattice H B N) :
    (twistedTraceForm H B hB neg).baseChange ℝ
        (twistedComplexStructure H B hB neg x) (twistedComplexStructure H B hB neg y) =
      (twistedTraceForm H B hB neg).baseChange ℝ x y := by
  rw [twistedTraceForm_realFormula H B hB hconj, twistedTraceForm_realFormula H B hB hconj]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [twistedRealCoordinates_complexStructure, twistedRealCoordinates_complexStructure,
    blk_apply, blk_apply, diagonalJ_isometry]

/-- Source positivity with its original conjugate-first orientation. -/
theorem twistedComplexStructure_pos (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    {N : ℕ} (neg : Fin N → Bool) (x : ℝ ⊗[ℤ] twistedLattice H B N) (hx : x ≠ 0) :
    0 < (twistedTraceForm H B hB neg).baseChange ℝ
      (twistedComplexStructure H B hB neg x) x := by
  rw [twistedTraceForm_realFormula H B hB hconj, twistedRealCoordinates_complexStructure]
  have hu : twistedRealCoordinates H B N x ≠ 0 := by
    intro h0
    apply hx
    apply (twistedRealEquiv H B hB N).injective
    change twistedRealCoordinates H B N x = twistedRealCoordinates H B N 0
    rw [h0, map_zero]
  obtain ⟨τ0, hτ0⟩ := Function.ne_iff.1 hu
  have hpos := fun τ : cmTypeFinset H =>
    diagonalJ_term_pos neg ((τ : H.E →+* ℂ) (xi H))
      (xi_im_pos H τ ((mem_cmTypeFinset H τ).mp τ.2))
      (twistedRealCoordinates H B N x τ)
  exact Finset.sum_pos' (fun τ _ => (hpos τ).1)
    ⟨τ0, Finset.mem_univ _, (hpos τ0).2 hτ0⟩

/-- The actual coefficient action in the same complex coordinates. -/
def twistedCoordinateMultiplication (N : ℕ) (a : 𝓞 H.E) :
    (cmTypeFinset H → Fin N → ℂ) →ₗ[ℝ] (cmTypeFinset H → Fin N → ℂ) :=
  blk fun τ : cmTypeFinset H => ((τ : H.E →+* ℂ) (a : H.E)) •
    (1 : Matrix (Fin N) (Fin N) ℂ)

theorem twistedRealCoordinates_mul (B : Ideal (𝓞 H.E)) (N : ℕ) (a : 𝓞 H.E)
    (A : (ℝ ⊗[ℤ] twistedLattice H B N) →ₗ[ℝ] (ℝ ⊗[ℤ] twistedLattice H B N))
    (hA : ∀ x : twistedLattice H B N, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x))
    (z : ℝ ⊗[ℤ] twistedLattice H B N) :
    twistedRealCoordinates H B N (A z) =
      twistedCoordinateMultiplication H N a (twistedRealCoordinates H B N z) := by
  have h1 : ∀ x : twistedLattice H B N,
      twistedRealCoordinates H B N ((1 : ℝ) ⊗ₜ (a • x)) =
        twistedCoordinateMultiplication H N a
          (twistedRealCoordinates H B N ((1 : ℝ) ⊗ₜ x)) := by
    intro x
    funext τ i
    rw [twistedCoordinateMultiplication, blk_apply, twistedRealCoordinates_tmul,
      twistedRealCoordinates_tmul, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_one, one_mul]
    change (τ : H.E →+* ℂ) ((a : H.E) * x.1 i) =
      (τ : H.E →+* ℂ) (a : H.E) * (τ : H.E →+* ℂ) (x.1 i)
    exact map_mul _ _ _
  induction z using TensorProduct.inductionOn with
  | add z1 z2 h1' h2' =>
    rw [map_add, map_add, h1', h2', map_add (twistedRealCoordinates H B N),
      map_add (twistedCoordinateMultiplication H N a)]
  | tmul x m =>
    have e : x ⊗ₜ[ℤ] m = x • ((1 : ℝ) ⊗ₜ[ℤ] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, LinearMap.map_smul, hA, LinearMap.map_smul, h1,
      LinearMap.map_smul, LinearMap.map_smul]

theorem twistedCoordinateMultiplication_comm {N : ℕ} (neg : Fin N → Bool) (a : 𝓞 H.E) :
    blk (fun _ : cmTypeFinset H => diagonalJ neg) ∘ₗ twistedCoordinateMultiplication H N a =
      twistedCoordinateMultiplication H N a ∘ₗ blk (fun _ : cmTypeFinset H => diagonalJ neg) := by
  rw [twistedCoordinateMultiplication, blk_comp, blk_comp]
  congr 1
  funext τ
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem twistedCoordinateMultiplication_trace (N : ℕ) (a : 𝓞 H.E) :
    LinearMap.trace ℝ _ (twistedCoordinateMultiplication H N a) =
      ∑ τ : cmTypeFinset H, 2 * (((τ : H.E →+* ℂ) (a : H.E)) * (N : ℂ)).re := by
  rw [twistedCoordinateMultiplication, trace_blk]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]

theorem twistedCoordinateMultiplication_J_trace {N : ℕ} (neg : Fin N → Bool) (a : 𝓞 H.E) :
    LinearMap.trace ℝ _
        (blk (fun _ : cmTypeFinset H => diagonalJ neg) ∘ₗ twistedCoordinateMultiplication H N a) =
      ∑ τ : cmTypeFinset H,
        2 * (((τ : H.E →+* ℂ) (a : H.E)) * (diagonalJ neg).trace).re := by
  rw [twistedCoordinateMultiplication, blk_comp, trace_blk]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

/-- The explicit complex structure for the original full-rank W_j. -/
def prescribedComplexStructure (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (k m j : ℕ) :
    (ℝ ⊗[ℤ] prescribedLattice H B k m) →ₗ[ℝ] (ℝ ⊗[ℤ] prescribedLattice H B k m) :=
  twistedComplexStructure H B hB (negTail (k + m - 1) (m - j))

/-- The complete source DomFor conclusion on the actual native lattice and
its existing trace form, with the positive sign chosen constructively. -/
theorem prescribedComplexStructure_properties (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    let J := prescribedComplexStructure H B hB k m j
    let EF := prescribedTraceForm H B hB k m j
    (∀ x, J (J x) = -x) ∧
      (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
      (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
      ∀ (a : 𝓞 H.E)
        (A : (ℝ ⊗[ℤ] prescribedLattice H B k m) →ₗ[ℝ]
          (ℝ ⊗[ℤ] prescribedLattice H B k m)) (t : ℂ),
        (∀ x : prescribedLattice H B k m, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
        t = ∑ τ ∈ cmTypeFinset H,
          (((k + j - 1 : ℕ) : ℂ) * τ (a : H.E) +
            ((m - j : ℕ) : ℂ) * conj (τ (a : H.E))) →
        J ∘ₗ A = A ∘ₗ J ∧
          LinearMap.trace ℝ _ A = 2 * t.re ∧
          LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im := by
  dsimp only
  refine ⟨twistedComplexStructure_sq H B hB _,
    twistedComplexStructure_isometry H B hB hconj _,
    twistedComplexStructure_pos H B hB hconj _, ?_⟩
  intro a A t hA ht
  let N := k + m - 1
  let neg := negTail N (m - j)
  let θ := twistedRealEquiv H B hB N
  let J := twistedComplexStructure H B hB neg
  have hA' : ∀ z, θ (A z) = twistedCoordinateMultiplication H N a (θ z) :=
    twistedRealCoordinates_mul H B N a A hA
  have hJ' : ∀ z, θ (J z) = blk (fun _ : cmTypeFinset H => diagonalJ neg) (θ z) :=
    twistedRealCoordinates_complexStructure H B hB neg
  have hconjA : θ.conj A = twistedCoordinateMultiplication H N a := by
    apply LinearMap.ext
    intro u
    rw [LinearEquiv.conj_apply_apply, hA', LinearEquiv.apply_symm_apply]
  have hconjJA : θ.conj (J ∘ₗ A) =
      blk (fun _ : cmTypeFinset H => diagonalJ neg) ∘ₗ twistedCoordinateMultiplication H N a := by
    apply LinearMap.ext
    intro u
    rw [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, hJ', hA',
      LinearEquiv.apply_symm_apply, LinearMap.comp_apply]
  have htrA : LinearMap.trace ℝ _ A =
      LinearMap.trace ℝ _ (twistedCoordinateMultiplication H N a) := by
    rw [← hconjA, LinearMap.trace_conj']
  have htrJA : LinearMap.trace ℝ _ (J ∘ₗ A) = LinearMap.trace ℝ _
      (blk (fun _ : cmTypeFinset H => diagonalJ neg) ∘ₗ twistedCoordinateMultiplication H N a) := by
    rw [← hconjJA, LinearMap.trace_conj']
  have hN : N = (k + j - 1) + (m - j) := by dsimp only [N]; omega
  have hq : m - j ≤ N := by dsimp only [N]; omega
  have hp : N - (m - j) = k + j - 1 := by dsimp only [N]; omega
  have ht' : t = ∑ τ : cmTypeFinset H,
      (((k + j - 1 : ℕ) : ℂ) * (τ : H.E →+* ℂ) (a : H.E) +
        ((m - j : ℕ) : ℂ) * conj ((τ : H.E →+* ℂ) (a : H.E))) := by
    rw [Finset.sum_coe_sort]
    exact ht
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro z
    apply θ.injective
    change θ (J (A z)) = θ (A (J z))
    rw [hJ', hA', hA', hJ']
    exact LinearMap.congr_fun (twistedCoordinateMultiplication_comm H neg a) (θ z)
  · rw [htrA, twistedCoordinateMultiplication_trace, ht', Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hN]
    simp only [Nat.cast_add, Complex.add_re, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im, Complex.conj_re, Complex.conj_im]
    ring
  · change LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im
    rw [htrJA, twistedCoordinateMultiplication_J_trace, ht', Complex.im_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [diagonalJ_tail_trace N (m - j) hq, hp]
    simp only [Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im]
    ring

end NativeRawHostPolarization

open NativeRawHostPolarization

/-- The field compatibility used above is supplied by the actual native CM
involution, on the same fixed field and the same embeddings. -/
theorem nativeDyadicHostRaw_prescribed_embedding_conj
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x) := by
  let H := nativeDyadicHostRaw e q d he hH
  let _ : IsCMField H.E := nativeDyadicHostRaw_cm e q d he hH
  intro τ x
  have hc : H.conj x = IsCMField.complexConj H.E x :=
    nativeDyadicHostRaw_prescribed_conj e q d he hH x
  rw [hc]
  exact IsCMField.complexEmbedding_complexConj H.E τ x

/-- One constructed half-different supports every prescribed W_j, with the
explicit positive complex structure and all of the source DomFor identities.
No complex structure, positivity, trace or finite-adelic premise is assumed. -/
theorem nativeDyadicHostRaw_exists_prescribedDomain
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ k m : ℕ, m + 3 ≤ k → ∀ j : ℕ, 1 ≤ j → j ≤ m →
        let J := prescribedComplexStructure H B hB k m j
        let EF := prescribedTraceForm H B hB k m j
        (∀ x, J (J x) = -x) ∧
          (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
          (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
          ∀ (a : 𝓞 H.E)
            (A : (ℝ ⊗[ℤ] prescribedLattice H B k m) →ₗ[ℝ]
              (ℝ ⊗[ℤ] prescribedLattice H B k m)) (t : ℂ),
            (∀ x : prescribedLattice H B k m, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
            t = ∑ τ ∈ cmTypeFinset H,
              (((k + j - 1 : ℕ) : ℂ) * τ (a : H.E) +
                ((m - j : ℕ) : ℂ) * conj (τ (a : H.E))) →
            J ∘ₗ A = A ∘ₗ J ∧
              LinearMap.trace ℝ _ A = 2 * t.re ∧
              LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im := by
  let H := nativeDyadicHostRaw e q d he hH
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_⟩
  intro k m hk j _ hj
  exact prescribedComplexStructure_properties H B hB
    (nativeDyadicHostRaw_prescribed_embedding_conj e q d he hH) k m j hk hj

end RHLean.Analysis.AlpogeThin

end
