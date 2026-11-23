import RHLean.Geometry.NativePrescribedGeometricPeriod
import RHLean.Geometry.NativeCMQuadraticOrder

/-!
# Pure-block positivity on the actual inverse-half-different

The elliptic Serre constructor requires a positive quadratic-order Hermitian
form. The mixed-signature native lattice cannot satisfy that condition with
one sign. Here positivity on the actual coefficient module is proved by the
exact trace identity, before any tensor or polarized-scheme inference.

For the original half-root w and M = B^-1,
  2 EF(w x,x) = Tr(conj(x)x) = sum_sigma |sigma(x)|^2.
Thus the positive coordinate block uses EF and the negative coordinate block
uses -EF with the opposite elliptic orientation. No free coefficient basis,
new polarization scalar, or desired analytic estimate is assumed.

Source consumer: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/
ExistsCmTensorLatticeCurvePrincipalTriple.lean, exists_isTen, and
ExistsHermFormCurve.lean, exists_isExp_of_isTen. The latter explicitly
requires q=0 or p=0. The trace calculation specializes those positivity
inputs to RHLean's actual coefficient module. The source archive states no
license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField ComplexConjugate
open scoped BigOperators Pointwise

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativePrescribedHermitian

variable {φ : Frame} (H : HostRaw φ)

/-- Split the literal inverse-ideal coordinates, preserving their coefficient
module. This introduces no basis in the projective ideal. -/
def blockCoordinates (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    (p q : ℕ) : (Fin (p + q) → M) ≃ₗ[A] ((Fin p → M) × (Fin q → M)) where
  toFun x := (fun i => x (Fin.castAdd q i), fun i => x (Fin.natAdd p i))
  invFun x := Fin.addCases x.1 x.2
  left_inv x := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def twistedBlockSplit (B : Ideal (𝓞 H.E)) (p q : ℕ) :
    twistedLattice H B (p + q) ≃ₗ[𝓞 H.E]
      (twistedLattice H B p × twistedLattice H B q) :=
  (twistedCoordinates H B (p + q)).trans
    ((blockCoordinates (𝓞 H.E) (coefficientIdeal H B) p q).trans
      (LinearEquiv.prodCongr (twistedCoordinates H B p).symm
        (twistedCoordinates H B q).symm))

theorem twistedBlockSplit_left (B : Ideal (𝓞 H.E)) (p q : ℕ)
    (x : twistedLattice H B (p + q)) (i : Fin p) :
    twistedCoordinates H B p (twistedBlockSplit H B p q x).1 i =
      twistedCoordinates H B (p + q) x (Fin.castAdd q i) := by
  simp [twistedBlockSplit, blockCoordinates]

theorem twistedBlockSplit_right (B : Ideal (𝓞 H.E)) (p q : ℕ)
    (x : twistedLattice H B (p + q)) (i : Fin q) :
    twistedCoordinates H B q (twistedBlockSplit H B p q x).2 i =
      twistedCoordinates H B (p + q) x (Fin.natAdd p i) := by
  simp [twistedBlockSplit, blockCoordinates]

/-- The exact mixed form is the positive-block form minus the same
positive form on the negative block. No cross term or lattice index is lost. -/
theorem twistedBlockSplit_trace (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (p q : ℕ) (x y : twistedLattice H B (p + q)) :
    twistedTraceForm H B hB (negTail (p + q) q) x y =
      twistedTraceForm H B hB (fun _ => false)
        (twistedBlockSplit H B p q x).1 (twistedBlockSplit H B p q y).1 -
      twistedTraceForm H B hB (fun _ => false)
        (twistedBlockSplit H B p q x).2 (twistedBlockSplit H B p q y).2 := by
  simp only [twistedTraceForm_apply, twistedBlockSplit_left, twistedBlockSplit_right,
    sgn, Bool.false_eq_true, ite_false, one_mul]
  let f : Fin (p + q) → ℤ := fun i =>
    (if negTail (p + q) q i = true then -1 else 1) *
      integralTraceForm H B hB (twistedCoordinates H B (p + q) x i)
        (twistedCoordinates H B (p + q) y i)
  change (∑ i, f i) = _
  rw [← Equiv.sum_comp finSumFinEquiv f, Fintype.sum_sum_type]
  have hl (i : Fin p) : negTail (p + q) q (Fin.castAdd q i) = false := by
    apply negTail_false
    simp
  have hr (i : Fin q) : negTail (p + q) q (Fin.natAdd p i) = true := by
    apply negTail_true
    simp
  simp [f, hl, hr, sub_eq_add_neg]

theorem twice_coefficient_trace_halfRoot
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (w : 𝓞 H.E) (hw : (2 : H.E) * (w : H.E) = 1 + H.sqd)
    (x : (coefficientIdeal H B : Submodule (𝓞 H.E) H.E)) :
    (2 : ℚ) * (integralTraceForm H B hB (w • x) x : ℚ) =
      Algebra.trace ℚ H.E (H.conj (x : H.E) * x) := by
  have hcw : H.conj (w : H.E) = 1 - (w : H.E) := by
    have h := congrArg H.conj hw
    rw [map_mul, map_ofNat, map_add, map_one, conj_sqd] at h
    linear_combination (h + hw) / 2
  have hxi : xi H * H.sqd = -1 := by
    exact div_mul_cancel₀ _ (NativeRawHostCore.sqd_ne_zero H)
  let z := xi H * H.conj ((w : H.E) * x) * x
  have hz : z + H.conj z = H.conj (x : H.E) * x := by
    dsimp [z]
    simp only [map_mul, map_sub, map_one, conj_xi, conj_conj, hcw]
    linear_combination
      (-xi H * H.conj (x : H.E) * (x : H.E)) * hw +
      (-H.conj (x : H.E) * (x : H.E)) * hxi
  have htrace := congrArg (Algebra.trace ℚ H.E) hz
  rw [map_add, Algebra.trace_eq_of_algEquiv] at htrace
  rw [integralTraceForm_cast]
  change (2 : ℚ) * Algebra.trace ℚ H.E z = _
  linarith

theorem twice_coefficient_trace_halfRoot_eq_sum_sq
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (hconj : ∀ (τ : H.E →+* ℂ) (a : H.E), τ (H.conj a) = conj (τ a))
    (w : 𝓞 H.E) (hw : (2 : H.E) * (w : H.E) = 1 + H.sqd)
    (x : (coefficientIdeal H B : Submodule (𝓞 H.E) H.E)) :
    (2 : ℝ) * (integralTraceForm H B hB (w • x) x : ℝ) =
      ∑ τ : H.E →+* ℂ, ‖τ (x : H.E)‖ ^ 2 := by
  have ht := congrArg (fun a : ℚ => (a : ℝ))
    (twice_coefficient_trace_halfRoot H B hB w hw x)
  push_cast at ht
  rw [ht]
  have hs := congrArg Complex.re
    (NativeNumberFieldLattice.trace_eq_sum_complexEmbeddings
      (H.conj (x : H.E) * x))
  simp only [Complex.ratCast_re, Complex.re_sum] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [map_mul, hconj, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring

theorem coefficient_trace_halfRoot_pos
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (hconj : ∀ (τ : H.E →+* ℂ) (a : H.E), τ (H.conj a) = conj (τ a))
    (w : 𝓞 H.E) (hw : (2 : H.E) * (w : H.E) = 1 + H.sqd)
    (x : (coefficientIdeal H B : Submodule (𝓞 H.E) H.E)) (hx : x ≠ 0) :
    0 < integralTraceForm H B hB (w • x) x := by
  have hxE : (x : H.E) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨τ⟩ : Nonempty (H.E →+* ℂ) := inferInstance
  have hs : (0 : ℝ) < ∑ σ : H.E →+* ℂ, ‖σ (x : H.E)‖ ^ 2 := by
    apply Finset.sum_pos'
    · intro σ _
      positivity
    · refine ⟨τ, Finset.mem_univ _, ?_⟩
      exact sq_pos_of_pos (norm_pos_iff.mpr ((map_ne_zero τ).mpr hxE))
  rw [← twice_coefficient_trace_halfRoot_eq_sum_sq H B hB hconj w hw x] at hs
  have hi : (0 : ℝ) < (integralTraceForm H B hB (w • x) x : ℝ) := by linarith
  exact_mod_cast hi

/-- This is the pure positive block's actual source positivity input. -/
theorem positive_block_trace_halfRoot_pos
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (hconj : ∀ (τ : H.E →+* ℂ) (a : H.E), τ (H.conj a) = conj (τ a))
    (w : 𝓞 H.E) (hw : (2 : H.E) * (w : H.E) = 1 + H.sqd)
    (N : ℕ) (x : twistedLattice H B N) (hx : x ≠ 0) :
    0 < twistedTraceForm H B hB (fun _ => false) (w • x) x := by
  have hnon : twistedCoordinates H B N x ≠ 0 := by
    intro h
    apply hx
    apply (twistedCoordinates H B N).injective
    simpa using h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hnon
  rw [twistedTraceForm_apply]
  simp only [sgn, Bool.false_eq_true, ite_false, one_mul, map_smul, Pi.smul_apply]
  apply Finset.sum_pos'
  · intro j _
    by_cases h0 : twistedCoordinates H B N x j = 0
    · simp [h0]
    · exact (coefficient_trace_halfRoot_pos H B hB hconj w hw _ h0).le
  · exact ⟨i, Finset.mem_univ _, coefficient_trace_halfRoot_pos H B hB hconj w hw _ hi⟩

/-- The negative block has the opposite elliptic orientation; its original
alternating form is retained with the source sign epsilon=-1. -/
theorem negative_block_trace_halfRoot_pos
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (hconj : ∀ (τ : H.E →+* ℂ) (a : H.E), τ (H.conj a) = conj (τ a))
    (w : 𝓞 H.E) (hw : (2 : H.E) * (w : H.E) = 1 + H.sqd)
    (N : ℕ) (x : twistedLattice H B N) (hx : x ≠ 0) :
    0 < (-1 : ℤ) * twistedTraceForm H B hB (fun _ => true) (w • x) x := by
  have hp := positive_block_trace_halfRoot_pos H B hB hconj w hw N x hx
  rw [twistedTraceForm_apply] at hp ⊢
  simpa [sgn, Finset.sum_neg_distrib] using hp

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry NativeRawHostPolarization

/-- The actual native half-root supplies both pure-block positivity inputs.
The only assumptions are the original host regime and its half-different. -/
theorem nativeDyadicHalfRoot_pureBlockPositivity
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    (∀ x : (coefficientIdeal H.toHostRaw B : Submodule (𝓞 H.E) H.E), x ≠ 0 →
      0 < integralTraceForm H.toHostRaw B hB (G.w0 • x) x) ∧
    (∀ N : ℕ, ∀ x : twistedLattice H.toHostRaw B N, x ≠ 0 →
      0 < twistedTraceForm H.toHostRaw B hB (fun _ => false) (G.w0 • x) x) ∧
    (∀ N : ℕ, ∀ x : twistedLattice H.toHostRaw B N, x ≠ 0 →
      0 < (-1 : ℤ) * twistedTraceForm H.toHostRaw B hB (fun _ => true)
        (G.w0 • x) x) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  have hw : (2 : H.E) * (G.w0 : H.E) = 1 + H.sqd := by
    have ht := congrArg (algebraMap (𝓞 H.E) H.E) G.two_weight_eq_one_add_root
    simp only [map_mul, map_ofNat, map_add, map_one] at ht
    change (2 : H.E) * (G.w0 : H.E) = 1 + (G.rt : H.E) at ht
    have hroot : (G.rt : H.E) = H.sqd := rfl
    rwa [hroot] at ht
  have hc := nativeDyadicHostRaw_prescribed_embedding_conj e q d he hH
  exact ⟨fun x hx => coefficient_trace_halfRoot_pos H.toHostRaw B hB hc G.w0 hw x hx,
    fun N x hx => positive_block_trace_halfRoot_pos H.toHostRaw B hB hc G.w0 hw N x hx,
    fun N x hx => negative_block_trace_halfRoot_pos H.toHostRaw B hB hc G.w0 hw N x hx⟩

end RHLean.Analysis.AlpogeThin

end
