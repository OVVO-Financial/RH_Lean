import RHLean.Geometry.NativeCMSerreGramForm
import RHLean.Geometry.NativeCMSerreEigenlatticeDegree

/-!
# The signed tensor-bundle Gram and the literal integral eigenline

The four pullbacks in the explicit Serre bundle have a computed Hermitian
Gram. Its two cross terms recombine using w + conjugate(w) = 1. The actual
native trace formula then identifies the result with the sum over all
root-fixing embeddings of the original integral tensor. On its genuine
identity-character eigenmodule the result is exactly the coordinate-line
norm used by the existing AllWt degree.

This is native algebraic glue to the attributed tensor-bundle Gram and
integral eigenlattice constructors. It does not identify a chosen form
with a line-bundle curvature. The later analytic seed chart comparison
must supply that geometric identification for the same four pullbacks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open NumberField Complex
open scoped Classical BigOperators Pointwise nonZeroDivisors TensorProduct ComplexConjugate

namespace RHLean.Geometry.NativeCM.SerreGram

/-- The Gram of the four signed pullbacks, in their actual order. -/
def squareGram (c : ℂ) (a b a' b' : ℂ) : ℂ :=
  c * (a + b) * conj (a' + b') - c * a * conj a' - c * b * conj b' +
    c * 0 * conj 0

theorem squareGram_eq (c a b a' b' : ℂ) :
    squareGram c a b a' b' = c * (a * conj b' + b * conj a') := by
  simp only [squareGram, map_add, map_zero]
  ring

/-- The actual half-root cancels the extra polarization factor. -/
theorem sum_squareGram {I : Type} [Fintype I]
    (c ω : ℂ) (hω : ω + conj ω = 1) (g : I → I → ℂ)
    (hg : ∀ i j, g j i = conj (g i j)) (p q : I → ℂ) :
    (∑ k : I × I, squareGram c (g k.1 k.2 * p k.1) (ω * p k.2)
      (g k.1 k.2 * q k.1) (ω * q k.2)) =
        c * ∑ k : I × I, g k.1 k.2 * p k.1 * conj (q k.2) := by
  have h (i j : I) :
      squareGram c (g i j * p i) (ω * p j) (g i j * q i) (ω * q j) =
        c * (conj ω * (g i j * p i * conj (q j)) +
          ω * (g j i * p j * conj (q i))) := by
    rw [squareGram_eq]
    simp only [map_mul]
    rw [← hg i j]
    ring
  simp_rw [h]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hs : (∑ k : I × I, g k.2 k.1 * p k.2 * conj (q k.1)) =
      ∑ k : I × I, g k.1 k.2 * p k.1 * conj (q k.2) :=
    Fintype.sum_equiv (Equiv.prodComm I I) _ _ fun _ => rfl
  rw [hs, ← add_mul, add_comm (conj ω), hω, one_mul]

/-- Expand both finite frame evaluations in the same ordered indices.
The permutations below exchange only independent sums, never the
coefficients attached to a frame index. -/
theorem sum_frame_pairing {I J : Type} [Fintype I] [Fintype J]
    (a b : I → J → ℂ) (p q : I → ℂ) :
    (∑ k : I × I, (∑ ρ : J, a k.1 ρ * conj (b k.2 ρ)) *
        p k.1 * conj (q k.2)) =
      ∑ ρ : J, (∑ i : I, p i * a i ρ) * conj (∑ j : I, q j * b j ρ) := by
  calc
    _ = ∑ i : I, ∑ j : I, ∑ ρ : J,
        a i ρ * conj (b j ρ) * p i * conj (q j) := by
      simp only [Fintype.sum_prod_type, Finset.sum_mul]
    _ = ∑ i : I, ∑ ρ : J, ∑ j : I,
        a i ρ * conj (b j ρ) * p i * conj (q j) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Finset.sum_comm
    _ = ∑ ρ : J, ∑ i : I, ∑ j : I,
        a i ρ * conj (b j ρ) * p i * conj (q j) := Finset.sum_comm
    _ = ∑ ρ : J, ∑ i : I, ∑ j : I,
        (p i * a i ρ) * (conj (q j) * conj (b j ρ)) := by
      refine Finset.sum_congr rfl fun ρ _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = _ := by
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul]

end RHLean.Geometry.NativeCM.SerreGram

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM SerreEigenlattice

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E)
    (F : Type) [Field F] [Algebra H.E F]
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)

include hbar in
theorem coefficientEmbedding_conjugate (σ : F →+* ℂ) (ρ : RootAut G) (x : H.E) :
    σ (algebraMap H.E F (ρ.1 (H.conj x))) =
      conj (σ (algebraMap H.E F (ρ.1 x))) := by
  let τ : H.E →+* ℂ := (σ.comp (algebraMap H.E F)).comp ρ.1.toRingHom
  have hc (a : 𝓞 H.E) : τ (H.conj (a : H.E)) = conj (τ (a : H.E)) := by
    have hb : ((G.bar a : 𝓞 H.E) : H.E) = H.conj (a : H.E) :=
      congrArg (fun b : 𝓞 H.E => (b : H.E)) (hbar a)
    rw [← hb, G.bar_eq, IsCMField.complexEmbedding_complexConj]
  change τ (H.conj x) = conj (τ x)
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 H.E) x
  simp only [map_div₀, hc]

def embeddedPairing (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (σ : F →+* ℂ) (i : Fin (coefficientSerreFrame H G hbar B hB 1).n)
    (t : IntegralTensor H G F B) : ℂ :=
  σ (algebraMap (𝓞 F) F (integralPairing H G F hbar B hB i t))

def embeddedCoefficient (σ : F →+* ℂ) (c : OK G) : ℂ :=
  σ (algebraMap (𝓞 F) F (algebraMap (OK G) (𝓞 F) c))

theorem embeddedCoefficient_bar (σ : F →+* ℂ) (c : OK G) :
    embeddedCoefficient H G F σ (barOK G c) =
      conj (embeddedCoefficient H G F σ c) := by
  change embed G (σ.comp (algebraMap H.E F)) (barOK G c) =
    conj (embed G (σ.comp (algebraMap H.E F)) c)
  exact EllipticSeed.embed_bar G (σ.comp (algebraMap H.E F)) c

theorem embeddedCoefficient_halfRoot (σ : F →+* ℂ) :
    embeddedCoefficient H G F σ (wK G) +
      conj (embeddedCoefficient H G F σ (wK G)) = 1 := by
  rw [← embeddedCoefficient_bar]
  change embed G (σ.comp (algebraMap H.E F)) (wK G) +
    embed G (σ.comp (algebraMap H.E F)) (barOK G (wK G)) = 1
  rw [← map_add, wK_add_barOK, map_one]

theorem embeddedCoefficient_kLin_sum
    (hroot : (G.rt : H.E) = H.sqd) (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (σ : F →+* ℂ) (x y : (coefficientIdeal H B : Submodule (𝓞 H.E) H.E)) :
    embeddedCoefficient H G F σ (kLin (coefficientTraceLattice H G hbar B hB) 1 x y) =
      ∑ ρ, σ (coefficientEvaluation H G F B x ρ) *
        conj (σ (coefficientEvaluation H G F B y ρ)) := by
  have he := congrArg σ (coefficientEvaluation_pairing H G F hroot hbar B hB x y)
  simp only [map_sum, map_mul] at he
  change embeddedCoefficient H G F σ
    (kLin (coefficientTraceLattice H G hbar B hB) 1 x y) = _ at he
  rw [he]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [coefficientDualEvaluation, coefficientEmbedding_conjugate H G F hbar]
  rfl

theorem integralEvaluation_frame
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (t : IntegralTensor H G F B) (ρ : RootAut G) :
    integralEvaluation H G F B t ρ =
      ∑ i, algebraMap (𝓞 F) F (integralPairing H G F hbar B hB i t) *
        coefficientEvaluation H G F B ((coefficientSerreFrame H G hbar B hB 1).x i) ρ := by
  calc
    _ = integralEvaluation H G F B
        (∑ i, integralPairing H G F hbar B hB i t •
          (1 ⊗ₜ[OK G] (coefficientSerreFrame H G hbar B hB 1).x i)) ρ :=
      congrArg (fun s => integralEvaluation H G F B s ρ)
        (integralTensor_resolve H G F hbar B hB t)
    _ = _ := by
      rw [map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      have he : integralEvaluation H G F B
          (1 ⊗ₜ[OK G] (coefficientSerreFrame H G hbar B hB 1).x i) =
          coefficientEvaluation H G F B ((coefficientSerreFrame H G hbar B hB 1).x i) :=
        (integralEvaluation_tmul H G F B 1 _).trans (one_smul _ _)
      rw [he]
      change integralPairing H G F hbar B hB i t •
          coefficientEvaluation H G F B ((coefficientSerreFrame H G hbar B hB 1).x i) ρ = _
      exact Algebra.smul_def _ _

/-- The exact four-pullback expression of the constructed tensor bundle,
evaluated on the original integral tangent coefficients. -/
def tensorOriginGram (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (σ : F →+* ℂ) (n : ℝ) (t u : IntegralTensor H G F B) : ℂ :=
  let fr := coefficientSerreFrame H G hbar B hB 1
  ∑ k : Fin fr.n × Fin fr.n,
    SerreGram.squareGram n
      (embeddedCoefficient H G F σ (kLin (coefficientTraceLattice H G hbar B hB) 1
        (fr.x k.1) (fr.x k.2)) * embeddedPairing H G F hbar B hB σ k.1 t)
      (embeddedCoefficient H G F σ (wK G) * embeddedPairing H G F hbar B hB σ k.2 t)
      (embeddedCoefficient H G F σ (kLin (coefficientTraceLattice H G hbar B hB) 1
        (fr.x k.1) (fr.x k.2)) * embeddedPairing H G F hbar B hB σ k.1 u)
      (embeddedCoefficient H G F σ (wK G) * embeddedPairing H G F hbar B hB σ k.2 u)

theorem tensorOriginGram_eq_sum
    (hroot : (G.rt : H.E) = H.sqd) (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (σ : F →+* ℂ) (n : ℝ) (t u : IntegralTensor H G F B) :
    tensorOriginGram H G F hbar B hB σ n t u =
      (n : ℂ) * ∑ ρ, σ (integralEvaluation H G F B t ρ) *
        conj (σ (integralEvaluation H G F B u ρ)) := by
  let fr := coefficientSerreFrame H G hbar B hB 1
  let g : Fin fr.n → Fin fr.n → ℂ := fun i j =>
    embeddedCoefficient H G F σ (kLin (coefficientTraceLattice H G hbar B hB) 1
      (fr.x i) (fr.x j))
  have hg (i j : Fin fr.n) : g j i = conj (g i j) := by
    change embeddedCoefficient H G F σ (kLin (coefficientTraceLattice H G hbar B hB) 1
      (fr.x j) (fr.x i)) = conj (embeddedCoefficient H G F σ
        (kLin (coefficientTraceLattice H G hbar B hB) 1 (fr.x i) (fr.x j)))
    rw [kLin_barOK, embeddedCoefficient_bar]
  have he : tensorOriginGram H G F hbar B hB σ n t u =
      (n : ℂ) * ∑ k : Fin fr.n × Fin fr.n, g k.1 k.2 *
        embeddedPairing H G F hbar B hB σ k.1 t *
        conj (embeddedPairing H G F hbar B hB σ k.2 u) :=
    -- Supply both coefficient families: `?p k.1` is not a higher-order
    -- pattern, so leaving them implicit forces unbounded unfolding.
    SerreGram.sum_squareGram (n : ℂ) (embeddedCoefficient H G F σ (wK G))
      (embeddedCoefficient_halfRoot H G F σ) g hg
      (fun i => embeddedPairing H G F hbar B hB σ i t)
      (fun i => embeddedPairing H G F hbar B hB σ i u)
  rw [he]
  congr 1
  let a : Fin fr.n → RootAut G → ℂ := fun i ρ =>
    σ (coefficientEvaluation H G F B (fr.x i) ρ)
  let p : Fin fr.n → ℂ := fun i => embeddedPairing H G F hbar B hB σ i t
  let q : Fin fr.n → ℂ := fun i => embeddedPairing H G F hbar B hB σ i u
  change (∑ k : Fin fr.n × Fin fr.n, g k.1 k.2 * p k.1 * conj (q k.2)) = _
  have hg' (i j : Fin fr.n) : g i j = ∑ ρ : RootAut G, a i ρ * conj (a j ρ) :=
    embeddedCoefficient_kLin_sum H G F hbar hroot B hB σ (fr.x i) (fr.x j)
  calc
    _ = ∑ k : Fin fr.n × Fin fr.n,
        (∑ ρ : RootAut G, a k.1 ρ * conj (a k.2 ρ)) * p k.1 * conj (q k.2) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hg' k.1 k.2]
    _ = ∑ ρ : RootAut G, (∑ i : Fin fr.n, p i * a i ρ) *
        conj (∑ j : Fin fr.n, q j * a j ρ) :=
      SerreGram.sum_frame_pairing a a p q
    _ = _ := by
      refine Finset.sum_congr rfl fun ρ _ => ?_
      have htρ := congrArg σ (integralEvaluation_frame H G F hbar B hB t ρ)
      have huρ := congrArg σ (integralEvaluation_frame H G F hbar B hB u ρ)
      simp only [map_sum, map_mul] at htρ huρ
      exact congrArg₂ (· * ·) htρ.symm
        (congrArg (fun z : ℂ => conj z) huρ.symm)

/-- The actual identity-character eigenmodule has the coordinate norm,
with its full integral index retained by eigenCoordinate. -/
theorem tensorOriginGram_eigen
    (hroot : (G.rt : H.E) = H.sqd) (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (σ : F →+* ℂ) (n : ℝ) (t u : integralEigenmodule H G F B) :
    tensorOriginGram H G F hbar B hB σ n t u =
      (n : ℂ) * σ (eigenCoordinate H G F B t) *
        conj (σ (eigenCoordinate H G F B u)) := by
  rw [tensorOriginGram_eq_sum H G F hbar hroot,
    (integralEigenmodule_iff_coordinates H G F hroot hbar B hB t).mp t.property,
    (integralEigenmodule_iff_coordinates H G F hroot hbar B hB u).mp u.property]
  simp [eigenCoordinate, Pi.single_apply, apply_ite, mul_assoc]

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
