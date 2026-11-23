import RHLean.Geometry.NativeDyadicAdelicNorm
import RHLean.Geometry.NativePrescribedPolarizationLattice

/-!
# The actual finite-adelic comparison of the prescribed Hermitian spaces

The previously constructed norm-minus-one element supplies a diagonal
invertible matrix: its entry is one where the two signs agree and the
actual norm-minus-one element where they differ. Its inverse has entries
one or minus the conjugate of that same element. The resulting matrix
congruence compares the literal mapped Gram matrices of the existing
prescribed spaces.

The final specialization uses the source base space Y_0 with rank k+m-1
and (m-0)/2 negative entries, and the SAME prescribed W_j with m-j
negative entries. No norm solution, matrix isometry or complete Spaces
record is an input. The coefficient ideal and its lattice are unchanged.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Formalism/LocalRingCardinality/SpanPowerMembership/Spaces.lean,
cT_diagonal, diag_congr and diagUnit;
BaseFormAnisotropicOrthogonalSingle.lean, dSpace_gram_map, dSpace_congr
and spacesOfRanks.baseSpace_isometric_graded. The latter is the exact
finite-adelic compatibility field of the source DataSpaces.Spaces record.
The norm element comes from the native reconstruction of Adelic.lean,
using the same host field, both Gauss roots and restricted product.
The source archive/mirror states no license; attribution is retained
without assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

open NumberField
open scoped TensorProduct

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry.NativePrescribedHermitian

attribute [local instance] conjugationStar

/-- The literal diagonal base space Y_0 in the source construction. -/
def prescribedBaseSpace {φ : Frame} (H : HostRaw φ) (k m : ℕ) : HSpace H.E :=
  dSpace (k + m - 1) ((m - 0) / 2)

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

namespace RHLean.Geometry.NativeDyadicAdelicIsometry

open RHLean.Analysis RHLean.Analysis.AlpogeThin Formalism.FrobeniusOrbits
open NativePrescribedHermitian NativeRawHostPolarization NativeDyadicAdelicNorm

attribute [local instance] conjugationStar

private theorem cT_diagonal {n A : Type} [DecidableEq n] [CommRing A]
    (σ : A →+* A) (v : n → A) :
    Signature.cT σ (Matrix.diagonal v) = Matrix.diagonal (fun i => σ (v i)) := by
  ext i j
  simp only [Signature.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

private theorem diagonal_congr {n A : Type} [Fintype n] [DecidableEq n] [CommRing A]
    (σ : A →+* A) (v s t : n → A) (h : ∀ i, σ (v i) * s i * v i = t i) :
    Signature.cT σ (Matrix.diagonal v) * Matrix.diagonal s * Matrix.diagonal v =
      Matrix.diagonal t := by
  rw [cT_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext h)

private def diagonalUnit {n A : Type} [Fintype n] [DecidableEq n] [CommRing A]
    (v w : n → A) (h : ∀ i, v i * w i = 1) : Matrix.GeneralLinearGroup n A where
  val := Matrix.diagonal v
  inv := Matrix.diagonal w
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    exact (congrArg Matrix.diagonal (funext h)).trans Matrix.diagonal_one
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have h' : ∀ i, w i * v i = 1 := fun i => (mul_comm _ _).trans (h i)
    exact (congrArg Matrix.diagonal (funext h')).trans Matrix.diagonal_one

/-- The existing standard coordinate frame gives the literal diagonal Gram
matrix after any ring map; no new Hermitian form is chosen. -/
theorem dSpace_gram_map {E A : Type} [Field E] [NumberField E] [StarRing E]
    [CommRing A] (ι : E →+* A) (N a : ℕ) :
    (dSpace (E := E) N a).gram.map ι =
      Matrix.diagonal fun i : Fin N => (sgn (negTail N a i) : A) := by
  ext i j
  rw [Matrix.map_apply]
  refine (congrArg ι (stdSpace_gram_apply N (negTail N a) (N - a) a i j)).trans ?_
  change ι (if i = j then (sgn (negTail N a i) : E) else 0) =
    if i = j then (sgn (negTail N a i) : A) else 0
  by_cases h : i = j <;> simp [h, map_sgn]

private theorem inverse_of_norm_neg_one {A : Type} [CommRing A]
    (σ : A →+* A) (u : A) (hu : σ u * u = -1) : u * -(σ u) = 1 := by
  rw [mul_neg, mul_comm u (σ u), hu, neg_neg]

private theorem prescribed_gram_congr {φ : Formalism.HC.Frame} (H : HostRaw φ)
    {A : Type} [CommRing A] (ι : H.E →+* A) (σ : A →+* A) (k m j : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin (k + m - 1)) A)
    (hg : Signature.cT σ g.val *
        Matrix.diagonal (fun i : Fin (k + m - 1) =>
          (sgn (negTail (k + m - 1) ((m - 0) / 2) i) : A)) * g.val =
        Matrix.diagonal (fun i : Fin (k + m - 1) =>
          (sgn (negTail (k + m - 1) (m - j) i) : A))) :
    Signature.cT σ g.val *
        ((prescribedBaseSpace H k m).gram.map ι :
          Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) A) * g.val =
      ((prescribedSpace H k m j).gram.map ι :
        Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) A) := by
  have hbase :
      ((prescribedBaseSpace H k m).gram.map ι :
        Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) A) =
      Matrix.diagonal (fun i : Fin (k + m - 1) =>
        (sgn (negTail (k + m - 1) ((m - 0) / 2) i) : A)) :=
    dSpace_gram_map ι (k + m - 1) ((m - 0) / 2)
  have hgraded :
      ((prescribedSpace H k m j).gram.map ι :
        Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) A) =
      Matrix.diagonal (fun i : Fin (k + m - 1) =>
        (sgn (negTail (k + m - 1) (m - j) i) : A)) :=
    dSpace_gram_map ι (k + m - 1) (m - j)
  exact (congrArg
    (fun J : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) A =>
      Signature.cT σ g.val * J * g.val) hbase).trans (hg.trans hgraded.symm)

section Host

variable (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]

local notation "EH" => alpogeNativeHostField e q d
local notation "F" => maximalRealSubfield EH
local notation "Af" => IsDedekindDomain.FiniteAdeleRing (𝓞 F) F
local notation "AE" => EH ⊗[F] Af

/-- The explicit invertible sign-change matrix, constructed from the SAME
native adelic norm element and its proved inverse. -/
def diagonalChange (he : 2 ≤ e) (hH : HostHyp q d) (N a b : ℕ) :
    Matrix.GeneralLinearGroup (Fin N) AE :=
  diagonalUnit (n := Fin N) (A := AE)
    (fun i => if negTail N a i = negTail N b i then 1 else normMinusOne e q d he hH)
    (fun i => if negTail N a i = negTail N b i then 1
      else -(tensorConjugation e q d he hH (normMinusOne e q d he hH)))
    (by
      intro i
      by_cases h : negTail N a i = negTail N b i
      · simp only [ite_eq_left h, one_mul]
      · simp only [ite_eq_right h]
        exact inverse_of_norm_neg_one (A := AE) (tensorConjugation e q d he hH)
          (normMinusOne e q d he hH) (normMinusOne_spec e q d he hH))

theorem diagonalChange_val (he : 2 ≤ e) (hH : HostHyp q d) (N a b : ℕ) :
    (diagonalChange e q d he hH N a b).val =
      Matrix.diagonal (fun i => if negTail N a i = negTail N b i then 1
        else normMinusOne e q d he hH) := rfl

theorem diagonalChange_inv_val (he : 2 ≤ e) (hH : HostHyp q d) (N a b : ℕ) :
    (diagonalChange e q d he hH N a b).inv =
      Matrix.diagonal (fun i => if negTail N a i = negTail N b i then 1
        else -(tensorConjugation e q d he hH (normMinusOne e q d he hH))) := rfl

theorem diagonalChange_congr (he : 2 ≤ e) (hH : HostHyp q d) (N a b : ℕ) :
    Signature.cT (tensorConjugation e q d he hH)
        (diagonalChange e q d he hH N a b).val *
      Matrix.diagonal (fun i : Fin N => (sgn (negTail N a i) : AE)) *
        (diagonalChange e q d he hH N a b).val =
      Matrix.diagonal (fun i : Fin N => (sgn (negTail N b i) : AE)) := by
  simp only [diagonalChange_val]
  refine diagonal_congr _ _ _ _ (fun i => ?_)
  by_cases h : negTail N a i = negTail N b i
  · simp only [ite_eq_left h, map_one, one_mul, mul_one, h]
  · simp only [ite_eq_right h]
    have hs : (sgn (negTail N b i) : AE) = -(sgn (negTail N a i)) := by
      cases h₁ : negTail N a i <;> cases h₂ : negTail N b i <;> simp_all [sgn]
    rw [hs, mul_right_comm, normMinusOne_spec]
    ring

/-- The original base-to-W_j Gram congruence on the actual native host,
using the SAME prescribed space as the inverse-ideal lattice construction. -/
theorem baseSpace_congr_prescribed (he : 2 ≤ e) (hH : HostHyp q d) (k m j : ℕ) :
    let H := nativeDyadicHostRaw e q d he hH
    let g := diagonalChange e q d he hH (k + m - 1) ((m - 0) / 2) (m - j)
    Signature.cT (tensorConjugation e q d he hH) g.val *
      ((prescribedBaseSpace H k m).gram.map
        (Algebra.TensorProduct.includeLeftRingHom : EH →+* AE) :
          Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) AE) * g.val =
      ((prescribedSpace H k m j).gram.map
        (Algebra.TensorProduct.includeLeftRingHom : EH →+* AE) :
          Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) AE) := by
  exact prescribed_gram_congr (nativeDyadicHostRaw e q d he hH) (A := AE)
    (Algebra.TensorProduct.includeLeftRingHom : EH →+* AE)
    (tensorConjugation e q d he hH) k m j
    (diagonalChange e q d he hH (k + m - 1) ((m - 0) / 2) (m - j))
    (diagonalChange_congr e q d he hH (k + m - 1) ((m - 0) / 2) (m - j))

/-- Exact finite-adelic compatibility required by the source Spaces record.
The coordinate equivalence and invertible matrix are constructed here. -/
theorem baseSpace_isometric_prescribed (he : 2 ≤ e) (hH : HostHyp q d) (k m j : ℕ) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ ε : Fin (prescribedBaseSpace H k m).rank ≃ Fin (prescribedSpace H k m j).rank,
      ∃ g : Matrix.GeneralLinearGroup (Fin (prescribedSpace H k m j).rank) AE,
        Signature.cT (tensorConjugation e q d he hH) g.val *
          (((prescribedBaseSpace H k m).gram.reindex ε ε).map
            (Algebra.TensorProduct.includeLeftRingHom : EH →+* AE)) * g.val =
          (prescribedSpace H k m j).gram.map
            (Algebra.TensorProduct.includeLeftRingHom : EH →+* AE) := by
  refine ⟨Equiv.refl _,
    diagonalChange e q d he hH (k + m - 1) ((m - 0) / 2) (m - j), ?_⟩
  exact baseSpace_congr_prescribed e q d he hH k m j

end Host

end RHLean.Geometry.NativeDyadicAdelicIsometry

end
