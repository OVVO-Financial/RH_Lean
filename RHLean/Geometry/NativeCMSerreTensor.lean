import RHLean.Geometry.NativeCMHermitianForm
import RHLean.Geometry.NativeCMEllipticPolarization
import RHLean.Geometry.NativeThetaFullLevelCost
import RHLean.Geometry.NativePrescribedGeometricDatum

/-!
# The Serre projective module on the actual trace-polarized lattice

The quadratic-order Hermitian dual frame constructs the inclusion and
projection of the original module into a finite free module, with an
explicit idempotent matrix. Tensoring these maps with any coefficient
module produces a split retraction and identifies the Serre tensor module
with the fixed module of that same idempotent. The literal coefficient
module is `B⁻¹`, not a free `O_E` replacement.

The complex fibre rank is `[E:Q]/2` times the original `O_E` rank. This is
the dimension input to a CM-degree calculation, not an arithmetic-degree
formula. Representability of this point functor by an abelian scheme, its
line bundle and positivity on each pure-signature block remain distinct
geometric constructions.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/`
`PowObjGeometricallyConnected.lean`, `Serre.Summand` and `IsTensor.ofRetract`;
`Proofs/CubicalLineBundles/ExistsCmTensorLatticeCurvePrincipalTriple.lean`.
This module reconstructs the projective module and tensor algebra used by
those scheme-level suppliers. It imports no source compiled object or RH
conclusion. The source mirror states no license; attribution is retained
without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped TensorProduct Pointwise nonZeroDivisors

namespace RHLean.Geometry.NativeCM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : NativeGeometricHost E} (D : TraceLattice H) (ε : ℤˣ)

/-- A finite dual frame for the explicit Hermitian form on the actual
module. No bound or positivity is included as a record field. -/
structure TraceFrame where
  n : ℕ
  x : Fin n → D.La
  y : Fin n → D.La
  resolve : ∀ a, a = ∑ i, kLin D ε a (y i) • x i

/-- The frame is a conclusion of trace perfection and actual projectivity. -/
def traceFrame : TraceFrame D ε := Classical.choice (by
  obtain ⟨n, x, y, hxy⟩ := kLin_dual_frame D ε
  exact ⟨⟨n, x, y, hxy⟩⟩)

namespace TraceFrame

variable {D ε} (F : TraceFrame D ε)

/-- Coordinates are the actual Hermitian pairings with the dual frame. -/
def incl : D.La →ₗ[OK H] (Fin F.n → OK H) :=
  LinearMap.pi fun i =>
    { toFun := fun a => kLin D ε a (F.y i)
      map_add' := fun a b => kFun_add_left D ε a b (F.y i)
      map_smul' := fun c a => kFun_smul D ε c a (F.y i) }

/-- The free-module projection uses the same integral frame vectors. -/
def proj : (Fin F.n → OK H) →ₗ[OK H] D.La where
  toFun a := ∑ i, a i • F.x i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, mul_smul]

theorem incl_apply (a : D.La) (i : Fin F.n) :
    F.incl a i = kLin D ε a (F.y i) := rfl

theorem proj_apply (a : Fin F.n → OK H) :
    F.proj a = ∑ i, a i • F.x i := rfl

/-- The actual module is a summand, with a proved retraction identity. -/
theorem proj_incl : F.proj ∘ₗ F.incl = LinearMap.id := by
  ext a
  exact (F.resolve a).symm

/-- The source's idempotent matrix, on the actual Hermitian dual frame. -/
def matrix : Matrix (Fin F.n) (Fin F.n) (OK H) :=
  LinearMap.toMatrix' (F.incl ∘ₗ F.proj)

theorem matrix_apply (i j : Fin F.n) :
    F.matrix i j = kLin D ε (F.x j) (F.y i) := by
  simp [matrix, LinearMap.toMatrix'_apply, incl, proj]

theorem matrix_mul_self : F.matrix * F.matrix = F.matrix := by
  rw [matrix, ← LinearMap.toMatrix'_comp, LinearMap.comp_assoc,
    ← LinearMap.comp_assoc _ _ F.proj, F.proj_incl, LinearMap.id_comp]

variable (A : Type) [AddCommGroup A] [Module (OK H) A]

/-- Tensoring preserves the exact retraction before any rank or degree
calculation. No flatness assumption on the point module `A` is needed. -/
theorem tensor_proj_incl :
    F.proj.rTensor A ∘ₗ F.incl.rTensor A = LinearMap.id := by
  rw [← LinearMap.rTensor_comp, F.proj_incl, LinearMap.rTensor_id]

def tensorIdempotent :
    Module.End (OK H) ((Fin F.n → OK H) ⊗[OK H] A) :=
  F.incl.rTensor A ∘ₗ F.proj.rTensor A

theorem tensorIdempotent_comp_self :
    F.tensorIdempotent A ∘ₗ F.tensorIdempotent A = F.tensorIdempotent A := by
  rw [tensorIdempotent, LinearMap.comp_assoc,
    ← LinearMap.comp_assoc _ _ (F.proj.rTensor A),
    F.tensor_proj_incl A, LinearMap.id_comp]

/-- The fixed module of the constructed idempotent. -/
def tensorFixed : Submodule (OK H) ((Fin F.n → OK H) ⊗[OK H] A) :=
  LinearMap.ker (F.tensorIdempotent A - LinearMap.id)

/-- The Serre tensor point module is identified with the actual fixed
module. This does not assert scheme-level representability. -/
def tensorEquivFixed : D.La ⊗[OK H] A ≃ₗ[OK H] F.tensorFixed A where
  toFun z := ⟨F.incl.rTensor A z, by
    change (F.incl.rTensor A (F.proj.rTensor A (F.incl.rTensor A z))) -
      F.incl.rTensor A z = 0
    have hz := LinearMap.congr_fun (F.tensor_proj_incl A) z
    change F.proj.rTensor A (F.incl.rTensor A z) = z at hz
    rw [hz, sub_self]⟩
  invFun z := F.proj.rTensor A z
  left_inv z := LinearMap.congr_fun (F.tensor_proj_incl A) z
  right_inv z := by
    apply Subtype.ext
    have hz := z.property
    change F.incl.rTensor A (F.proj.rTensor A z.1) - z.1 = 0 at hz
    exact sub_eq_zero.mp hz
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_smul _ _ _)

theorem tensorEquivFixed_tmul (x : D.La) (a : A) :
    (F.tensorEquivFixed A (x ⊗ₜ[OK H] a) :
      (Fin F.n → OK H) ⊗[OK H] A) = F.incl x ⊗ₜ[OK H] a := by
  change F.incl.rTensor A (x ⊗ₜ[OK H] a) = F.incl x ⊗ₜ[OK H] a
  rw [LinearMap.rTensor_tmul]

end TraceFrame

/-- The same finite-projective module has the CM dimension used by the
source's Serre polarized triple construction. -/
theorem complex_fibre_rank [Algebra (OK H) ℂ] :
    Module.finrank ℂ (ℂ ⊗[OK H] D.La) =
      Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) D.La := by
  obtain ⟨hfin, hproj, hrank⟩ :=
    (OK_isDedekindDomain_and_projective E H).2.2.2.2.2 D.La D.fin D.proj
  have := hfin
  have := hproj
  rw [NativeThetaFullLevelCost.finrank_fibre, hrank]

/-- In particular the complete prescribed lattice retains its full
signature rank in the complex fibre. -/
theorem datum_complex_fibre_rank (D : NativeGeometricDatum H)
    [Algebra (OK H) ℂ] :
    Module.finrank ℂ (ℂ ⊗[OK H] D.La) =
      Module.finrank ℚ E / 2 * (D.p + D.q) := by
  rw [complex_fibre_rank (traceLatticeOfDatum D), D.rank]

end RHLean.Geometry.NativeCM

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]

/-- Serre tensor points of the ACTUAL normalized CM elliptic seed with the
ACTUAL coefficient ideal. Its order action is the quotient multiplication
constructed in `EllipticSeed.torusModule`. -/
abbrev coefficientSerrePoints (G : NativeGeometricHost H.E) (τ : H.E →+* ℂ)
    (B : Ideal (𝓞 H.E)) :=
  coefficientIdeal H B ⊗[OK G] EllipticSeed.Torus G τ

/-- The original full CM coefficient action is retained on the Serre
points by acting on the inverse-ideal factor. It is not replaced by only
the quadratic-order action on the elliptic seed. -/
theorem coefficientSerrePoints_smul_tmul (G : NativeGeometricHost H.E)
    (τ : H.E →+* ℂ) (B : Ideal (𝓞 H.E)) (a : 𝓞 H.E)
    (x : coefficientIdeal H B) (z : EllipticSeed.Torus G τ) :
    (a • x) ⊗ₜ[OK G] z = a • (x ⊗ₜ[OK G] z : coefficientSerrePoints H G τ B) :=
  TensorProduct.smul_tmul' a x z

/-- The idempotent is built from the original trace-polarized ideal. -/
def coefficientSerreFrame (G : NativeGeometricHost H.E)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (ε : ℤˣ) :
    TraceFrame (coefficientTraceLattice H G hbar B hB) ε :=
  traceFrame (coefficientTraceLattice H G hbar B hB) ε

/-- This is the genuine analytic-seed point module realization by the
same explicit integral idempotent, not an unspecified point module. -/
def coefficientSerreFixedEquiv (G : NativeGeometricHost H.E)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (ε : ℤˣ) (τ : H.E →+* ℂ) :
    coefficientSerrePoints H G τ B ≃ₗ[OK G]
      (coefficientSerreFrame H G hbar B hB ε).tensorFixed (EllipticSeed.Torus G τ) :=
  (coefficientSerreFrame H G hbar B hB ε).tensorEquivFixed (EllipticSeed.Torus G τ)

/-- On each original point-tensor the realization uses the actual Hermitian
frame coordinate map and the original elliptic point class. -/
theorem coefficientSerreFixedEquiv_tmul (G : NativeGeometricHost H.E)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (ε : ℤˣ) (τ : H.E →+* ℂ) (x : coefficientIdeal H B) (z : ℂ) :
    ((coefficientSerreFixedEquiv H G hbar B hB ε τ)
      (x ⊗ₜ[OK G] (QuotientAddGroup.mk' (EllipticSeed.period G τ).range z)) :
        (Fin (coefficientSerreFrame H G hbar B hB ε).n → OK G) ⊗[OK G]
          EllipticSeed.Torus G τ) =
      (coefficientSerreFrame H G hbar B hB ε).incl x ⊗ₜ[OK G]
        QuotientAddGroup.mk' (EllipticSeed.period G τ).range z :=
  (coefficientSerreFrame H G hbar B hB ε).tensorEquivFixed_tmul
    (EllipticSeed.Torus G τ) x _

/-- The rank-one `O_E` coefficient module is carried into the quadratic
Serre base with its exact `[E:Q]/2` rank. It is never declared free over
`O_E`. -/
theorem coefficient_serre_rank (G : NativeGeometricHost H.E)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) :
    Module.finrank (OK G) (coefficientIdeal H B) = Module.finrank ℚ H.E / 2 := by
  obtain ⟨-, -, hrank⟩ := (OK_isDedekindDomain_and_projective H.E G).2.2.2.2.2
    (coefficientIdeal H B) (coefficientIdeal_finite_over_integers H B)
      (coefficientIdeal_projective H B)
  rw [hrank, coefficientIdeal_rank_over_integers H B hB, mul_one]

/-- The literal inverse-ideal fibre has the dimension required by the
CM calculation; all finite-projective inputs come from that same ideal. -/
theorem coefficient_complex_fibre_rank (G : NativeGeometricHost H.E)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    [Algebra (OK G) ℂ] :
    Module.finrank ℂ (ℂ ⊗[OK G] coefficientIdeal H B) =
      Module.finrank ℚ H.E / 2 := by
  rw [complex_fibre_rank (coefficientTraceLattice H G hbar B hB),
    coefficientIdeal_rank_over_integers H B hB, mul_one]

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization
end

noncomputable section

open NumberField
open scoped Pointwise nonZeroDivisors TensorProduct

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM
open NativeRawHostPolarization

/-- One actually constructed half-different is retained through the native
CM host, its proved conjugation compatibility, the trace-Hermitian frame,
and the analytic elliptic-seed Serre point module. No compatible host,
Hermitian form, projective presentation or rank is assumed at this endpoint.
The scalar is the exact complex dimension of the coefficient tensor, not
an arithmetic degree or an estimate. -/
theorem nativeDyadicHost_exists_coefficientSerreConstruction
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ (ε : ℤˣ) (τ : H.E →+* ℂ),
        let F := coefficientSerreFrame H.toHostRaw G
          (nativeDyadicGeometricHost_bar_eq e q d he hH) B hB ε
        Module.Finite (OK G) (coefficientIdeal H.toHostRaw B) ∧
        Module.Projective (OK G) (coefficientIdeal H.toHostRaw B) ∧
        F.proj ∘ₗ F.incl = LinearMap.id ∧
        F.matrix * F.matrix = F.matrix ∧
        Nonempty (coefficientSerrePoints H.toHostRaw G τ B ≃ₗ[OK G]
          F.tensorFixed (EllipticSeed.Torus G τ)) ∧
        Module.finrank (OK G) (coefficientIdeal H.toHostRaw B) = 2 * 2 ^ e := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_⟩
  intro ε τ
  let F := coefficientSerreFrame H.toHostRaw G
    (nativeDyadicGeometricHost_bar_eq e q d he hH) B hB ε
  obtain ⟨hfin, hproj, -⟩ := (OK_isDedekindDomain_and_projective H.E G).2.2.2.2.2
    (coefficientIdeal H.toHostRaw B) (coefficientIdeal_finite_over_integers H.toHostRaw B)
      (coefficientIdeal_projective H.toHostRaw B)
  refine ⟨hfin, hproj, F.proj_incl, F.matrix_mul_self,
    ⟨coefficientSerreFixedEquiv H.toHostRaw G
      (nativeDyadicGeometricHost_bar_eq e q d he hH) B hB ε τ⟩, ?_⟩
  rw [coefficient_serre_rank H.toHostRaw G B hB]
  change Module.finrank ℚ (nativeDyadicHostRaw e q d he hH).E / 2 = 2 * 2 ^ e
  rw [nativeDyadicHostRaw_finrank_E, nativeDyadicFrame_ord]
  omega

end RHLean.Analysis.AlpogeThin
end
