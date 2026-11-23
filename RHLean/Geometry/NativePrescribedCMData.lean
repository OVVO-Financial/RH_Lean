import RHLean.Analysis.AlpogeThin.NativeDyadicHostDer
import RHLean.Geometry.NativeDyadicAdelicIsometry

/-!
# The complete CM datum on the actual native host

This constructs all four fields of the original `DataSpaces.CMData` record:
the full unramified CM predicate (including an integral conjugation-separating
element at every maximal ideal), total reality of the actual maximal real
subfield, degree two, and the literal fixed-field equality. The involution
is the SAME `conjugationStar` already used by the prescribed Hermitian space
and its coefficient-twisted lattice.

The record's algebra homomorphism and its finite-adelic scalar extension are
proved equal to those in the constructed norm-minus-one element and diagonal
isometry. No CM datum, norm witness or isometry is assumed at the native
endpoint. This does not construct the whole `Spaces` or `D7` record: their
auxiliary prime must satisfy the same ray-norm congruences and level/window
constraints, and their actual member, period-map and coefficient data remain
separate constructions.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/HermitianLattices/StatementMass.lean`, `IsCMUnram`;
`src/Formalism/LocalRingCardinality/DataSpaces.lean`, `CMData`, `CMData.sig`;
`src/Formalism/LocalRingCardinality/SpanPowerMembership/`
`ExampleLayerExistsGenerators.lean`, `unram_at`, `cmData`;
`src/Formalism/SatakeDualWeyl/Statement.lean`, `sigR`, `inclE`.
The original mass statements, example layer and placeholder record choices
are not needed for these constructions. The source archive/mirror states
no license; attribution is retained without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

open NumberField
open scoped TensorProduct

namespace RHLean.Geometry.NativePrescribedHermitian

/-- The complete source predicate, including integral separation at every
maximal ideal rather than only the abstract field involution. -/
def IsCMUnram (E : Type*) [Field E] [NumberField E] [StarRing E] : Prop :=
  IsTotallyComplex E ∧
    (∀ (τ : E →+* ℂ) (x : E), τ (star x) = starRingEnd ℂ (τ x)) ∧
    ∀ P : Ideal (𝓞 E), P.IsMaximal →
      ∃ θ t : 𝓞 E, algebraMap (𝓞 E) E t =
        star (algebraMap (𝓞 E) E θ) ∧ θ - t ∉ P

/-- The full original `DataSpaces.CMData`, with no field removed. -/
structure CMData (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] : Prop where
  cmUnram : IsCMUnram E
  totReal : IsTotallyReal F
  deg2 : Module.finrank F E = 2
  fixed : ∀ x : E, star x = x ↔ x ∈ (algebraMap F E).range

/-- The same involution, now linear over the proved fixed field. -/
def CMData.sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : CMData F E) : E →ₐ[F] E :=
  { starRingEnd E with
    commutes' := fun x => (hc.fixed (algebraMap F E x)).2 ⟨x, rfl⟩ }

namespace Signature

/-- Literal source scalar extension of the field involution. -/
def sigR {F E : Type} [Field F] [CommRing E] [Algebra F E]
    (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] :
    E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

/-- The original inclusion of the CM field into the tensor algebra. -/
def inclE {F E : Type} [Field F] [CommRing E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

end Signature

end RHLean.Geometry.NativePrescribedHermitian

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry.NativePrescribedHermitian

variable {φ : Frame} (H : HostAx φ)

/-- The actual all-prime unramifiedness theorem supplies the original
integral pair at each maximal ideal, with its required subtraction sign. -/
theorem unram_at (P : Ideal (𝓞 H.E)) (hP : P.IsMaximal) :
    ∃ θ t : 𝓞 H.E, algebraMap (𝓞 H.E) H.E t =
      H.conj (algebraMap (𝓞 H.E) H.E θ) ∧ θ - t ∉ P := by
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP
    (RingOfIntegers.not_isField H.E)
  have h := H.der.unramEF P hP.isPrime hP0
  push Not at h
  obtain ⟨θ, hθ⟩ := h
  refine ⟨θ, H.conj • θ, rfl, fun hmem => hθ ?_⟩
  rw [← neg_sub]
  exact P.neg_mem hmem

/-- The source's full CM/unramified predicate for the same host involution. -/
theorem isCMUnram :
    @IsCMUnram H.E _ _ (conjugationStar H.toHostRaw) := by
  have : IsCMField H.E := H.der.cm
  exact ⟨inferInstance, fun τ x => H.conjE_apply τ x, unram_at H⟩

/-- All fields of the original CM datum, supplied from the actual host. -/
theorem cmData :
    @CMData H.F H.E _ _ _ _ (conjugationStar H.toHostRaw) _ := by
  have : IsCMField H.E := H.der.cm
  letI : StarRing H.E := conjugationStar H.toHostRaw
  refine
    { cmUnram := isCMUnram H
      totReal := inferInstance
      deg2 := Algebra.IsQuadraticExtension.finrank_eq_two H.F H.E
      fixed := ?_ }
  intro x
  change H.conj x = x ↔ x ∈ (algebraMap H.F H.E).range
  rw [← H.der.mem_F x]
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩

theorem cmData_sig_apply (x : H.E) :
    @CMData.sig H.F H.E _ _ _ _ (conjugationStar H.toHostRaw) _ (cmData H) x =
      H.conj x := rfl

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

namespace RHLean.Analysis.AlpogeThin

open Formalism.FrobeniusOrbits
open RHLean.Geometry.NativePrescribedHermitian
open RHLean.Geometry NativeRawHostPolarization

variable (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]

local notation "E" => alpogeNativeHostField e q d
local notation "F" => maximalRealSubfield E
local notation "Af" => IsDedekindDomain.FiniteAdeleRing (𝓞 F) F

/-- The native endpoint assumes only the original host prime conditions
and exponent bound; every field of CMData is constructed on the SAME field. -/
theorem nativeDyadicHostCMData (he : 2 ≤ e) (hH : HostHyp q d) :
    @CMData F E _ _ _ _
      (conjugationStar (nativeDyadicHostRaw e q d he hH)) _ :=
  cmData (nativeDyadicHostAx e q d he hH)

/-- The record induces exactly the field involution used by the actual
finite-adelic norm construction. -/
theorem nativeDyadicHostCMData_sig (he : 2 ≤ e) (hH : HostHyp q d) :
    @CMData.sig F E _ _ _ _ (conjugationStar (nativeDyadicHostRaw e q d he hH)) _
        (nativeDyadicHostCMData e q d he hH) =
      NativeDyadicAdelicNorm.conjugation e q d he hH := by
  ext x
  change (nativeDyadicHostRaw e q d he hH).conj x =
    NativeDyadicAdelicNorm.conjugation e q d he hH x
  exact (NativeDyadicAdelicNorm.conjugation_eq_host e q d he hH x).symm

/-- Hence the original CMData tensor involution in the Spaces Gram field
is the one in the already constructed diagonal finite-adelic isometry. -/
theorem nativeDyadicHostCMData_sigR (he : 2 ≤ e) (hH : HostHyp q d) :
    Signature.sigR
        (@CMData.sig F E _ _ _ _ (conjugationStar (nativeDyadicHostRaw e q d he hH)) _
          (nativeDyadicHostCMData e q d he hH)) Af =
      NativeDyadicAdelicNorm.tensorConjugation e q d he hH := by
  rw [nativeDyadicHostCMData_sig]
  rfl

end RHLean.Analysis.AlpogeThin

end
