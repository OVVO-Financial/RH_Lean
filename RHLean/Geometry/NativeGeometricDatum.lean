import RHLean.Geometry.NativeGeometricHost

/-!
# The original polarized integral-lattice datum

This reconstructs every field of Geo.Tor.Datum over the already constructed
native geometric host. The domain predicate is the literal source predicate:
the integral host root selects the complex embeddings; the positive form is
EF(J x,x); and the two real trace factors are 2 and -2. No domain, lattice,
rank or polarization witness is asserted by the record definition.

The source's integer lift of a rational bilinear form is also retained.
Its uniqueness lemma identifies that choice with an independently constructed
integer form having the same rational trace formula. The actual prescribed
native lattice is instantiated in NativePrescribedGeometricDatum.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/
ToroidalCompactification/TwoWeightEqOneAddRoot.lean, Geo.Tor.Datum;
src/Formalism/LocalToGlobal/ProjectiveLattices/
HalfOneAddSqrtNegIsIntegral.lean, choose_cast, intForm, intForm_cast, DomFor.
The source mirror states no license; attribution is preserved without
assigning one. No terminal RH theorem or source compiled artifact is imported.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped BigOperators TensorProduct Classical

namespace RHLean.Geometry

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/-- The literal real-domain condition from the original geometric Datum.
The abbreviation only shares its full type with the supplying theorem. -/
abbrev NativeGeometricDomain (H : NativeGeometricHost E)
    (La : Type) [AddCommGroup La] [Module (𝓞 E) La]
    (EF : LinearMap.BilinForm ℤ La) (p q : ℕ) : Prop :=
  ∃ J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    ∀ (a : 𝓞 E) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La) (t : ℂ),
      (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
      t = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
        ((p : ℂ) * τ (a : E) + (q : ℂ) * starRingEnd ℂ (τ (a : E))) →
      J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧
        LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im

/-- Every original Geo.Tor.Datum field, with its original type. The dom
abbreviation unfolds to the complete literal existential condition above. -/
structure NativeGeometricDatum (H : NativeGeometricHost E) where
  La : Type
  [acg : AddCommGroup La]
  [mod : Module (𝓞 E) La]
  fin : Module.Finite (𝓞 E) La
  proj : Module.Projective (𝓞 E) La
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  unimod : Function.Bijective EF
  adj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)
  p : ℕ
  q : ℕ
  rank : Module.finrank (𝓞 E) La = p + q
  dom : NativeGeometricDomain H La EF p q

attribute [instance] NativeGeometricDatum.acg NativeGeometricDatum.mod

namespace NativePolarizationIntegralForm

variable {M : Type} [AddCommGroup M]

theorem choose_cast (B : M →ₗ[ℤ] M →ₗ[ℤ] ℚ)
    (h : ∀ x y, ∃ n : ℤ, B x y = n) (x y : M) :
    (((h x y).choose : ℤ) : ℚ) = B x y :=
  (h x y).choose_spec.symm

/-- The exact integer lift used by the source's polarization datum. -/
def intForm (B : M →ₗ[ℤ] M →ₗ[ℤ] ℚ)
    (h : ∀ x y, ∃ n : ℤ, B x y = n) : LinearMap.BilinForm ℤ M :=
  LinearMap.mk₂ ℤ (fun x y => (h x y).choose)
    (fun x x' y => Int.cast_injective (α := ℚ) (by
      rw [Int.cast_add, choose_cast, choose_cast, choose_cast, map_add, LinearMap.add_apply]))
    (fun c x y => Int.cast_injective (α := ℚ) (by
      rw [smul_eq_mul, Int.cast_mul, choose_cast, choose_cast,
        LinearMap.map_smul₂, zsmul_eq_mul]))
    (fun x y y' => Int.cast_injective (α := ℚ) (by
      rw [Int.cast_add, choose_cast, choose_cast, choose_cast, map_add]))
    (fun c x y => Int.cast_injective (α := ℚ) (by
      rw [smul_eq_mul, Int.cast_mul, choose_cast, choose_cast, map_zsmul, zsmul_eq_mul]))

theorem intForm_cast (B : M →ₗ[ℤ] M →ₗ[ℤ] ℚ)
    (h : ∀ x y, ∃ n : ℤ, B x y = n) (x y : M) :
    ((intForm B h x y : ℤ) : ℚ) = B x y :=
  choose_cast B h x y

/-- The integral lift is the same actual integer form whenever its rational
formula agrees; there is no freedom to rescale or change its sign. -/
theorem intForm_eq_of_cast (B : M →ₗ[ℤ] M →ₗ[ℤ] ℚ)
    (h : ∀ x y, ∃ n : ℤ, B x y = n) (EF : LinearMap.BilinForm ℤ M)
    (hEF : ∀ x y, ((EF x y : ℤ) : ℚ) = B x y) : intForm B h = EF := by
  ext x y
  exact Int.cast_injective (α := ℚ)
    ((intForm_cast B h x y).trans (hEF x y).symm)

end NativePolarizationIntegralForm
end RHLean.Geometry

end
