import RHLean.Geometry.NativeIntegralSymplecticBasis
import RHLean.Geometry.NativePrescribedGeometricDatum

/-!
# Actual symplectic integral coordinates on the native polarization lattice

Every complete native geometric Datum has a symplectic integral basis for
its existing perfect alternating form. The argument derives the integer
rank and integer freeness from the original finite projective O(E)-module;
it does not assume an integral basis, a level, a period or a moduli object.

For the constructed dyadic host the basis is on the SAME literal
prescribedLattice and prescribedTraceForm. Its size is exactly twice
2*2^e*(k+m-1), using the proved degree [E:Q]=4*2^e. One actual
half-different is chosen before all prescribed ranks and signatures.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/
ExistsArBaseAway.lean, IsSympBasis; and
src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/
ExistsEquivStdSymp.lean, finrank_int_eq_mul, finrank_int_lattice,
exists_isSympBasis. The source mirror states no license; attribution is
preserved without assigning one. No terminal RH theorem or source
compiled artifact is imported or assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical BigOperators Pointwise

namespace RHLean.Geometry.NativeGeometricSymplectic

open NativeIntegralSymplectic

/-- The complete original standard-basis predicate, with its original sign. -/
def IsSympBasis {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : NativeGeometricHost E} (D : NativeGeometricDatum H) {g : ℕ}
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) : Prop :=
  ∀ i j, D.EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) = stdSymp g i j

theorem finrank_int_eq_mul (O M : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Module.finrank ℤ M = Module.finrank ℤ O * Module.finrank O M := by
  have : Module.Finite ℤ M := Module.Finite.trans O M
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := O) (M := M) le_rfl
  let F : Submodule O M := Submodule.span O (Set.range f)
  let bF : Module.Basis (Fin (Module.finrank O M)) O F := Module.Basis.span hf
  have : Module.Free O F := Module.Free.of_basis bF
  have h1 : Module.finrank O F = Module.finrank O M := by
    rw [Module.finrank_eq_card_basis bF, Fintype.card_fin]
  have h2 : Module.finrank O (M ⧸ F) = 0 := by
    have := Submodule.finrank_quotient_add_finrank F
    omega
  have h3 : Module.finrank ℤ (M ⧸ F.restrictScalars ℤ) = 0 := by
    rw [Module.finrank_eq_zero_iff] at h2 ⊢
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, ha, hax⟩ := h2 (Submodule.Quotient.mk x)
    obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ha)
    refine ⟨r, hr, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax ⊢
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul O r x, hc, mul_comm, mul_smul]
    exact F.smul_mem c hax
  have h4 := Submodule.finrank_quotient_add_finrank (F.restrictScalars ℤ)
  have h5 : Module.finrank ℤ (F.restrictScalars ℤ) = Module.finrank ℤ O * Module.finrank O F :=
    (Module.finrank_mul_finrank ℤ O F).symm
  rw [← h4, h3, zero_add, h5, h1]

theorem finrank_int_lattice {E : Type} [Field E] [NumberField E] [IsCMField E] {H : NativeGeometricHost E} (D : NativeGeometricDatum H) :
    Module.finrank ℤ D.La = 2 * (Module.finrank ℚ E / 2 * (D.p + D.q)) := by
  have := D.fin
  rw [finrank_int_eq_mul (𝓞 E) D.La, D.rank, RingOfIntegers.rank, IsTotallyComplex.finrank E,
    Nat.mul_div_cancel_left _ two_pos, Nat.mul_assoc]

theorem exists_isSympBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : NativeGeometricHost E) (D : NativeGeometricDatum H),
    ∃ bas : (Fin (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) → ℤ) ≃ₗ[ℤ] D.La, IsSympBasis D bas := by
  intro E _ _ _ H D
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := inferInstance
  exact exists_equiv_stdSymp D.alt D.unimod (finrank_int_lattice D)

end RHLean.Geometry.NativeGeometricSymplectic

namespace RHLean.Analysis.AlpogeThin

open RHLean.Geometry RHLean.Geometry.NativeIntegralSymplectic
open RHLean.Geometry.NativeGeometricSymplectic
open Formalism.HC Formalism.FrobeniusOrbits
open NativeRawHostPolarization

/-- Explicit symplectic coordinates on the SAME native inverse-ideal
lattice and its original signed trace form. No form or rank premise is added. -/
theorem nativeDyadicPrescribedTraceForm_exists_symplecticBasis
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ bas : (Fin (2 * (2 * 2 ^ e * (k + m - 1))) → ℤ) ≃ₗ[ℤ]
        prescribedLattice H B k m,
      ∀ i j', prescribedTraceForm H B hB k m j
        (bas (Pi.single i 1)) (bas (Pi.single j' 1)) =
          stdSymp (2 * 2 ^ e * (k + m - 1)) i j' := by
  let H := nativeDyadicHostRaw e q d he hH
  have := twistedLattice_free_int H B (k + m - 1)
  have := twistedLattice_finite_int H B (k + m - 1)
  have hrank : Module.finrank ℤ (prescribedLattice H B k m) =
      2 * (2 * 2 ^ e * (k + m - 1)) := by
    change Module.finrank ℤ (twistedLattice H B (k + m - 1)) = _
    rw [twistedLattice_rank_int H B hB, nativeDyadicHostRaw_finrank_E,
      nativeDyadicFrame_ord]
    ring
  exact exists_equiv_stdSymp
    (twistedTraceForm_alternating H B hB _)
    (twistedTraceForm_bijective H B hB _) hrank

/-- The literal source symplectic-basis condition on the already constructed
complete Datum; the underlying lattice and alternating form are unchanged. -/
theorem nativeDyadicPrescribedGeometricDatum_exists_symplecticBasis
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    ∃ bas : (Fin (2 * (Module.finrank ℚ H.E / 2 * (D.p + D.q))) → ℤ) ≃ₗ[ℤ] D.La,
      IsSympBasis D bas := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  exact exists_isSympBasis H.E (nativeDyadicGeometricHostOfDerived e q d he hH)
    (nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj)

/-- A single constructed half-different supplies the original symplectic
basis predicate for every prescribed native Datum, in the original witness order. -/
theorem nativeDyadicHost_exists_prescribedSymplecticBases
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ k m : ℕ, ∀ hk : m + 3 ≤ k, ∀ j : ℕ, 1 ≤ j → ∀ hj : j ≤ m,
        let H' := nativeDyadicHostAx e q d he hH
        let _ : IsCMField H'.E := H'.der.cm
        let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
        ∃ bas : (Fin (2 * (Module.finrank ℚ H.E / 2 * (D.p + D.q))) → ℤ) ≃ₗ[ℤ] D.La,
          IsSympBasis D bas := by
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_⟩
  intro k m hk j _ hj
  exact nativeDyadicPrescribedGeometricDatum_exists_symplecticBasis
    e q d he hH B hB k m j hk hj

end RHLean.Analysis.AlpogeThin

end
