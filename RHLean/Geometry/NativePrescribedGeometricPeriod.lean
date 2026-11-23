import RHLean.Geometry.NativeGeometricPeriods
import RHLean.Geometry.NativePeriodTypeCoordinates
import RHLean.Geometry.NativePrescribedGeometricDatum

/-!
# Actual period data for the same constructed geometric Datum

The original inverse-half-different lattice is mapped by its proved real
realization, conjugation of exactly the negative coordinates, and one finite
enumeration. This gives the exact prescribed coefficient type and converts
the previously constructed J to ordinary multiplication by i. Its range is
proved injective, discrete and spanning over R, and a positive Hermitian
matrix is constructed whose imaginary part is the SAME source-normalized EF.

The final native theorem chooses one actual half-different before all ranks
and signatures. Every host/root/type/conjugation compatibility is supplied
by the same native field. No period, positivity, diagonalization, discrete
range, Moduli, SAB or theta-section premise is added. This closes the period
input only; the separate analytic/algebraic uniformization and level/moduli
suppliers are not asserted here.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/ToricGeometry/
ExistsEquivOfSumEq.lean, exists_diag_real and exists_isPeriod;
src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/
ToroidalCompactification/IsHolPeriods.lean, IsTypeFn and IsPeriod.
The source mirror states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical TensorProduct Pointwise ComplexConjugate

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry
open NativePrescribedHermitian NativeGeometricPeriods

namespace NativeRawHostPolarization

attribute [local instance] conjugationStar

variable {φ : Frame} (H : HostRaw φ)

/-- The actual real coordinates in which the constructed J is multiplication by i. -/
def twistedPeriodRealEquiv (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N q : ℕ) :
    (ℝ ⊗[ℤ] twistedLattice H B N) ≃ₗ[ℝ]
      (Fin ((cmTypeFinset H).card * N) → ℂ) :=
  (twistedRealEquiv H B hB N).trans
    (NativePeriodCoordinates.coordinates (cmTypeFinset H) N q)

theorem twistedPeriodRealEquiv_tmul (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N q : ℕ)
    (a : ℝ) (x : twistedLattice H B N) :
    twistedPeriodRealEquiv H B hB N q (a ⊗ₜ x) =
      NativePeriodCoordinates.coordinates (cmTypeFinset H) N q
        (fun (τ : cmTypeFinset H) i => (a : ℂ) * (τ : H.E →+* ℂ) (x.1 i)) := by
  change NativePeriodCoordinates.coordinates (cmTypeFinset H) N q
    (twistedRealCoordinates H B N (a ⊗ₜ x)) = _
  rw [twistedRealCoordinates_tmul]

theorem twistedPeriodRealEquiv_complexStructure (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N q : ℕ)
    (x : ℝ ⊗[ℤ] twistedLattice H B N) :
    twistedPeriodRealEquiv H B hB N q
        (twistedComplexStructure H B hB (negTail N q) x) =
      Complex.I • twistedPeriodRealEquiv H B hB N q x := by
  change NativePeriodCoordinates.coordinates (cmTypeFinset H) N q
    (twistedRealCoordinates H B N
      (twistedComplexStructure H B hB (negTail N q) x)) = _
  rw [twistedRealCoordinates_complexStructure]
  exact NativePeriodCoordinates.coordinates_diagonalJ (cmTypeFinset H) N q _

/-- The canonical period map of the SAME prescribed lattice. -/
def prescribedPeriodMap (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (k m j : ℕ) :
    prescribedLattice H B k m →+ (Fin ((cmTypeFinset H).card * (k + m - 1)) → ℂ) :=
  periodOfRealEquiv (twistedPeriodRealEquiv H B hB (k + m - 1) (m - j))

/-- Positive rows retain the actual CM embedding, negative rows its conjugate. -/
def prescribedPeriodType (k m j : ℕ) :
    Fin ((cmTypeFinset H).card * (k + m - 1)) → (H.E →+* ℂ) :=
  NativePeriodCoordinates.typeFn (cmTypeFinset H) (k + m - 1) (m - j)

theorem prescribedPeriodMap_apply (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (k m j : ℕ)
    (x : prescribedLattice H B k m) :
    prescribedPeriodMap H B hB k m j x =
      NativePeriodCoordinates.coordinates (cmTypeFinset H) (k + m - 1) (m - j)
        (fun (τ : cmTypeFinset H) i => (τ : H.E →+* ℂ) (x.1 i)) := by
  rw [prescribedPeriodMap, periodOfRealEquiv_apply, twistedPeriodRealEquiv_tmul]
  simp only [Complex.ofReal_one, one_mul]

theorem prescribedPeriodMap_smul (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (k m j : ℕ)
    (a : 𝓞 H.E) (x : prescribedLattice H B k m)
    (s : Fin ((cmTypeFinset H).card * (k + m - 1))) :
    prescribedPeriodMap H B hB k m j (a • x) s =
      prescribedPeriodType H k m j s (a : H.E) *
        prescribedPeriodMap H B hB k m j x s := by
  rw [prescribedPeriodMap_apply, prescribedPeriodMap_apply]
  change NativePeriodCoordinates.coordinates (cmTypeFinset H) (k + m - 1) (m - j)
      (fun (τ : cmTypeFinset H) i => (τ : H.E →+* ℂ) ((a : H.E) * x.1 i)) s = _
  simp only [map_mul]
  exact NativePeriodCoordinates.coordinates_mul (cmTypeFinset H)
    (k + m - 1) (m - j) (a : H.E) _ s

section GeometricHost

variable [IsCMField H.E]

/-- The exact original root filter gives the claimed multiplicities in the
same finite enumeration as the actual period coordinates. -/
theorem prescribedPeriodType_isTypeFn (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    IsTypeFn G (k + j - 1) (m - j) (prescribedPeriodType H k m j) := by
  intro τ
  have hf : τ ∈ cmTypeFinset H ↔ τ (G.rt : H.E) = G.rt0 :=
    (mem_cmTypeFinset H τ).trans (hΨ τ).symm
  constructor
  · intro ht
    change Nat.card {i // NativePeriodCoordinates.typeFn (cmTypeFinset H)
      (k + m - 1) (m - j) i = τ} = _
    rw [NativePeriodCoordinates.typeFn_card_of_mem (cmTypeFinset H)
      (cmTypeFinset_conjugate H) (k + m - 1) (m - j) τ (hf.mpr ht)]
    omega
  · intro ht
    exact NativePeriodCoordinates.typeFn_card_of_not_mem (cmTypeFinset H)
      (cmTypeFinset_conjugate H) (k + m - 1) (m - j) (by omega) τ
      (fun h => ht (hf.mp h))

/-- Full original IsPeriod on the actual complete Datum. Discreteness,
spanning, injectivity and the positive Hermitian matrix are proved here. -/
theorem prescribedPeriod_isPeriod (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    IsPeriod (prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj)
      (prescribedPeriodType H k m j) (prescribedPeriodMap H B hB k m j) := by
  let : Module.Free ℤ
      (prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj).La :=
    twistedLattice_free_int H B (k + m - 1)
  let : Module.Finite ℤ
      (prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj).La :=
    twistedLattice_finite_int H B (k + m - 1)
  refine periodOfRealEquiv_isPeriod
    (prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj)
    (prescribedPeriodType H k m j)
    (twistedPeriodRealEquiv H B hB (k + m - 1) (m - j))
    (twistedComplexStructure H B hB (negTail (k + m - 1) (m - j)))
    (twistedPeriodRealEquiv_complexStructure H B hB (k + m - 1) (m - j))
    ?_ ?_ ?_
  · rw [prescribedGeometricDatum_form]
    exact twistedComplexStructure_isometry H B hB hconj _
  · rw [prescribedGeometricDatum_form]
    exact twistedComplexStructure_pos H B hB hconj _
  · exact prescribedPeriodMap_smul H B hB k m j

end GeometricHost
end NativeRawHostPolarization

open NativeRawHostPolarization

/-- Actual coefficient type and full period predicate for the constructed
native Datum, with no compatibility or period premise left to supply. -/
theorem nativeDyadicPrescribedGeometricDatum_isPeriod
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    IsTypeFn G D.p D.q (prescribedPeriodType H.toHostRaw k m j) ∧
      IsPeriod D (prescribedPeriodType H.toHostRaw k m j)
        (prescribedPeriodMap H.toHostRaw B hB k m j) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  constructor
  · exact prescribedPeriodType_isTypeFn H.toHostRaw
      (nativeDyadicGeometricHostOfDerived e q d he hH)
      (nativeDyadicGeometricHostOfDerived_inPsi e q d he hH) k m j hk hj
  · exact prescribedPeriod_isPeriod H.toHostRaw B hB
      (nativeDyadicGeometricHostOfDerived e q d he hH)
      (nativeDyadicGeometricHostOfDerived_inPsi e q d he hH)
      (nativeDyadicHostRaw_prescribed_embedding_conj e q d he hH)
      (nativeDyadicGeometricHost_bar_eq e q d he hH) k m j hk hj

/-- One actual half-different supplies actual periods for every prescribed
rank and signature on the SAME full geometric host and literal lattice. -/
theorem nativeDyadicHost_exists_prescribedPeriods
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ k m : ℕ, ∀ hk : m + 3 ≤ k, ∀ j : ℕ, 1 ≤ j → ∀ hj : j ≤ m,
        let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
        IsTypeFn G D.p D.q (prescribedPeriodType H.toHostRaw k m j) ∧
          IsPeriod D (prescribedPeriodType H.toHostRaw k m j)
            (prescribedPeriodMap H.toHostRaw B hB k m j) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_⟩
  intro k m hk j _ hj
  exact nativeDyadicPrescribedGeometricDatum_isPeriod e q d he hH B hB k m j hk hj

end RHLean.Analysis.AlpogeThin

end
