import RHLean.Geometry.NativeGeometricDatum
import RHLean.Geometry.NativePrescribedPolarizationDomain
import RHLean.Geometry.NativeDerivedGeometricHost

/-!
# The full geometric Datum on the same prescribed native lattice

The literal root filter of the constructed geometric host is identified with
the raw host CM type. The original rational trace form is integral on the
same inverse-half-different lattice. Its source intForm equals the already
constructed perfect alternating integer form, and the source sgnW selection
is proved to be +1 from the actual positive complex structure. Every field
of the original Geo.Tor.Datum is then supplied, including adjointness with
the geometric host's own integral involution and both real trace identities.

The normalization is exactly the original host constructor's ccK = top:
xi0 = -1/sqrt(-d), AA = B^-1. The same B is used for every prescribed rank
and signature. This constructs the lattice Datum, not the source's larger
D7 record, auxiliary prime, levels, semiabelian schemes, or theta sections.

Mathematical source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Formalism/LocalToGlobal/ProjectiveLattices/
HalfOneAddSqrtNegIsIntegral.lean, efQ, DatInt, DomFor, sgnW, efW, datumOf;
DatumOfRecordSignature.lean, datumOfRecord; DatProofs.lean, datDom_holds;
src/Formalism/LocalRingCardinality/DataHost.lean, xi0, ccE, AA0, AA;
src/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsHost.lean,
exists_host_of_injective. The source mirror states no license; attribution
is preserved without assigning one. No source compiled artifact is imported.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField ComplexConjugate
open scoped BigOperators Classical TensorProduct Pointwise nonZeroDivisors

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry

namespace NativeRawHostPolarization

attribute [local instance] conjugationStar

variable {φ : Frame} (H : HostRaw φ)

/-- The source imaginary generator at its actually constructed ccK = top. -/
theorem xi_eq_source_top :
    xi H = -1 / ((Ideal.absNorm (⊤ : Ideal (𝓞 H.K)) : H.E) * H.sqd) := by
  simp only [Ideal.absNorm_top, Nat.cast_one, one_mul, xi]

/-- The source AA at ccK = top is the same coefficient inverse ideal. -/
theorem coefficientIdeal_eq_source_top (B : Ideal (𝓞 H.E)) :
    coefficientIdeal H B =
      (((⊤ : Ideal (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) :
          Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) *
        (B : FractionalIdeal (𝓞 H.E)⁰ H.E)⁻¹ := by
  rw [Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]

/-- The literal original efQ formula, before choosing an integer lift. -/
def prescribedRationalTraceForm (B : Ideal (𝓞 H.E)) (k m j : ℕ) :
    prescribedLattice H B k m →ₗ[ℤ] prescribedLattice H B k m →ₗ[ℤ] ℚ :=
  LinearMap.mk₂ ℤ
    (fun x y => Algebra.trace ℚ H.E (xi H * (prescribedSpace H k m j).hT x y))
    (fun x x' y => by simp [map_add, mul_add])
    (fun c x y => by
      simp [map_zsmul]
      rw [mul_left_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul])
    (fun x y y' => by simp [map_add, mul_add])
    (fun c x y => by
      simp [map_zsmul]
      rw [mul_left_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul])

theorem prescribedRationalTraceForm_apply (B : Ideal (𝓞 H.E)) (k m j : ℕ)
    (x y : prescribedLattice H B k m) :
    prescribedRationalTraceForm H B k m j x y =
      Algebra.trace ℚ H.E (xi H * (prescribedSpace H k m j).hT x y) := rfl

/-- Actual integrality follows from the previously constructed integer form. -/
theorem prescribedRationalTraceForm_integral (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (k m j : ℕ) :
    ∀ x y, ∃ n : ℤ, prescribedRationalTraceForm H B k m j x y = n := by
  intro x y
  exact ⟨prescribedTraceForm H B hB k m j x y,
    (prescribedTraceForm_cast H B hB k m j x y).symm⟩

/-- Every source choice of integer lift equals the same native perfect form. -/
theorem prescribedIntForm_eq (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (k m j : ℕ)
    (hI : ∀ x y, ∃ n : ℤ, prescribedRationalTraceForm H B k m j x y = n) :
    NativePolarizationIntegralForm.intForm (prescribedRationalTraceForm H B k m j) hI =
      prescribedTraceForm H B hB k m j :=
  NativePolarizationIntegralForm.intForm_eq_of_cast _ hI _
    (prescribedTraceForm_cast H B hB k m j)

section GeometricHost

variable [IsCMField H.E]

/-- The literal host-root filter, retaining its exact chosen complex root. -/
theorem prescribedGeometricHost_filter (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType) :
    Finset.univ.filter (fun τ : H.E →+* ℂ => τ (G.rt : H.E) = G.rt0) =
      cmTypeFinset H := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_cmTypeFinset]
  exact hΨ τ

/-- The proved real block satisfies the exact geometric host domain, with
its own root filter. No domain or positivity premise is introduced. -/
theorem prescribedGeometricDomain (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    NativeGeometricDomain G (prescribedLattice H B k m)
      (prescribedTraceForm H B hB k m j) (k + j - 1) (m - j) := by
  obtain ⟨hsq, hiso, hpos, hact⟩ :=
    prescribedComplexStructure_properties H B hB hconj k m j hk hj
  refine ⟨prescribedComplexStructure H B hB k m j, hsq, hiso, hpos, ?_⟩
  intro a A t hA ht
  apply hact a A t hA
  rw [prescribedGeometricHost_filter H G hΨ] at ht
  exact ht

/-- The source's sgnW selection on the SAME rational trace form and host. -/
def prescribedSign (G : NativeGeometricHost H.E)
    (B : Ideal (𝓞 H.E)) (k m j : ℕ) : ℤ :=
  if ∃ hI : ∀ x y, ∃ n : ℤ, prescribedRationalTraceForm H B k m j x y = n,
      NativeGeometricDomain G (prescribedLattice H B k m)
        (NativePolarizationIntegralForm.intForm (prescribedRationalTraceForm H B k m j) hI)
        (k + j - 1) (m - j)
  then 1 else -1

/-- The source's sign is +1, derived from the actual positive xi and J. -/
theorem prescribedSign_eq_one (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    prescribedSign H G B k m j = 1 := by
  have h : ∃ hI : ∀ x y, ∃ n : ℤ, prescribedRationalTraceForm H B k m j x y = n,
      NativeGeometricDomain G (prescribedLattice H B k m)
        (NativePolarizationIntegralForm.intForm (prescribedRationalTraceForm H B k m j) hI)
        (k + j - 1) (m - j) := by
    refine ⟨prescribedRationalTraceForm_integral H B hB k m j, ?_⟩
    rw [prescribedIntForm_eq H B hB]
    exact prescribedGeometricDomain H B hB G hΨ hconj k m j hk hj
  simp only [prescribedSign, ite_eq_left h]

/-- The original efW definition, including its sign-selection factor. -/
def prescribedSignedTraceForm (G : NativeGeometricHost H.E)
    (B : Ideal (𝓞 H.E)) (k m j : ℕ)
    (hI : ∀ x y, ∃ n : ℤ, prescribedRationalTraceForm H B k m j x y = n) :
    LinearMap.BilinForm ℤ (prescribedLattice H B k m) :=
  prescribedSign H G B k m j •
    NativePolarizationIntegralForm.intForm (prescribedRationalTraceForm H B k m j) hI

/-- The source's sign-selected form is exactly the constructed integer form. -/
theorem prescribedSignedTraceForm_eq (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m)
    (hI : ∀ x y, ∃ n : ℤ, prescribedRationalTraceForm H B k m j x y = n) :
    prescribedSignedTraceForm H G B k m j hI = prescribedTraceForm H B hB k m j := by
  unfold prescribedSignedTraceForm
  rw [prescribedSign_eq_one H B hB G hΨ hconj k m j hk hj, one_smul]
  exact prescribedIntForm_eq H B hB k m j hI

/-- Construct every original Datum field on the literal prescribed lattice.
The compatibility arguments identify already constructed objects; the native
endpoint below supplies them from the same actual host. -/
def prescribedGeometricDatum (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) : NativeGeometricDatum G := by
  let hI := prescribedRationalTraceForm_integral H B hB k m j
  have hEF : prescribedSignedTraceForm H G B k m j hI =
      prescribedTraceForm H B hB k m j :=
    prescribedSignedTraceForm_eq H B hB G hΨ hconj k m j hk hj hI
  exact
    { La := prescribedLattice H B k m
      fin := twistedLattice_finite H B (k + m - 1)
      proj := twistedLattice_projective H B (k + m - 1)
      EF := prescribedSignedTraceForm H G B k m j hI
      alt := by rw [hEF]; exact twistedTraceForm_alternating H B hB _
      unimod := by rw [hEF]; exact twistedTraceForm_bijective H B hB _
      adj := by
        rw [hEF]
        intro a x y
        rw [hbar a]
        exact twistedTraceForm_adjoint H B hB _ a x y
      p := k + j - 1
      q := m - j
      rank := by rw [twistedLattice_rank H B hB]; omega
      dom := by
        rw [hEF]
        exact prescribedGeometricDomain H B hB G hΨ hconj k m j hk hj }

/-- The datum retains the literal source lattice, without an unspecified
module equivalence or change of coefficient ideal. -/
theorem prescribedGeometricDatum_lattice (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    (prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj).La =
      prescribedLattice H B k m := rfl

theorem prescribedGeometricDatum_form (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (G : NativeGeometricHost H.E)
    (hΨ : ∀ τ : H.E →+* ℂ, G.InPsi τ ↔ τ ∈ H.cmType)
    (hconj : ∀ (τ : H.E →+* ℂ) (x : H.E), τ (H.conj x) = conj (τ x))
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    (prescribedGeometricDatum H B hB G hΨ hconj hbar k m j hk hj).EF =
      prescribedTraceForm H B hB k m j :=
  prescribedSignedTraceForm_eq H B hB G hΨ hconj k m j hk hj _

end GeometricHost
end NativeRawHostPolarization

open NativeRawHostPolarization

/-- The source root filter is the literal native arithmetic CM type. The
geometric rt0 is the chosen native embedding of the same square root. -/
theorem nativeDyadicGeometricHost_rootFilter
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    Finset.univ.filter (fun τ : H.E →+* ℂ => τ (G.rt : H.E) = G.rt0) =
      cmTypeFinset H.toHostRaw := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  exact prescribedGeometricHost_filter H.toHostRaw
    (nativeDyadicGeometricHostOfDerived e q d he hH)
    (nativeDyadicGeometricHostOfDerived_inPsi e q d he hH)

/-- Equality of the actual integral involutions, not only their field casts. -/
theorem nativeDyadicGeometricHost_bar_eq
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (a : 𝓞 (nativeDyadicHostAx e q d he hH).E) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    (nativeDyadicGeometricHostOfDerived e q d he hH).bar a = H.conj • a := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  apply Subtype.ext
  exact nativeDyadicGeometricHostOfDerived_bar e q d he hH a

/-- The exact original Datum, with every compatibility supplied by the
same fully derived native host and the given actual half-different. -/
def nativeDyadicPrescribedGeometricDatum
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    NativeGeometricDatum (nativeDyadicGeometricHostOfDerived e q d he hH) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  exact prescribedGeometricDatum H.toHostRaw B hB
    (nativeDyadicGeometricHostOfDerived e q d he hH)
    (nativeDyadicGeometricHostOfDerived_inPsi e q d he hH)
    (nativeDyadicHostRaw_prescribed_embedding_conj e q d he hH)
    (nativeDyadicGeometricHost_bar_eq e q d he hH) k m j hk hj

/-- The constructed record has the SAME literal lattice, integer trace
form, and original positive and negative signature multiplicities. -/
theorem nativeDyadicPrescribedGeometricDatum_spec
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    let H := nativeDyadicHostRaw e q d he hH
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    D.La = prescribedLattice H B k m ∧
      D.EF = prescribedTraceForm H B hB k m j ∧
      D.p = k + j - 1 ∧ D.q = m - j := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  refine ⟨rfl, ?_, rfl, rfl⟩
  exact prescribedGeometricDatum_form H.toHostRaw B hB
    (nativeDyadicGeometricHostOfDerived e q d he hH)
    (nativeDyadicGeometricHostOfDerived_inPsi e q d he hH)
    (nativeDyadicHostRaw_prescribed_embedding_conj e q d he hH)
    (nativeDyadicGeometricHost_bar_eq e q d he hH) k m j hk hj

/-- One actual half-different constructs the complete source Datum for
every prescribed rank and signature. No half-different, integral-form,
domain, positivity, rank, or host-compatibility premise remains here. -/
theorem nativeDyadicHost_exists_prescribedGeometricData
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ k m : ℕ, ∀ hk : m + 3 ≤ k, ∀ j : ℕ, 1 ≤ j → ∀ hj : j ≤ m,
        let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j
          hk hj
        D.La = prescribedLattice H B k m ∧
          D.EF = prescribedTraceForm H B hB k m j ∧
          D.p = k + j - 1 ∧ D.q = m - j := by
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_⟩
  intro k m hk j _ hj
  exact nativeDyadicPrescribedGeometricDatum_spec e q d he hH B hB k m j hk hj

end RHLean.Analysis.AlpogeThin

end
