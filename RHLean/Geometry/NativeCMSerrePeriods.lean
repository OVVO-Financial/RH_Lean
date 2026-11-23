import RHLean.Geometry.NativeCMSerreTensor
import RHLean.Geometry.NativePrescribedGeometricPeriod

/-!
# The actual analytic periods of the native Serre tensor

Every embedding in the original CM type has the same restriction to the
quadratic order. Complex base change of the literal inverse-half-different
module therefore maps to the original embedding coordinates. The already
constructed real realization proves surjectivity; the projective module's
exact rank proves injectivity. In particular, no independent identification
of a Serre tangent space with the prescribed period space is assumed.

Tensoring the actual elliptic quotient map gives a surjection whose kernel
is exactly the original integral module. Transport through the proved
complex equivalence identifies its quotient with the analytic Serre points.
These are analytic module statements; algebraization and the arithmetic
integral tangent generator are separate obligations.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsDiagonalCoordinates.lean`, `exists_lift` and `tensor_unif`, and
`ExistsHermFormCurve.lean`, `exists_isExp_of_isTen`. The native proof uses
the actual already constructed period coordinates and projectivity.
The source archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical TensorProduct Pointwise nonZeroDivisors

namespace RHLean.Geometry.NativeCM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/-- The same root-selected CM type has one and the same quadratic-order
embedding. This is derived from the actual integral generator. -/
theorem embed_eq_of_inPsi (G : NativeGeometricHost E) (τ σ : E →+* ℂ)
    (hτ : G.InPsi τ) (hσ : G.InPsi σ) : embed G τ = embed G σ := by
  have hw : embed G τ (wK G) = embed G σ (wK G) := by
    have ht := EllipticSeed.two_mul_omega G τ
    have hs := EllipticSeed.two_mul_omega G σ
    change τ (G.rt : E) = G.rt0 at hτ
    change σ (G.rt : E) = G.rt0 at hσ
    rw [hτ] at ht
    rw [hσ] at hs
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (ht.trans hs.symm)
  apply RingHom.ext
  intro a
  obtain ⟨⟨m, n⟩, ha, -⟩ := existsUnique_coord G a
  rw [ha]
  simp only [map_add, map_mul, map_intCast, hw]

namespace EllipticSeed

variable (G : NativeGeometricHost E) (τ : E →+* ℂ)
    [Algebra (OK G) ℂ] (hemb : algebraMap (OK G) ℂ = embed G τ)

/-- The actual elliptic quotient map, with its proved quadratic-order
linearity for the selected complex embedding. -/
def quotientLinear : ℂ →ₗ[OK G] Torus G τ :=
  { QuotientAddGroup.mk' (period G τ).range with
    map_smul' := by
      intro a z
      rw [Algebra.smul_def, hemb, torus_smul_mk] }

theorem quotientLinear_surjective : Function.Surjective (quotientLinear G τ hemb) :=
  QuotientAddGroup.mk'_surjective (period G τ).range

theorem quotientLinear_ker (z : ℂ) :
    quotientLinear G τ hemb z = 0 ↔ z ∈ Set.range (algebraMap (OK G) ℂ) := by
  change QuotientAddGroup.mk' (period G τ).range z = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  change (∃ a, embed G τ a = z) ↔ ∃ a, algebraMap (OK G) ℂ a = z
  rw [hemb]

variable (M : Type) [AddCommGroup M] [Module (OK G) M]

/-- The analytic Serre quotient map is literally the tensor of the
actual elliptic quotient, followed by tensor-factor commutation. -/
def serreExponential :
    ℂ ⊗[OK G] M →ₗ[OK G] M ⊗[OK G] Torus G τ :=
  (TensorProduct.comm (OK G) (Torus G τ) M).toLinearMap ∘ₗ
    (quotientLinear G τ hemb).rTensor M

theorem serreExponential_tmul (z : ℂ) (m : M) :
    serreExponential G τ hemb M (z ⊗ₜ[OK G] m) =
      m ⊗ₜ[OK G] QuotientAddGroup.mk' (period G τ).range z := by
  simp only [serreExponential, LinearMap.comp_apply, LinearMap.rTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.comm_tmul]
  rfl

theorem serreExponential_surjective :
    Function.Surjective (serreExponential G τ hemb M) :=
  (TensorProduct.comm (OK G) (Torus G τ) M).surjective.comp
    (LinearMap.rTensor_surjective M (quotientLinear_surjective G τ hemb))

/-- Right exactness supplies the integral period kernel; no freeness or
chosen basis of the coefficient module is substituted here. -/
theorem serreExponential_ker (t : ℂ ⊗[OK G] M) :
    serreExponential G τ hemb M t = 0 ↔ ∃ m : M, t = 1 ⊗ₜ[OK G] m := by
  constructor
  · intro ht
    change TensorProduct.comm (OK G) (Torus G τ) M
      ((quotientLinear G τ hemb).rTensor M t) = 0 at ht
    rw [LinearEquiv.map_eq_zero_iff] at ht
    obtain ⟨s, rfl⟩ := (rTensor_exact M (f := Algebra.linearMap (OK G) ℂ)
      (quotientLinear_ker G τ hemb) (quotientLinear_surjective G τ hemb) t).1 ht
    obtain ⟨m, rfl⟩ := (TensorProduct.lid (OK G) M).symm.surjective s
    exact ⟨m, by simp⟩
  · rintro ⟨m, rfl⟩
    have h1 : quotientLinear G τ hemb 1 = 0 :=
      (quotientLinear_ker G τ hemb 1).2 ⟨1, map_one _⟩
    change TensorProduct.comm (OK G) (Torus G τ) M
      ((quotientLinear G τ hemb).rTensor M (1 ⊗ₜ[OK G] m)) = 0
    rw [LinearMap.rTensor_tmul, h1, TensorProduct.zero_tmul, map_zero]

end EllipticSeed
end RHLean.Geometry.NativeCM

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM
open RHLean.Geometry.NativePolarizationRealCoordinates

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E) [Algebra (OK G) ℂ]
    (hcompat : ∀ τ : cmTypeFinset H,
      embed G (τ : H.E →+* ℂ) = algebraMap (OK G) ℂ)

/-- The original positive CM-type period coordinates on the complete
literal inverse-ideal lattice, now proved quadratic-order linear. -/
def purePeriodLinear (B : Ideal (𝓞 H.E)) (N : ℕ) :
    twistedLattice H B N →ₗ[OK G] (cmTypeFinset H → Fin N → ℂ) where
  toFun x τ i := (τ : H.E →+* ℂ) (x.1 i)
  map_add' x y := by
    ext τ i
    exact map_add (τ : H.E →+* ℂ) _ _
  map_smul' a x := by
    ext τ i
    change (τ : H.E →+* ℂ) (((a : 𝓞 H.E) : H.E) * x.1 i) =
      algebraMap (OK G) ℂ a * (τ : H.E →+* ℂ) (x.1 i)
    rw [map_mul]
    change embed G (τ : H.E →+* ℂ) a * _ = _
    rw [hcompat τ]

theorem purePeriodLinear_apply (B : Ideal (𝓞 H.E)) (N : ℕ)
    (x : twistedLattice H B N) (τ : cmTypeFinset H) (i : Fin N) :
    purePeriodLinear H G hcompat B N x τ i = (τ : H.E →+* ℂ) (x.1 i) := rfl

/-- Complex extension of the original period map along the actual order. -/
def pureSerrePeriod (B : Ideal (𝓞 H.E)) (N : ℕ) :
    ℂ ⊗[OK G] twistedLattice H B N →ₗ[ℂ] (cmTypeFinset H → Fin N → ℂ) :=
  LinearMap.liftBaseChange ℂ (purePeriodLinear H G hcompat B N)

theorem pureSerrePeriod_tmul (B : Ideal (𝓞 H.E)) (N : ℕ)
    (z : ℂ) (x : twistedLattice H B N) :
    pureSerrePeriod H G hcompat B N (z ⊗ₜ[OK G] x) =
      z • purePeriodLinear H G hcompat B N x := rfl

/-- Surjectivity comes from the already proved original real realization,
not from a separately assumed Serre period comparison. -/
theorem pureSerrePeriod_surjective (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ) :
    Function.Surjective (pureSerrePeriod H G hcompat B N) := by
  intro u
  obtain ⟨t, rfl⟩ := (twistedRealCoordinates_bijective H B hB N).2 u
  change twistedRealCoordinates H B N t ∈ (pureSerrePeriod H G hcompat B N).range
  induction t using TensorProduct.inductionOn with
  | add t u ht hu =>
    rw [map_add]
    exact Submodule.add_mem _ ht hu
  | tmul a x =>
    refine ⟨(a : ℂ) ⊗ₜ[OK G] x, ?_⟩
    rw [pureSerrePeriod_tmul, twistedRealCoordinates_tmul]
    rfl

/-- The projective restriction from O_E to the genuine quadratic order
retains every original coordinate. -/
theorem pureSerrePeriod_finrank (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ) :
    Module.finrank ℂ (ℂ ⊗[OK G] twistedLattice H B N) =
      (cmTypeFinset H).card * N := by
  obtain ⟨hfin, hproj, hrank⟩ :=
    (OK_isDedekindDomain_and_projective H.E G).2.2.2.2.2
      (twistedLattice H B N) (twistedLattice_finite H B N)
      (twistedLattice_projective H B N)
  have := hfin
  have := hproj
  rw [NativeThetaFullLevelCost.finrank_fibre, hrank, twistedLattice_rank H B hB N]
  have hcard : Module.finrank ℚ H.E / 2 = (cmTypeFinset H).card := by
    have htwo := two_card (cmTypeFinset_conjugate H)
    omega
  rw [hcard]

theorem pureSerrePeriod_bijective (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ) :
    Function.Bijective (pureSerrePeriod H G hcompat B N) := by
  obtain ⟨hfin, hproj, -⟩ :=
    (OK_isDedekindDomain_and_projective H.E G).2.2.2.2.2
      (twistedLattice H B N) (twistedLattice_finite H B N)
      (twistedLattice_projective H B N)
  have := hfin
  have := hproj
  have hdim : Module.finrank ℂ (ℂ ⊗[OK G] twistedLattice H B N) =
      Module.finrank ℂ (cmTypeFinset H → Fin N → ℂ) := by
    rw [pureSerrePeriod_finrank H G B hB N]
    simp
  have hsurj := pureSerrePeriod_surjective H G hcompat B hB N
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj,
    hsurj⟩

/-- The complex tangent-space identification is constructed from the
literal embedding coordinates on the same projective lattice. -/
def pureSerrePeriodEquiv (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ) :
    ℂ ⊗[OK G] twistedLattice H B N ≃ₗ[ℂ] (cmTypeFinset H → Fin N → ℂ) :=
  LinearEquiv.ofBijective (pureSerrePeriod H G hcompat B N)
    (pureSerrePeriod_bijective H G hcompat B hB N)

theorem pureSerrePeriodEquiv_tmul (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ)
    (z : ℂ) (x : twistedLattice H B N) :
    pureSerrePeriodEquiv H G hcompat B hB N (z ⊗ₜ[OK G] x) =
      z • purePeriodLinear H G hcompat B N x := rfl

/-- The resulting analytic exponential has values in the actual elliptic
seed tensor, without replacing the coefficient ideal by a free lattice. -/
def pureSerreExponential (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ)
    (τ₀ : cmTypeFinset H) :
    (cmTypeFinset H → Fin N → ℂ) →ₗ[OK G]
      twistedLattice H B N ⊗[OK G] EllipticSeed.Torus G (τ₀ : H.E →+* ℂ) :=
  EllipticSeed.serreExponential G (τ₀ : H.E →+* ℂ) (hcompat τ₀).symm
      (twistedLattice H B N) ∘ₗ
    (pureSerrePeriodEquiv H G hcompat B hB N).symm.toLinearMap.restrictScalars (OK G)

theorem pureSerreExponential_period_smul (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ)
    (τ₀ : cmTypeFinset H) (z : ℂ) (x : twistedLattice H B N) :
    pureSerreExponential H G hcompat B hB N τ₀
        (z • purePeriodLinear H G hcompat B N x) =
      x ⊗ₜ[OK G] QuotientAddGroup.mk'
        (EllipticSeed.period G (τ₀ : H.E →+* ℂ)).range z := by
  change EllipticSeed.serreExponential G _ _ _
    ((pureSerrePeriodEquiv H G hcompat B hB N).symm
      (z • purePeriodLinear H G hcompat B N x)) = _
  rw [← pureSerrePeriodEquiv_tmul H G hcompat B hB N z x,
    LinearEquiv.symm_apply_apply, EllipticSeed.serreExponential_tmul]

theorem pureSerreExponential_surjective (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ)
    (τ₀ : cmTypeFinset H) :
    Function.Surjective (pureSerreExponential H G hcompat B hB N τ₀) :=
  (EllipticSeed.serreExponential_surjective G (τ₀ : H.E →+* ℂ)
    (hcompat τ₀).symm (twistedLattice H B N)).comp
      (pureSerrePeriodEquiv H G hcompat B hB N).symm.surjective

/-- The period kernel is the original integral embedding image, exactly. -/
theorem pureSerreExponential_ker (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ)
    (τ₀ : cmTypeFinset H) (v : cmTypeFinset H → Fin N → ℂ) :
    pureSerreExponential H G hcompat B hB N τ₀ v = 0 ↔
      v ∈ (purePeriodLinear H G hcompat B N).range := by
  change EllipticSeed.serreExponential G _ _ _
    ((pureSerrePeriodEquiv H G hcompat B hB N).symm v) = 0 ↔ _
  rw [EllipticSeed.serreExponential_ker]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have he := congrArg (pureSerrePeriodEquiv H G hcompat B hB N) hx
    simpa only [LinearEquiv.apply_symm_apply, pureSerrePeriodEquiv_tmul,
      one_smul] using he.symm
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    apply (pureSerrePeriodEquiv H G hcompat B hB N).injective
    simp only [LinearEquiv.apply_symm_apply, pureSerrePeriodEquiv_tmul, one_smul]

/-- The quotient by the actual prescribed positive-type period image is
the actual Serre tensor point module. -/
def purePeriodQuotientEquiv (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ)
    (τ₀ : cmTypeFinset H) :
    ((cmTypeFinset H → Fin N → ℂ) ⧸ (purePeriodLinear H G hcompat B N).range)
      ≃ₗ[OK G] twistedLattice H B N ⊗[OK G]
        EllipticSeed.Torus G (τ₀ : H.E →+* ℂ) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext v
    exact (pureSerreExponential_ker H G hcompat B hB N τ₀ v).symm)).trans
      ((pureSerreExponential H G hcompat B hB N τ₀).quotKerEquivOfSurjective
        (pureSerreExponential_surjective H G hcompat B hB N τ₀))

/-- The pure-type source period map is exactly the same coordinate image,
with only the existing finite enumeration applied. -/
theorem purePeriodLinear_prescribed (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m : ℕ) (x : prescribedLattice H B k m) :
    prescribedPeriodMap H B hB k m m x =
      NativePeriodCoordinates.coordinates (cmTypeFinset H) (k + m - 1) 0
        (purePeriodLinear H G hcompat B (k + m - 1) x) := by
  rw [prescribedPeriodMap_apply, Nat.sub_self]
  rfl

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM
open NativeRawHostPolarization

/-- Native CM-type compatibility of the quadratic seed is proved from
the very same selected root and CM type. -/
theorem nativeDyadic_quadraticEmbeddings_eq
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    ∀ τ σ : cmTypeFinset H.toHostRaw,
      embed G (τ : H.E →+* ℂ) = embed G (σ : H.E →+* ℂ) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  intro τ σ
  apply embed_eq_of_inPsi G
  · exact (nativeDyadicGeometricHostOfDerived_inPsi e q d he hH τ).2
      ((mem_cmTypeFinset H.toHostRaw τ).1 τ.2)
  · exact (nativeDyadicGeometricHostOfDerived_inPsi e q d he hH σ).2
      ((mem_cmTypeFinset H.toHostRaw σ).1 σ.2)

/-- One constructed half-different supplies the exact analytic Serre
periods in every full original rank. The actual seed embedding, order
compatibility, complex dimension and quotient kernel are all discharged
here. The endpoint asserts no scheme or arithmetic degree comparison. -/
theorem nativeDyadicHost_exists_serrePeriods
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let G := nativeDyadicGeometricHostOfDerived e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (_hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ (N : ℕ) (τ₀ : cmTypeFinset H.toHostRaw),
        let _ : Algebra (OK G) ℂ := (embed G (τ₀ : H.E →+* ℂ)).toAlgebra
        ∃ P : twistedLattice H.toHostRaw B N →ₗ[OK G]
            (cmTypeFinset H.toHostRaw → Fin N → ℂ),
          ∃ F : ℂ ⊗[OK G] twistedLattice H.toHostRaw B N ≃ₗ[ℂ]
              (cmTypeFinset H.toHostRaw → Fin N → ℂ),
            ∃ ex : (cmTypeFinset H.toHostRaw → Fin N → ℂ) →ₗ[OK G]
                twistedLattice H.toHostRaw B N ⊗[OK G]
                  EllipticSeed.Torus G (τ₀ : H.E →+* ℂ),
              (∀ x τ i, P x τ i = (τ : H.E →+* ℂ) (x.1 i)) ∧
              (∀ z x, F (z ⊗ₜ[OK G] x) = z • P x) ∧
              (∀ z x, ex (z • P x) = x ⊗ₜ[OK G]
                QuotientAddGroup.mk' (EllipticSeed.period G (τ₀ : H.E →+* ℂ)).range z) ∧
              Function.Surjective ex ∧
              (∀ v, ex v = 0 ↔ v ∈ P.range) ∧
              Nonempty (((cmTypeFinset H.toHostRaw → Fin N → ℂ) ⧸ P.range)
                ≃ₗ[OK G] twistedLattice H.toHostRaw B N ⊗[OK G]
                  EllipticSeed.Torus G (τ₀ : H.E →+* ℂ)) ∧
              Module.finrank ℂ (ℂ ⊗[OK G] twistedLattice H.toHostRaw B N) =
                (2 * 2 ^ e) * N := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let G := nativeDyadicGeometricHostOfDerived e q d he hH
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_⟩
  intro N τ₀
  let _ : Algebra (OK G) ℂ := (embed G (τ₀ : H.E →+* ℂ)).toAlgebra
  have hcompat : ∀ τ : cmTypeFinset H.toHostRaw,
      embed G (τ : H.E →+* ℂ) = algebraMap (OK G) ℂ := by
    intro τ
    exact nativeDyadic_quadraticEmbeddings_eq e q d he hH τ τ₀
  refine ⟨purePeriodLinear H.toHostRaw G hcompat B N,
    pureSerrePeriodEquiv H.toHostRaw G hcompat B hB N,
    pureSerreExponential H.toHostRaw G hcompat B hB N τ₀,
    purePeriodLinear_apply H.toHostRaw G hcompat B N,
    pureSerrePeriodEquiv_tmul H.toHostRaw G hcompat B hB N,
    pureSerreExponential_period_smul H.toHostRaw G hcompat B hB N τ₀,
    pureSerreExponential_surjective H.toHostRaw G hcompat B hB N τ₀,
    pureSerreExponential_ker H.toHostRaw G hcompat B hB N τ₀,
    ⟨purePeriodQuotientEquiv H.toHostRaw G hcompat B hB N τ₀⟩, ?_⟩
  rw [pureSerrePeriod_finrank H.toHostRaw G B hB N]
  have hcard : (cmTypeFinset H.toHostRaw).card = 2 * 2 ^ e := by
    have htwo := NativePolarizationRealCoordinates.two_card
      (cmTypeFinset_conjugate H.toHostRaw)
    change 2 * (cmTypeFinset H.toHostRaw).card =
      Module.finrank ℚ (nativeDyadicHostRaw e q d he hH).E at htwo
    rw [nativeDyadicHostRaw_finrank_E, nativeDyadicFrame_ord] at htwo
    omega
  rw [hcard]

end RHLean.Analysis.AlpogeThin

end
