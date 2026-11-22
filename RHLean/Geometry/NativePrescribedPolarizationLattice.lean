import RHLean.Geometry.NativePrescribedHermitianSpaces
import RHLean.Geometry.NativePolarizationCoefficientLattice

/-!
# The actual coefficient-twisted lattice in the prescribed Hermitian space

For the source's diagonal W_j and its standard L0, the literal span of
products a*x with a in the same inverse half-different B^-1 is exactly the
coordinate lattice (B^-1)^(k+m-1). We prove this equality and construct its
perfect alternating integer form as the signed sum of the already proved
coefficient forms. Its rational value is exactly Tr(xi*hT(x,y)), with the
original negative tail, conjugation and xi. Finite projectivity, the full
integer and O(E) ranks, alternation and conjugate adjointness are conclusions.

The finite-adelic comparison with Y_0, and the real complex structure with
its positivity and two embedding-trace identities, are separate obligations.
No such isometry, complex structure or completed Datum is assumed here.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/LocalRingCardinality/SpanPowerMembership/`
`BaseFormAnisotropicOrthogonalSingle.lean`, `spacesOfRanks.W`;
`src/Formalism/LocalToGlobal/ProjectiveLattices/`
`HalfOneAddSqrtNegIsIntegral.lean`, `latW`, `efQ`, `efQ_alt`, `efQ_adj`,
`latW_fin`, `latW_proj`; `HostInt.lean`, `efQ_surj` and `efW_unimod_of`;
`HostRank.lean`, `latW_isLocalized`, `latW_finrank`, `latW_rank`.
This is the source's actual `ccK = top`, `AA = B^-1` choice already proved
on the native host. The direct coordinate proof specializes those generic
source constructions to the literal prescribed W_j, retaining its full rank.
The source archive/mirror states no license; attribution is retained without
assigning a new license to source-derived material.
-/

set_option autoImplicit false

noncomputable section

open NumberField
open scoped Pointwise nonZeroDivisors

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry.NativePrescribedHermitian

namespace NativeRawHostPolarization

variable {φ : Frame} (H : HostRaw φ)

/-- The involution is the same actual Galois conjugation used by the
coefficient form. -/
@[instance_reducible]
def conjugationStar : StarRing H.E where
  star := H.conj
  star_involutive := conj_conj H
  star_mul x y := by rw [map_mul, mul_comm]
  star_add := map_add H.conj

attribute [local instance] conjugationStar

/-- The source's literal span of products `AA * L0`, for the actual diagonal
space whose standard base lattice is `stdLat`. -/
def twistedLattice (B : Ideal (𝓞 H.E)) (N : ℕ) :
    Submodule (𝓞 H.E) (Fin N → H.E) :=
  Submodule.span (𝓞 H.E) {v | ∃ a : H.E, a ∈ coefficientIdeal H B ∧
    ∃ x ∈ stdLat N, v = a • x}

/-- The actual product span is the full coordinate inverse-ideal lattice;
this is an equality of the original submodules, not a new lattice choice. -/
theorem twistedLattice_eq_pi (B : Ideal (𝓞 H.E)) (N : ℕ) :
    twistedLattice H B N =
      Submodule.pi Set.univ fun _ : Fin N =>
        (coefficientIdeal H B : Submodule (𝓞 H.E) H.E) := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [Submodule.mem_pi]
    intro i _
    have hxi := (mem_stdLat_iff N x).mp hx i
    change a * x i ∈ coefficientIdeal H B
    simpa only [Algebra.smul_def, mul_comm] using
      (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).smul_mem
        (⟨x i, hxi⟩ : 𝓞 H.E) ha
  · intro v hv
    have hvi : ∀ i, v i ∈ coefficientIdeal H B := by
      simpa only [Submodule.mem_pi, Set.mem_univ, forall_const] using hv
    have he : v = ∑ i : Fin N, v i • (Pi.single i 1 : Fin N → H.E) := by
      ext j
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [he]
    refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨v i, hvi i, Pi.single i 1, ?_, rfl⟩
    apply (mem_stdLat_iff N _).mpr
    intro j
    by_cases h : j = i <;> simp [Pi.single_apply, h]

theorem mem_twistedLattice (B : Ideal (𝓞 H.E)) (N : ℕ) (x : Fin N → H.E) :
    x ∈ twistedLattice H B N ↔ ∀ i, x i ∈ coefficientIdeal H B := by
  rw [twistedLattice_eq_pi]
  simp only [Submodule.mem_pi, Set.mem_univ, forall_const]

/-- Coordinates identify the same source span with a finite product of the
same coefficient ideal. -/
def twistedCoordinates (B : Ideal (𝓞 H.E)) (N : ℕ) :
    twistedLattice H B N ≃ₗ[𝓞 H.E] (Fin N → coefficientIdeal H B) where
  toFun x i := ⟨x.1 i, (mem_twistedLattice H B N x.1).mp x.2 i⟩
  invFun x := ⟨fun i => x i, (mem_twistedLattice H B N _).mpr fun i => (x i).2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := funext fun _ => Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem twistedLattice_finite (B : Ideal (𝓞 H.E)) (N : ℕ) :
    Module.Finite (𝓞 H.E) (twistedLattice H B N) := by
  have := coefficientIdeal_finite_over_integers H B
  exact Module.Finite.equiv (twistedCoordinates H B N).symm

theorem twistedLattice_free_int (B : Ideal (𝓞 H.E)) (N : ℕ) :
    Module.Free ℤ (twistedLattice H B N) := by
  have := coefficientIdeal_free H B
  exact Module.Free.of_equiv ((twistedCoordinates H B N).restrictScalars ℤ).symm

theorem twistedLattice_finite_int (B : Ideal (𝓞 H.E)) (N : ℕ) :
    Module.Finite ℤ (twistedLattice H B N) := by
  have := coefficientIdeal_finite H B
  exact Module.Finite.equiv ((twistedCoordinates H B N).restrictScalars ℤ).symm

/-- Projectivity follows on the actual full lattice from finite generation
and torsion-freeness over the original Dedekind ring. -/
theorem twistedLattice_projective (B : Ideal (𝓞 H.E)) (N : ℕ) :
    Module.Projective (𝓞 H.E) (twistedLattice H B N) := by
  have := twistedLattice_finite H B N
  have : Module.Flat (𝓞 H.E) (twistedLattice H B N) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨⟨r, hr⟩, hrx⟩ := (Submodule.mem_torsion_iff x).mp hx
    have h0 : r • x = 0 := hrx
    have h1 : r • (x : Fin N → H.E) = 0 := by
      rw [← Submodule.coe_smul, h0]
      rfl
    rw [← algebraMap_smul H.E r (x : Fin N → H.E), smul_eq_zero] at h1
    rcases h1 with h | h
    · exact False.elim ((nonZeroDivisors.ne_zero hr)
        (IsFractionRing.injective _ H.E (h.trans (map_zero _).symm)))
    · exact (Submodule.mem_bot _).mpr (Subtype.ext h)
  have := Module.finitePresentation_of_finite (𝓞 H.E) (twistedLattice H B N)
  exact Module.Flat.projective_of_finitePresentation

/-- The finite product of actual fractional ideals spans the original
ambient E-space after localization; denominators are cleared simultaneously. -/
theorem twistedLattice_isLocalized (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ) :
    IsLocalizedModule (𝓞 H.E)⁰ (twistedLattice H B N).subtype where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hs0 : algebraMap (𝓞 H.E) H.E s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    have he (v : Fin N → H.E) :
        algebraMap (𝓞 H.E) (Module.End (𝓞 H.E) (Fin N → H.E)) s v =
          algebraMap (𝓞 H.E) H.E s • v := by
      rw [Module.algebraMap_end_apply, algebraMap_smul]
    constructor
    · intro v w h
      rw [he, he] at h
      exact smul_right_injective _ hs0 h
    · intro v
      refine ⟨(algebraMap (𝓞 H.E) H.E s)⁻¹ • v, ?_⟩
      rw [he, smul_smul, mul_inv_cancel₀ hs0, one_smul]
  surj y := by
    have := coefficientIdeal_isLocalized H B hB
    obtain ⟨s, hs⟩ := IsLocalizedModule.exist_integer_multiples_of_finite
      (𝓞 H.E)⁰ (coefficientIdeal H B : Submodule (𝓞 H.E) H.E).subtype y
    have hsy : (s : 𝓞 H.E) • y ∈ twistedLattice H B N := by
      apply (mem_twistedLattice H B N _).mpr
      intro i
      obtain ⟨a, ha⟩ := hs i
      change (s : 𝓞 H.E) • y i ∈ coefficientIdeal H B
      rw [← ha]
      exact a.2
    exact ⟨(⟨(s : 𝓞 H.E) • y, hsy⟩, s), rfl⟩
  exists_of_eq h := ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩

theorem twistedLattice_rank (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ) :
    Module.finrank (𝓞 H.E) (twistedLattice H B N) = N := by
  have := twistedLattice_isLocalized H B hB N
  calc
    _ = Module.finrank (𝓞 H.E) (Fin N → H.E) :=
      (IsLocalizedModule.finrank_eq (p := (𝓞 H.E)⁰)
        (f := (twistedLattice H B N).subtype) le_rfl).symm
    _ = Module.finrank H.E (Fin N → H.E) :=
      (IsFractionRing.finrank_right_eq (R := 𝓞 H.E) (S := H.E)
        (N := Fin N → H.E)).symm
    _ = N := Module.finrank_fin_fun H.E

theorem twistedLattice_rank_int (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (N : ℕ) :
    Module.finrank ℤ (twistedLattice H B N) = N * Module.finrank ℚ H.E := by
  calc
    _ = Module.finrank ℤ (Fin N → coefficientIdeal H B) :=
      ((twistedCoordinates H B N).restrictScalars ℤ).finrank_eq
    _ = N * Module.finrank ℚ H.E := by
      rw [Module.finrank_pi_fintype]
      simp only [coefficientIdeal_rank H B hB, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Multiplication by the literal diagonal signs is an integral involution. -/
def signedCoordinates {B : Ideal (𝓞 H.E)} {N : ℕ} (neg : Fin N → Bool) :
    (Fin N → coefficientIdeal H B) ≃ₗ[ℤ] (Fin N → coefficientIdeal H B) where
  toFun x i := (sgn (neg i) : ℤ) • x i
  invFun x i := (sgn (neg i) : ℤ) • x i
  left_inv x := funext fun i => by rw [smul_smul, sgn_mul_self, one_smul]
  right_inv x := funext fun i => by rw [smul_smul, sgn_mul_self, one_smul]
  map_add' x y := funext fun i => smul_add _ _ _
  map_smul' c x := funext fun i => by
    simp only [Pi.smul_apply, smul_smul]
    rw [mul_comm]

/-- The perfect coefficient form, coordinatewise, followed by the finite
product/dual equivalence. This constructs the full signed perfect form. -/
def coordinateTraceEquiv (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) :
    (Fin N → coefficientIdeal H B) ≃ₗ[ℤ]
      ((Fin N → coefficientIdeal H B) →ₗ[ℤ] ℤ) :=
  (signedCoordinates H (B := B) neg).trans
    ((LinearEquiv.piCongrRight fun _ : Fin N =>
      LinearEquiv.ofBijective (integralTraceForm H B hB)
        (integralTraceForm_bijective H B hB)).trans
      (LinearMap.lsum ℤ (fun _ : Fin N => coefficientIdeal H B) ℤ))

theorem coordinateTraceEquiv_apply (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) (x y : Fin N → coefficientIdeal H B) :
    coordinateTraceEquiv H B hB neg x y =
      ∑ i, (sgn (neg i) : ℤ) * integralTraceForm H B hB (x i) (y i) := by
  simp only [coordinateTraceEquiv, LinearEquiv.trans_apply,
    LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearEquiv.piCongrRight_apply,
    LinearEquiv.ofBijective_apply]
  change (∑ i, integralTraceForm H B hB ((sgn (neg i) : ℤ) • x i) (y i)) = _
  simp only [LinearMap.map_smul₂, smul_eq_mul]

/-- A duality equivalence on the literal source lattice, rather than only
on an isomorphic unspecified module. -/
def twistedTraceEquiv (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) :
    twistedLattice H B N ≃ₗ[ℤ] (twistedLattice H B N →ₗ[ℤ] ℤ) :=
  let c := (twistedCoordinates H B N).restrictScalars ℤ
  (c.trans (coordinateTraceEquiv H B hB neg)).trans c.dualMap

def twistedTraceForm (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) : LinearMap.BilinForm ℤ (twistedLattice H B N) :=
  (twistedTraceEquiv H B hB neg).toLinearMap

theorem twistedTraceForm_apply (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) (x y : twistedLattice H B N) :
    twistedTraceForm H B hB neg x y =
      ∑ i, (sgn (neg i) : ℤ) * integralTraceForm H B hB
        (twistedCoordinates H B N x i) (twistedCoordinates H B N y i) :=
  coordinateTraceEquiv_apply H B hB neg _ _

/-- The constructed integer form has exactly the original rational trace
formula and the same diagonal Hermitian form. -/
theorem twistedTraceForm_cast (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) (x y : twistedLattice H B N) :
    ((twistedTraceForm H B hB neg x y : ℤ) : ℚ) =
      Algebra.trace ℚ H.E (xi H * diagForm N neg
        (x : Fin N → H.E) (y : Fin N → H.E)) := by
  rw [twistedTraceForm_apply, Int.cast_sum, diagForm_apply, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_mul, integralTraceForm_cast]
  change ((sgn (neg i) : ℤ) : ℚ) *
      Algebra.trace ℚ H.E (xi H * H.conj (x.1 i) * y.1 i) =
    Algebra.trace ℚ H.E (xi H * (H.conj (x.1 i) * sgn (neg i) * y.1 i))
  cases h : neg i <;> simp [h, sgn, mul_assoc]

theorem twistedTraceForm_bijective (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) :
    Function.Bijective (twistedTraceForm H B hB neg) :=
  (twistedTraceEquiv H B hB neg).bijective

theorem twistedTraceForm_alternating (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) (x : twistedLattice H B N) :
    twistedTraceForm H B hB neg x x = 0 := by
  rw [twistedTraceForm_apply]
  exact Finset.sum_eq_zero fun _ _ => by
    rw [integralTraceForm_alternating, mul_zero]

theorem twistedTraceForm_adjoint (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    {N : ℕ} (neg : Fin N → Bool) (a : 𝓞 H.E)
    (x y : twistedLattice H B N) :
    twistedTraceForm H B hB neg (a • x) y =
      twistedTraceForm H B hB neg x ((H.conj • a) • y) := by
  rw [twistedTraceForm_apply, twistedTraceForm_apply]
  simp only [map_smul, Pi.smul_apply, integralTraceForm_adjoint]

/-- The prescribed source W_j, over the very same host field and actual
conjugation, with its original integral base lattice. -/
def prescribedSpace (k m j : ℕ) : HSpace H.E := W k m j

abbrev prescribedLattice (B : Ideal (𝓞 H.E)) (k m : ℕ) :=
  twistedLattice H B (k + m - 1)

/-- The constructed lattice is exactly the source product span with the
prescribed W_j and its own L0. -/
theorem prescribedLattice_eq_source (B : Ideal (𝓞 H.E)) (k m j : ℕ) :
    prescribedLattice H B k m =
      Submodule.span (𝓞 H.E) {v | ∃ a : H.E, a ∈ coefficientIdeal H B ∧
        ∃ x ∈ (prescribedSpace H k m j).L0, v = a • x} := rfl

def prescribedTraceForm (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (k m j : ℕ) :
    LinearMap.BilinForm ℤ (prescribedLattice H B k m) :=
  twistedTraceForm H B hB (negTail (k + m - 1) (m - j))

theorem prescribedTraceForm_cast (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (x y : prescribedLattice H B k m) :
    ((prescribedTraceForm H B hB k m j x y : ℤ) : ℚ) =
      Algebra.trace ℚ H.E (xi H * (prescribedSpace H k m j).hT
        (x : Fin (k + m - 1) → H.E) (y : Fin (k + m - 1) → H.E)) :=
  twistedTraceForm_cast H B hB _ x y

end NativeRawHostPolarization

open NativeRawHostPolarization

attribute [local instance] NativeRawHostPolarization.conjugationStar

/-- On the constructed native host, the involution in the prescribed form
is precisely the canonical CM involution. -/
theorem nativeDyadicHostRaw_prescribed_conj
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostRaw e q d he hH
    let _ : IsCMField H.E := nativeDyadicHostRaw_cm e q d he hH
    ∀ x : H.E, H.conj x = IsCMField.complexConj H.E x := by
  dsimp only
  let _ : IsCMField (nativeDyadicHostRaw e q d he hH).E :=
    nativeDyadicHostRaw_cm e q d he hH
  intro x
  rw [nativeDyadicHostRaw_conj]
  exact (RHLean.Analysis.alpogeNativeHostConj_complexConj e q d x).symm

/-- One actually constructed half-different supplies all prescribed full-rank
lattices and their exact signed perfect trace forms. Finite-adelic isometry
and the real `DomFor` complex structure are not part of this conclusion. -/
theorem nativeDyadicHostRaw_exists_prescribedPolarizationLattices
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) (k m : ℕ) (hk : m + 3 ≤ k) :
    let H := nativeDyadicHostRaw e q d he hH
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      Module.Finite (𝓞 H.E) (prescribedLattice H B k m) ∧
      Module.Projective (𝓞 H.E) (prescribedLattice H B k m) ∧
      Module.Free ℤ (prescribedLattice H B k m) ∧
      Module.Finite ℤ (prescribedLattice H B k m) ∧
      Module.finrank (𝓞 H.E) (prescribedLattice H B k m) = k + m - 1 ∧
      Module.finrank ℤ (prescribedLattice H B k m) = (k + m - 1) * (4 * 2 ^ e) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ m →
        (∀ τ : H.E →+* ℂ, Signature.HasSignature
          ((prescribedSpace H k m j).gram.map τ) (k + j - 1) (m - j)) ∧
        Function.Bijective (prescribedTraceForm H B hB k m j) ∧
        (∀ x, prescribedTraceForm H B hB k m j x x = 0) ∧
        (∀ (a : 𝓞 H.E) x y,
          prescribedTraceForm H B hB k m j (a • x) y =
            prescribedTraceForm H B hB k m j x ((H.conj • a) • y)) ∧
        (∀ x y,
          ((prescribedTraceForm H B hB k m j x y : ℤ) : ℚ) =
            Algebra.trace ℚ H.E (xi H * (prescribedSpace H k m j).hT
              (x : Fin (k + m - 1) → H.E) (y : Fin (k + m - 1) → H.E))) := by
  let H := nativeDyadicHostRaw e q d he hH
  obtain ⟨B, hB, hcop, hinv⟩ := nativeDyadicHostRaw_principal e q d he hH
  refine ⟨B, hB, hcop, hinv,
    twistedLattice_finite H B (k + m - 1),
    twistedLattice_projective H B (k + m - 1),
    twistedLattice_free_int H B (k + m - 1),
    twistedLattice_finite_int H B (k + m - 1),
    twistedLattice_rank H B hB (k + m - 1), ?_, ?_⟩
  · change Module.finrank ℤ (twistedLattice H B (k + m - 1)) = _
    rw [twistedLattice_rank_int H B hB, nativeDyadicHostRaw_finrank_E,
      nativeDyadicFrame_ord]
  · intro j _ hj
    exact ⟨W_hasSignature k m j hk hj,
      twistedTraceForm_bijective H B hB _,
      twistedTraceForm_alternating H B hB _,
      twistedTraceForm_adjoint H B hB _,
      prescribedTraceForm_cast H B hB k m j⟩

end RHLean.Analysis.AlpogeThin

end
