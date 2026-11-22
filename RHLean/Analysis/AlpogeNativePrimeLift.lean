import RHLean.Analysis.AlpogeNativeCyclotomicHost

/-!
# Genuine prime-ideal lifting for the native cyclotomic host

Inertia is defined here by the action on the actual ring of integers modulo
an actual prime ideal. Its lift through a number-field tower is constructed
using transitivity on the primes above a prime and surjectivity onto the
residue-field automorphisms. No identification with an abstract finite
inertia subgroup is assumed.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`
`InertiaGaloisSymmetry/CycLift.lean`, declarations
`Der.{res_smul,mem_over_iff,inertia_res,frob_res,inertia_lift,exists_over,`
`frob_iff_inertia}`, and
`src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean`,
`Decomp.mem_stab_of`. The native specialization retains the original fixed
field and the same cyclotomic modulus. The source archive/mirror states no
license; this notice preserves attribution without assigning a new license
to source-derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Ideal
open scoped Pointwise

namespace RHLean.Analysis.NativePrimeLift

section Tower

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra E L] [IsScalarTower ℚ E L]

omit [IsScalarTower ℚ E L] in
theorem res_smul (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L)
    (h : ∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) (x : 𝓞 E) :
    algebraMap (𝓞 E) (𝓞 L) (σ • x) = τ • algebraMap (𝓞 E) (𝓞 L) x := by
  apply RingOfIntegers.coe_injective
  exact h x

omit [IsScalarTower ℚ E L] [NumberField E] [NumberField L] in
theorem mem_over_iff (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.LiesOver P]
    (x : 𝓞 E) : x ∈ P ↔ algebraMap (𝓞 E) (𝓞 L) x ∈ Q := by
  rw [Ideal.over_def Q P, Ideal.under_def, Ideal.mem_comap]

omit [IsScalarTower ℚ E L] in
theorem inertia_res (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.LiesOver P]
    (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L)
    (h : ∀ x, algebraMap E L (σ x) = τ (algebraMap E L x))
    (hτ : ∀ y : 𝓞 L, τ • y - y ∈ Q) (x : 𝓞 E) : σ • x - x ∈ P := by
  rw [mem_over_iff P Q, map_sub, res_smul σ τ h]
  exact hτ _

omit [IsScalarTower ℚ E L] in
theorem frob_res (p : ℕ) (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L))
    [Q.LiesOver P] [Q.LiesOver (span {(p : ℤ)})]
    [P.LiesOver (span {(p : ℤ)})] (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L)
    (h : ∀ x, algebraMap E L (σ x) = τ (algebraMap E L x))
    (hτ : IsArithFrobAt ℤ τ Q) : IsArithFrobAt ℤ σ P := by
  have hcard : Nat.card (ℤ ⧸ P.under ℤ) = Nat.card (ℤ ⧸ Q.under ℤ) := by
    rw [← Ideal.over_def P (span {(p : ℤ)}),
      ← Ideal.over_def Q (span {(p : ℤ)})]
  intro x
  show σ • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P
  rw [hcard, mem_over_iff P Q, map_sub, map_pow, res_smul σ τ h]
  exact hτ (algebraMap (𝓞 E) (𝓞 L) x)

theorem mem_stabilizer_of {G S : Type*} [Group G] [CommRing S]
    [MulSemiringAction G S] (g : G) (I : Ideal S)
    (h : ∀ z : S, g • z ∈ I ↔ z ∈ I) : g ∈ MulAction.stabilizer G I := by
  rw [MulAction.mem_stabilizer_iff]
  ext z
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← h (g⁻¹ • z), smul_inv_smul]

theorem smul_mem_of_inertia {G S : Type*} [Group G] [CommRing S]
    [MulSemiringAction G S] (g : G) (I : Ideal S)
    (h : ∀ x : S, g • x - x ∈ I) (z : S) : g • z ∈ I ↔ z ∈ I :=
  ⟨fun hz => by simpa using I.sub_mem hz (h z),
    fun hz => by simpa using I.add_mem (h z) hz⟩

/-- An actual inertia automorphism downstairs has an inertia lift at the
chosen prime upstairs. The lift is adjusted inside the relative Galois group
to fix the prime and then to act trivially on its residue field. -/
theorem inertia_lift [IsGalois ℚ L]
    (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver P]
    (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x : 𝓞 E, σ • x - x ∈ P) :
    ∃ τ : L ≃ₐ[ℚ] L,
      (∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) ∧
      ∀ y : 𝓞 L, τ • y - y ∈ Q := by
  let : IsGalois E L := IsGalois.tower_top_of_isGalois ℚ E L
  let τ₀ : L ≃ₐ[ℚ] L := σ.liftNormal L
  have h₀ : ∀ x, algebraMap E L (σ x) = τ₀ (algebraMap E L x) :=
    fun x => (AlgEquiv.liftNormal_commutes σ L x).symm
  have hunder : (τ₀⁻¹ • Q).under (𝓞 E) = Q.under (𝓞 E) := by
    ext a
    rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_inv_pointwise_smul_iff, ← res_smul σ τ₀ h₀,
      ← mem_over_iff P Q, ← mem_over_iff P Q]
    exact smul_mem_of_inertia σ P hσ a
  obtain ⟨ρ, hρ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
    (𝓞 E) (𝓞 L) (L ≃ₐ[E] L) Q (τ₀⁻¹ • Q) hunder.symm
  let τ₁ : L ≃ₐ[ℚ] L := τ₀ * ρ.restrictScalars ℚ
  have hs : ∀ (r : L ≃ₐ[E] L) (y : 𝓞 L),
      (r.restrictScalars ℚ) • y = r • y := fun _ _ => rfl
  have h₁ : ∀ x, algebraMap E L (σ x) = τ₁ (algebraMap E L x) := fun x => by
    show _ = τ₀ (ρ (algebraMap E L x))
    rw [ρ.commutes, h₀]
  have hst : τ₁ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q := by
    refine mem_stabilizer_of τ₁ Q fun z => ?_
    rw [mul_smul, hs, ← Ideal.mem_inv_pointwise_smul_iff, hρ]
    exact Ideal.smul_mem_pointwise_smul_iff
  let f : (𝓞 L ⧸ Q) ≃ₐ[𝓞 E ⧸ P] (𝓞 L ⧸ Q) :=
    AlgEquiv.ofRingEquiv
      (f := (Ideal.Quotient.stabilizerHom Q (Q.under ℤ)
        (L ≃ₐ[ℚ] L) ⟨τ₁, hst⟩).toRingEquiv) (by
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      show Ideal.Quotient.mk Q (τ₁ • algebraMap (𝓞 E) (𝓞 L) a) =
        Ideal.Quotient.mk Q (algebraMap (𝓞 E) (𝓞 L) a)
      rw [Ideal.Quotient.eq, ← res_smul σ τ₁ h₁, ← map_sub, ← mem_over_iff P Q]
      exact hσ a)
  obtain ⟨r, hr⟩ := Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[E] L) P Q f
  refine ⟨τ₁ * (r.1⁻¹).restrictScalars ℚ, fun x => ?_, fun y => ?_⟩
  · show _ = τ₁ ((r.1⁻¹) (algebraMap E L x))
    rw [AlgEquiv.commutes, h₁]
  · have h2 : Ideal.Quotient.mk Q (r.1 • (r.1⁻¹ • y)) =
        Ideal.Quotient.mk Q (τ₁ • (r.1⁻¹ • y)) :=
      DFunLike.congr_fun hr (Ideal.Quotient.mk Q (r.1⁻¹ • y))
    rw [smul_inv_smul] at h2
    rw [mul_smul, hs, ← Ideal.Quotient.eq]
    exact h2.symm

/-- Choose a genuine prime of the upper number field over the given prime.
The same prime supports inertia lifting and arithmetic Frobenius descent. -/
theorem exists_over [IsGalois ℚ L] (l : ℕ)
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver P)
      (_ : Q.LiesOver (span {(l : ℤ)})),
      (∀ σ : E ≃ₐ[ℚ] E, (∀ x : 𝓞 E, σ • x - x ∈ P) ↔
        ∃ τ : L ≃ₐ[ℚ] L,
          (∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) ∧
          ∀ y : 𝓞 L, τ • y - y ∈ Q) ∧
      ∀ (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L),
        (∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) →
        IsArithFrobAt ℤ τ Q → IsArithFrobAt ℤ σ P := by
  obtain ⟨⟨Q, hQp, hQP⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
  let : Q.IsPrime := hQp
  let : Q.LiesOver P := hQP
  have hQl : Q.LiesOver (span {(l : ℤ)}) :=
    Ideal.LiesOver.trans Q P (span {(l : ℤ)})
  let : Q.LiesOver (span {(l : ℤ)}) := hQl
  exact ⟨Q, hQp, hQP, hQl,
    fun σ => ⟨inertia_lift P Q σ,
      fun ⟨τ, h1, h2⟩ => inertia_res P Q σ τ h1 h2⟩,
    fun σ τ h1 h2 => frob_res l P Q σ τ h1 h2⟩

end Tower

/-- All arithmetic Frobenius lifts at one prime form the coset of its
actual inertia subgroup. -/
theorem frob_iff_inertia {G S : Type*} [Group G] [CommRing S]
    [MulSemiringAction G S] [SMulCommClass G ℤ S]
    (P : Ideal S) (F σ : G) (hF : IsArithFrobAt ℤ F P) :
    IsArithFrobAt ℤ σ P ↔ ∀ x : S, (σ * F⁻¹) • x - x ∈ P := by
  have hF' : ∀ x : S, F • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P := hF
  constructor
  · intro hσ x
    have hσ' : ∀ x : S, σ • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P := hσ
    have h1 := P.sub_mem (hσ' (F⁻¹ • x)) (hF' (F⁻¹ • x))
    rwa [smul_inv_smul, ← mul_smul, sub_sub_sub_cancel_right] at h1
  · intro hρ x
    show σ • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P
    have h1 := P.add_mem (hρ (F • x)) (hF' x)
    rwa [← mul_smul, inv_mul_cancel_right, sub_add_sub_cancel] at h1

end RHLean.Analysis.NativePrimeLift

end
