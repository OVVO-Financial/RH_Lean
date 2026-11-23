import RHLean.Geometry.NativeThetaJetEvaluation

/-!
# Finite chart agreement for the literal native theta expression

Two enumerations of the same finite isotropic group are related by a
constructed permutation after translation. The column phases in the
theta-group comparison have odd-order torsion; isotropy gives square of
their product equal to one, so the product itself is one. Consequently the
exact normalized jet expression agrees in a common comparison algebra.

No chart-independence law or equality of theta values is assumed. The
inputs are the actual enumeration, translation, column phases, and their
torsion/pairing relations. Constructing these from a polarized abelian
scheme remains a separate geometric step.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`IsotropicSumIndependentOfChoicesLocal.lean`, `shortSum_indep_local`,
and `ShortThetaSumEqOfWitnessesCommonAlgebra.lean`.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativeTheta.ChartAgreement

/-- Translation of one enumeration of the same finite subgroup gives a
permutation of the other enumeration. Surjectivity of the second
enumeration is not an extra input: finite injectivity supplies it. -/
theorem exists_enumeration_translate_equiv {G J : Type} [Group G] [Finite J]
    (H : Subgroup G) (z₁ z₂ : J → G)
    (hz₁ : ∀ z ∈ H, ∃ j, z₁ j = z) (hz₂ : ∀ j, z₂ j ∈ H)
    (hinj : Function.Injective z₂) (u : G) (hu : u ∈ H) :
    ∃ ρ : J ≃ J, ∀ j, z₁ (ρ j) = u * z₂ j := by
  classical
  choose ρ hρ using fun j => hz₁ (u * z₂ j) (H.mul_mem hu (hz₂ j))
  have hρinj : Function.Injective ρ := by
    intro i j hij
    apply hinj
    apply mul_left_cancel (a := u)
    exact (hρ i).symm.trans ((congrArg z₁ hij).trans (hρ j))
  exact ⟨Equiv.ofBijective ρ (Finite.injective_iff_bijective.mp hρinj), hρ⟩

/-- Odd torsion eliminates the possible sign left by a squared pairing. -/
theorem eq_one_of_sq_eq_one_of_odd_torsion {M : Type} [CommMonoid M]
    (x : M) (N : ℕ) (hN : Odd N) (h₂ : x ^ 2 = 1)
    (hN₂ : x ^ (N ^ 2) = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hN.pow (n := 2)
  rw [hk, pow_succ, pow_mul, h₂, one_pow, one_mul] at hN₂
  exact hN₂

/-- The product of the column phases is one, with the original odd N²
torsion and isotropic square relation both retained. -/
theorem phase_product_eq_one {M I : Type} [CommMonoid M] [Fintype I]
    (r : I → M) (N : ℕ) (hN : Odd N)
    (h₂ : (∏ i, r i) ^ 2 = 1) (hN₂ : ∀ i, r i ^ (N ^ 2) = 1) :
    ∏ i, r i = 1 := by
  apply eq_one_of_sq_eq_one_of_odd_torsion _ N hN h₂
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => hN₂ i

/-- Derive the squared product relation in the base algebra from its
faithful realization and the actual isotropic pairing product. -/
theorem phase_product_eq_one_of_pairing {M A I : Type}
    [CommMonoid M] [CommMonoid A] [Fintype I]
    (f : M →* A) (hf : Function.Injective f) (r : I → M) (pair : I → A)
    (N : ℕ) (hN : Odd N) (hpair : ∀ i, (f (r i)) ^ 2 = pair i)
    (hisotropic : ∏ i, pair i = 1) (htorsion : ∀ i, r i ^ (N ^ 2) = 1) :
    ∏ i, r i = 1 := by
  apply phase_product_eq_one r N hN _ htorsion
  apply hf
  rw [map_pow, map_prod, ← Finset.prod_pow,
    Finset.prod_congr rfl (fun i _ => hpair i), hisotropic, map_one]

end RHLean.Geometry.NativeTheta.ChartAgreement

namespace RHLean.Geometry.NativeTheta.JetEvaluation

variable {T K S Q J : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
  [Field K] [CommRing S] [Algebra K S] [Fintype Q] [Fintype J]

/-- Coefficient base change preserves the exact four normalizing factors
and every finite jet contraction. -/
theorem map_rawShortValue {A : Type} [CommRing A] [Algebra K A]
    (φ : S →ₐ[K] A) (β : K) (index N : ℕ) (w : Q → K)
    (jet : Q → J → Fin n → (Row T r →₀ ℕ) → S)
    (P : MvPolynomial (Letter T r n) K) :
    φ (rawShortValue β index N w jet P) =
      rawShortValue β index N w (fun q j b α => φ (jet q j b α)) P := by
  classical
  simp only [rawShortValue, map_mul, map_sum, map_prod, AlgHom.commutes]

/-- Permuting the lattice lifts and multiplying the columns by phases
whose product is one does not change the actual theta expression. -/
theorem rawShortValue_eq_of_permuted_phases
    (β : K) (index N : ℕ) (w : Q → K)
    (jet₁ jet₂ : Q → J → Fin n → (Row T r →₀ ℕ) → S)
    (ρ : Q → J ≃ J) (phase : Q → J → Fin n → S)
    (hphase : ∀ q j, ∏ b, phase q j b = 1)
    (hjet : ∀ q j b α, jet₂ q j b α = phase q j b * jet₁ q (ρ q j) b α)
    (P : MvPolynomial (Letter T r n) K) :
    rawShortValue β index N w jet₂ P = rawShortValue β index N w jet₁ P := by
  classical
  unfold rawShortValue
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  calc
    _ = ∑ j, ∑ m ∈ P.support, algebraMap K S (P.coeff m) *
          ∏ b, jet₁ q (ρ q j) b (columnExponent m b) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.prod_congr rfl (fun b _ => hjet q j b (columnExponent m b)),
        Finset.prod_mul_distrib, hphase q j, one_mul]
    _ = _ := (ρ q).sum_comp (fun j : J =>
      ∑ m ∈ P.support, algebraMap K S (P.coeff m) *
        ∏ b, jet₁ q j b (columnExponent m b))

/-- In the original comparison the product-one relation is derived from
odd torsion and isotropy; it is not a chart-agreement premise. -/
theorem rawShortValue_eq_of_permuted_odd_phases
    (β : K) (index N : ℕ) (w : Q → K) (hN : Odd N)
    (jet₁ jet₂ : Q → J → Fin n → (Row T r →₀ ℕ) → S)
    (ρ : Q → J ≃ J) (phase : Q → J → Fin n → S)
    (hisotropic : ∀ q j, (∏ b, phase q j b) ^ 2 = 1)
    (htorsion : ∀ q j b, phase q j b ^ (N ^ 2) = 1)
    (hjet : ∀ q j b α, jet₂ q j b α = phase q j b * jet₁ q (ρ q j) b α)
    (P : MvPolynomial (Letter T r n) K) :
    rawShortValue β index N w jet₂ P = rawShortValue β index N w jet₁ P :=
  rawShortValue_eq_of_permuted_phases β index N w jet₁ jet₂ ρ phase
    (fun q j => ChartAgreement.phase_product_eq_one _ N hN (hisotropic q j) (htorsion q j))
    hjet P

/-- Common-algebra agreement of two chart expressions follows from the
literal transported column jets and the finite odd-phase calculation. -/
theorem map_rawShortValue_eq_of_permuted_odd_phases
    {S₁ S₂ A : Type} [CommRing S₁] [CommRing S₂] [CommRing A]
    [Algebra K S₁] [Algebra K S₂] [Algebra K A]
    (ψ₁ : S₁ →ₐ[K] A) (ψ₂ : S₂ →ₐ[K] A)
    (β : K) (index N : ℕ) (w : Q → K) (hN : Odd N)
    (jet₁ : Q → J → Fin n → (Row T r →₀ ℕ) → S₁)
    (jet₂ : Q → J → Fin n → (Row T r →₀ ℕ) → S₂)
    (ρ : Q → J ≃ J) (phase : Q → J → Fin n → A)
    (hisotropic : ∀ q j, (∏ b, phase q j b) ^ 2 = 1)
    (htorsion : ∀ q j b, phase q j b ^ (N ^ 2) = 1)
    (hjet : ∀ q j b α,
      ψ₂ (jet₂ q j b α) = phase q j b * ψ₁ (jet₁ q (ρ q j) b α))
    (P : MvPolynomial (Letter T r n) K) :
    ψ₁ (rawShortValue β index N w jet₁ P) =
      ψ₂ (rawShortValue β index N w jet₂ P) := by
  rw [map_rawShortValue, map_rawShortValue]
  exact (rawShortValue_eq_of_permuted_odd_phases β index N w hN _ _
    ρ phase hisotropic htorsion hjet P).symm

end RHLean.Geometry.NativeTheta.JetEvaluation

end
