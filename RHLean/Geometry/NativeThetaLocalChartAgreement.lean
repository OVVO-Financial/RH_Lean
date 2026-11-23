import RHLean.Geometry.NativeThetaSectionRealization
import RHLean.Geometry.NativeThetaJetFrame

/-!
# Theta descent from local chart phases

A torsion enumeration can be permuted differently over different local
pieces. This file therefore proves equality in the common coefficient
algebra from the actual maps to its maximal-ideal localizations. It applies
the finite odd-phase cancellation only after passage to a local algebra,
then constructs the unique original-base theta value by effective
faithfully flat descent. No global permutation or equality conclusion is
assumed. The raw jets and every short-value normalizer remain the same.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`ShortThetaSumEqOfWitnessesCommonAlgebra.lean`, GlobalTheory.ShortCompare.eq_of_local
and shortSum_eq_of_witnesses; and
`ShortThetaValueExistsUniqueNaturalOfLaws.lean`.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry.NativeTheta.SectionRealization

open JetEvaluation FormalCalculus

/-- The genuine maximal-ideal localization maps jointly detect equality. -/
theorem eq_of_maximal_localizations {A : Type} [CommRing A] (x y : A)
    (h : ∀ (I : Ideal A) [I.IsPrime], I.IsMaximal →
      algebraMap A (Localization.AtPrime I) x =
        algebraMap A (Localization.AtPrime I) y) : x = y := by
  rw [← sub_eq_zero]
  refine eq_zero_of_localization (x - y) fun I hI => ?_
  have : I.IsPrime := hI.isPrime
  simpa [map_sub, sub_eq_zero] using h I hI

/-- The source's local-algebra comparison, proved using those actual
localizations. -/
theorem eq_of_local_algebras {K A : Type} [Field K] [CommRing A] [Algebra K A]
    (x y : A)
    (h : ∀ (U : Type) [CommRing U] [IsLocalRing U] [Algebra K U]
      (κ : A →ₐ[K] U), κ x = κ y) : x = y := by
  apply eq_of_maximal_localizations x y
  intro I _ _
  exact h (Localization.AtPrime I) (IsScalarTower.toAlgHom K A (Localization.AtPrime I))

variable {T K Q J : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
  [Field K] [Fintype Q] [Fintype J]

/-- Only local permutations and phases are required on a common algebra.
They can vary with the chosen local base change. -/
def LocalPhaseTransport {B₁ B₂ A : Type}
    [CommRing B₁] [CommRing B₂] [CommRing A]
    [Algebra K B₁] [Algebra K B₂] [Algebra K A]
    (N : ℕ) (ψ₁ : B₁ →ₐ[K] A) (ψ₂ : B₂ →ₐ[K] A)
    (jet₁ : Q → J → Fin n → (Row T r →₀ ℕ) → B₁)
    (jet₂ : Q → J → Fin n → (Row T r →₀ ℕ) → B₂) : Prop :=
  ∀ (U : Type) [CommRing U] [IsLocalRing U] [Algebra K U] (κ : A →ₐ[K] U),
    PhaseTransport N (κ.comp ψ₁) (κ.comp ψ₂) jet₁ jet₂

theorem LocalPhaseTransport.value_eq {B₁ B₂ A : Type}
    [CommRing B₁] [CommRing B₂] [CommRing A]
    [Algebra K B₁] [Algebra K B₂] [Algebra K A]
    {N : ℕ} {ψ₁ : B₁ →ₐ[K] A} {ψ₂ : B₂ →ₐ[K] A}
    {jet₁ : Q → J → Fin n → (Row T r →₀ ℕ) → B₁}
    {jet₂ : Q → J → Fin n → (Row T r →₀ ℕ) → B₂}
    (h : LocalPhaseTransport N ψ₁ ψ₂ jet₁ jet₂) (hN : Odd N)
    (β : K) (index : ℕ) (w : Q → K) (P : MvPolynomial (Letter T r n) K) :
    ψ₁ (rawShortValue β index N w jet₁ P) =
      ψ₂ (rawShortValue β index N w jet₂ P) := by
  apply eq_of_local_algebras (K := K)
  intro U _ _ _ κ
  exact (h U κ).value_eq hN β index w P

section Value

variable {S B : Type} [CommRing S] [CommRing B] [Algebra K S] [Algebra K B]
  (φ : S →ₐ[K] B) (hφ : φ.toRingHom.FaithfullyFlat)
  (β : K) (index N : ℕ) (w : Q → K)
  (jet : Q → J → Fin n → (Row T r →₀ ℕ) → B) (hN : Odd N)
  (hphase : ∀ (A : Type) [CommRing A] [Algebra K A] (ψ₁ ψ₂ : B →ₐ[K] A),
    ψ₁.comp φ = ψ₂.comp φ → LocalPhaseTransport N ψ₁ ψ₂ jet jet)

include hφ hN hphase in
/-- Effective descent with the source-compatible local phase input. -/
theorem existsUnique_value_of_local_phases (P : MvPolynomial (Letter T r n) K) :
    ∃! v : S, φ v = rawShortValue β index N w jet P := by
  apply Descent.existsUnique_preimage_of_faithfullyFlat K S B φ hφ
  intro A _ _ ψ₁ ψ₂ hcomp
  exact (hphase A ψ₁ ψ₂ hcomp).value_eq hN β index w P

def valueOfLocalPhases (P : MvPolynomial (Letter T r n) K) : S :=
  (existsUnique_value_of_local_phases φ hφ β index N w jet hN hphase P).choose

theorem valueOfLocalPhases_spec (P : MvPolynomial (Letter T r n) K) :
    φ (valueOfLocalPhases φ hφ β index N w jet hN hphase P) =
      rawShortValue β index N w jet P :=
  (existsUnique_value_of_local_phases φ hφ β index N w jet hN hphase P).choose_spec.1

end Value

/-- Naturality uses only local phases on the constructed common
faithfully flat comparison algebra. -/
theorem map_eq_of_local_chart_values {S₁ S₂ B₁ B₂ : Type}
    [CommRing S₁] [CommRing S₂] [CommRing B₁] [CommRing B₂]
    [Algebra K S₁] [Algebra K S₂] [Algebra K B₁] [Algebra K B₂]
    (φ₁ : S₁ →ₐ[K] B₁) (φ₂ : S₂ →ₐ[K] B₂)
    (hφ₁ : φ₁.toRingHom.FaithfullyFlat) (hφ₂ : φ₂.toRingHom.FaithfullyFlat)
    (f : S₁ →ₐ[K] S₂) (β : K) (index N : ℕ) (w : Q → K) (hN : Odd N)
    (jet₁ : Q → J → Fin n → (Row T r →₀ ℕ) → B₁)
    (jet₂ : Q → J → Fin n → (Row T r →₀ ℕ) → B₂)
    (hphase : ∀ (A : Type) [CommRing A] [Algebra K A]
      (ψ₁ : B₁ →ₐ[K] A) (ψ₂ : B₂ →ₐ[K] A),
      ψ₁.comp φ₁ = ψ₂.comp (φ₂.comp f) → LocalPhaseTransport N ψ₁ ψ₂ jet₁ jet₂)
    (P : MvPolynomial (Letter T r n) K) (v₁ : S₁) (v₂ : S₂)
    (hv₁ : φ₁ v₁ = rawShortValue β index N w jet₁ P)
    (hv₂ : φ₂ v₂ = rawShortValue β index N w jet₂ P) : f v₁ = v₂ := by
  obtain ⟨A, _, _, ψ₂, ψ₁, hcomp, _, hinj⟩ :=
    Descent.exists_faithfullyFlat_pushout K S₁ B₂ B₁ (φ₂.comp f) φ₁ hφ₁
  apply hφ₂.injective
  apply hinj
  calc
    ψ₂ (φ₂ (f v₁)) = ψ₁ (φ₁ v₁) := AlgHom.congr_fun hcomp v₁
    _ = ψ₁ (rawShortValue β index N w jet₁ P) := congrArg ψ₁ hv₁
    _ = ψ₂ (rawShortValue β index N w jet₂ P) :=
      (hphase A ψ₁ ψ₂ hcomp.symm).value_eq hN β index w P
    _ = ψ₂ (φ₂ v₂) := (congrArg ψ₂ hv₂).symm

section Weight

variable {S B : Type} [CommRing S] [CommRing B] [Algebra K S] [Algebra K B]
  [Algebra ℚ B] [Infinite K] {d : ℕ}

/-- Local phase descent reaches the same original-base triangular weight
law. Only local permutations and phases are used to construct both values. -/
theorem valueOfLocalPhases_triangular
    (φ : S →ₐ[K] B) (hφ : φ.toRingHom.FaithfullyFlat)
    (β : K) (index N : ℕ) (w : Q → K) (hN : Odd N)
    (G : FormalGroup B d) (actW0 : Fin d → Series B 1 d) (h : Series B 2 d)
    (u u' : Row T r → Fin d → B)
    (germ : Q → J → Fin n → Series B 1 d)
    (hphase : ∀ (A : Type) [CommRing A] [Algebra K A] (ψ₁ ψ₂ : B →ₐ[K] A),
      ψ₁.comp φ = ψ₂.comp φ → LocalPhaseTransport N ψ₁ ψ₂
        (fun q j b => formalColumnJet G.F actW0 h (N ^ 2) (germ q j b) u)
        (fun q j b => formalColumnJet G.F actW0 h (N ^ 2) (germ q j b) u))
    (hphase' : ∀ (A : Type) [CommRing A] [Algebra K A] (ψ₁ ψ₂ : B →ₐ[K] A),
      ψ₁.comp φ = ψ₂.comp φ → LocalPhaseTransport N ψ₁ ψ₂
        (fun q j b => formalColumnJet G.F actW0 h (N ^ 2) (germ q j b) u')
        (fun q j b => formalColumnJet G.F actW0 h (N ^ 2) (germ q j b) u'))
    (cf : ∀ τ, Fin (r τ) → Fin (r τ) → S)
    (hcf : ∀ τ i j, i < j → cf τ i j = 0)
    (huu : ∀ τ i e, u' ⟨τ, i⟩ e = ∑ j, φ (cf τ i j) * u ⟨τ, j⟩ e)
    (hu : ∀ τ i, IsUnit (cf τ i i))
    (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) K) (hP : P ∈ HHa r n K cc isX a) :
    valueOfLocalPhases φ hφ β index N w
        (fun q j b => formalColumnJet G.F actW0 h (N ^ 2) (germ q j b) u')
        hN hphase' P =
      (∏ l : Row T r, cf l.1 l.2 l.2 ^ a l.1 l.2) *
        valueOfLocalPhases φ hφ β index N w
          (fun q j b => formalColumnJet G.F actW0 h (N ^ 2) (germ q j b) u)
          hN hphase P := by
  classical
  apply hφ.injective
  rw [map_mul, valueOfLocalPhases_spec, valueOfLocalPhases_spec]
  change shortValueOfFormalGerms β index N w G.F actW0 h u' germ P =
    φ (∏ l : Row T r, cf l.1 l.2 l.2 ^ a l.1 l.2) *
      shortValueOfFormalGerms β index N w G.F actW0 h u germ P
  simpa only [map_prod, map_pow] using
    JetFrame.shortValueOfFormalGerms_triangular β index N w G actW0 h u u' germ
      (fun τ i j => φ (cf τ i j))
      (fun τ i j hij => by simp [hcf τ i j hij]) huu
      (fun τ i => (hu τ i).map φ) cc isX a P hP

end Weight

end RHLean.Geometry.NativeTheta.SectionRealization

end
