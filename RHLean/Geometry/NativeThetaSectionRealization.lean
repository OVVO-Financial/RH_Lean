import RHLean.Geometry.NativeThetaChartAgreement
import RHLean.Geometry.NativeThetaFaithfullyFlatDescent
import RHLean.Geometry.NativeGenericFrameFaithfulness

/-!
# Realize the native short-theta expression in the original base algebra

The input consists of a faithfully flat evaluation algebra, its literal
column jets, and the finite permutations and odd-torsion phases on common
charts. Phase cancellation supplies the equalizer condition; effective
faithfully flat descent then constructs a unique value in the base algebra.
Fixed-degree linearity and naturality are proved for those constructed
values. Applied pointwise, this gives a natural rule in the existing
`NativeFramedRules.Rules` carrier.

No value-existence, theta-value comparison, linearity or naturality
conclusion is an input. The actual polarized geometric chart, its torsion
enumerations, and its theta-group phase relations must still be supplied
on the given host. Naturality alone does not assert the weight law,
integrality, Petersson bounds, or cusp density.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`ShortThetaValueExistsUniqueNaturalOfLaws.lean` and
`ShortThetaValueLinearInPolynomial.lean`.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace RHLean.Geometry.NativeTheta.SectionRealization

open JetEvaluation

variable {T K Q J : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
  [Field K] [Fintype Q] [Fintype J]

/-- Concrete transition data for the transported column jets. The final
theta expression is absent from this predicate. -/
def PhaseTransport {B₁ B₂ A : Type} [CommRing B₁] [CommRing B₂] [CommRing A]
    [Algebra K B₁] [Algebra K B₂] [Algebra K A]
    (N : ℕ) (ψ₁ : B₁ →ₐ[K] A) (ψ₂ : B₂ →ₐ[K] A)
    (jet₁ : Q → J → Fin n → (Row T r →₀ ℕ) → B₁)
    (jet₂ : Q → J → Fin n → (Row T r →₀ ℕ) → B₂) : Prop :=
  ∃ (ρ : Q → J ≃ J) (phase : Q → J → Fin n → A),
    (∀ q j, (∏ b, phase q j b) ^ 2 = 1) ∧
    (∀ q j b, phase q j b ^ (N ^ 2) = 1) ∧
    ∀ q j b α, ψ₂ (jet₂ q j b α) = phase q j b * ψ₁ (jet₁ q (ρ q j) b α)

theorem PhaseTransport.value_eq {B₁ B₂ A : Type}
    [CommRing B₁] [CommRing B₂] [CommRing A]
    [Algebra K B₁] [Algebra K B₂] [Algebra K A]
    {N : ℕ} {ψ₁ : B₁ →ₐ[K] A} {ψ₂ : B₂ →ₐ[K] A}
    {jet₁ : Q → J → Fin n → (Row T r →₀ ℕ) → B₁}
    {jet₂ : Q → J → Fin n → (Row T r →₀ ℕ) → B₂}
    (h : PhaseTransport N ψ₁ ψ₂ jet₁ jet₂) (hN : Odd N)
    (β : K) (index : ℕ) (w : Q → K) (P : MvPolynomial (Letter T r n) K) :
    ψ₁ (rawShortValue β index N w jet₁ P) =
      ψ₂ (rawShortValue β index N w jet₂ P) := by
  obtain ⟨ρ, phase, hisotropic, htorsion, hjet⟩ := h
  exact map_rawShortValue_eq_of_permuted_odd_phases ψ₁ ψ₂ β index N w hN
    jet₁ jet₂ ρ phase hisotropic htorsion hjet P

section Value

variable {S B : Type} [CommRing S] [CommRing B] [Algebra K S] [Algebra K B]
  (φ : S →ₐ[K] B) (hφ : φ.toRingHom.FaithfullyFlat)
  (β : K) (index N : ℕ) (w : Q → K)
  (jet : Q → J → Fin n → (Row T r →₀ ℕ) → B) (hN : Odd N)
  (hphase : ∀ (A : Type) [CommRing A] [Algebra K A] (ψ₁ ψ₂ : B →ₐ[K] A),
    ψ₁.comp φ = ψ₂.comp φ → PhaseTransport N ψ₁ ψ₂ jet jet)

/-- The original-base value is constructed by effective descent, with its
equalizer condition proved by the finite odd-phase calculation. -/
theorem existsUnique_value (P : MvPolynomial (Letter T r n) K) :
    ∃! v : S, φ v = rawShortValue β index N w jet P := by
  apply Descent.existsUnique_preimage_of_faithfullyFlat K S B φ hφ
  intro A _ _ ψ₁ ψ₂ hcomp
  exact (hphase A ψ₁ ψ₂ hcomp).value_eq hN β index w P

def value (P : MvPolynomial (Letter T r n) K) : S :=
  (existsUnique_value φ hφ β index N w jet hN hphase P).choose

theorem value_spec (P : MvPolynomial (Letter T r n) K) :
    φ (value φ hφ β index N w jet hN hphase P) = rawShortValue β index N w jet P :=
  (existsUnique_value φ hφ β index N w jet hN hphase P).choose_spec.1

/-- The unique descended values form a linear map on the prescribed
homogeneous degree. The zero polynomial is included. -/
def valueLinear (D : ℕ) : homogeneousSubmodule (Letter T r n) K D →ₗ[K] S where
  toFun P := value φ hφ β index N w jet hN hphase P
  map_add' P P' := by
    apply hφ.injective
    rw [map_add, value_spec, value_spec, value_spec]
    rw [rawShortValue_eq_linear_of_homogeneous β index N D w jet _ (P + P').property,
      rawShortValue_eq_linear_of_homogeneous β index N D w jet _ P.property,
      rawShortValue_eq_linear_of_homogeneous β index N D w jet _ P'.property]
    exact map_add _ _ _
  map_smul' c P := by
    apply hφ.injective
    rw [map_smul, value_spec, value_spec]
    rw [rawShortValue_eq_linear_of_homogeneous β index N D w jet _ (c • P).property,
      rawShortValue_eq_linear_of_homogeneous β index N D w jet _ P.property]
    exact map_smul _ _ _

@[simp] theorem valueLinear_apply (D : ℕ)
    (P : homogeneousSubmodule (Letter T r n) K D) :
    valueLinear φ hφ β index N w jet hN hphase D P =
      value φ hφ β index N w jet hN hphase P := rfl

end Value

/-- Compare two descended values after an actual base change. The common
faithfully flat comparison algebra is constructed, and its equality of
theta expressions comes from the supplied finite transition data. -/
theorem map_eq_of_chart_values {S₁ S₂ B₁ B₂ : Type}
    [CommRing S₁] [CommRing S₂] [CommRing B₁] [CommRing B₂]
    [Algebra K S₁] [Algebra K S₂] [Algebra K B₁] [Algebra K B₂]
    (φ₁ : S₁ →ₐ[K] B₁) (φ₂ : S₂ →ₐ[K] B₂)
    (hφ₁ : φ₁.toRingHom.FaithfullyFlat) (hφ₂ : φ₂.toRingHom.FaithfullyFlat)
    (f : S₁ →ₐ[K] S₂) (β : K) (index N : ℕ) (w : Q → K) (hN : Odd N)
    (jet₁ : Q → J → Fin n → (Row T r →₀ ℕ) → B₁)
    (jet₂ : Q → J → Fin n → (Row T r →₀ ℕ) → B₂)
    (hphase : ∀ (A : Type) [CommRing A] [Algebra K A]
      (ψ₁ : B₁ →ₐ[K] A) (ψ₂ : B₂ →ₐ[K] A),
      ψ₁.comp φ₁ = ψ₂.comp (φ₂.comp f) → PhaseTransport N ψ₁ ψ₂ jet₁ jet₂)
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

section Rules

open RHLean.Geometry.NativeFramedRules

variable
  (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
  (mapR : ∀ {S A : Type} [CommRing S] [Algebra K S]
    [CommRing A] [Algebra K A], (S →ₐ[K] A) → pts S → pts A → Prop)
  (B : ∀ p : TestRing K, pts p.R → Type)
  [∀ p y, CommRing (B p y)] [∀ p y, Algebra K (B p y)]
  (φ : ∀ (p : TestRing K) (y : pts p.R), p.R →ₐ[K] B p y)
  (hφ : ∀ p y, (φ p y).toRingHom.FaithfullyFlat)
  (β : K) (index N : ℕ) (w : Q → K) (hN : Odd N)
  (jet : ∀ (p : TestRing K) (y : pts p.R), Q → J → Fin n → (Row T r →₀ ℕ) → B p y)
  (hself : ∀ (p : TestRing K) (y : pts p.R)
    (A : Type) [CommRing A] [Algebra K A] (ψ₁ ψ₂ : B p y →ₐ[K] A),
    ψ₁.comp (φ p y) = ψ₂.comp (φ p y) → PhaseTransport N ψ₁ ψ₂ (jet p y) (jet p y))

/-- A rule on the original reduced test rings, taking its values in those
test rings rather than in their chosen evaluation covers. -/
def rule (P : MvPolynomial (Letter T r n) K) : Rules pts :=
  fun p y => value (φ p y) (hφ p y) β index N w (jet p y) hN (hself p y) P

/-- The rule's geometric naturality is a conclusion of the concrete
common-chart phase relations and faithful descent. -/
theorem rule_isNatural
    (hchange : ∀ (p q : TestRing K) (f : p.R →ₐ[K] q.R)
      (y : pts p.R) (z : pts q.R), mapR f y z →
      ∀ (A : Type) [CommRing A] [Algebra K A]
        (ψ₁ : B p y →ₐ[K] A) (ψ₂ : B q z →ₐ[K] A),
        ψ₁.comp (φ p y) = ψ₂.comp ((φ q z).comp f) →
        PhaseTransport N ψ₁ ψ₂ (jet p y) (jet q z))
    (P : MvPolynomial (Letter T r n) K) :
    IsNatural pts mapR (rule pts B φ hφ β index N w hN jet hself P) := by
  intro p q f y z hmap
  exact (map_eq_of_chart_values (φ p y) (φ q z) (hφ p y) (hφ q z)
    f β index N w hN (jet p y) (jet q z) (hchange p q f y z hmap) P _ _
    (value_spec (φ p y) (hφ p y) β index N w (jet p y) hN (hself p y) P)
    (value_spec (φ q z) (hφ q z) β index N w (jet q z) hN (hself q z) P)).symm

/-- Fixed-degree polynomials map linearly into the existing rule carrier. -/
def ruleLinear (D : ℕ) : homogeneousSubmodule (Letter T r n) K D →ₗ[K] Rules pts :=
  LinearMap.pi fun p => LinearMap.pi fun y =>
    valueLinear (φ p y) (hφ p y) β index N w (jet p y) hN (hself p y) D

@[simp] theorem ruleLinear_apply (D : ℕ)
    (P : homogeneousSubmodule (Letter T r n) K D) :
    ruleLinear pts B φ hφ β index N w hN jet hself D P =
      rule pts B φ hφ β index N w hN jet hself P := rfl

end Rules

end RHLean.Geometry.NativeTheta.SectionRealization

end
