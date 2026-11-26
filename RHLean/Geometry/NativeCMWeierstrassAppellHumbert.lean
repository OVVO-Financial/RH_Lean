import RHLean.Geometry.NativeCMWeierstrassHolomorphic

/-!
# A constructed elliptic Appell--Humbert uniformization and exact Lie norm

This is the scalar, dimension-one form of the source HolUnif contract:
actual scheme exponential, exact original lattice kernel, all regular
sections holomorphic, and analytic nonzero frames with the actual bundle
transitions. Its Appell--Humbert law is proved from the constructed sigma
product. The actual epsilon tangent has direction u by the regular-section
localization theorem, so its squared length is exactly pi*|u|²/covol(L).

The definition follows the dimension-one content of
`src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsLieBasis.lean`
in Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
The source archive states no license; attribution is retained without assigning one.
No global theta-uniformization theorem or prescribed arithmetic mean is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj PeriodPair
open Complex Filter
open scoped Topology ComplexConjugate Real

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory

open SectionPoints SchemeTheory.WeierstrassCurve WeierstrassLie

/-- The domain condition for a complex point in an algebraic chart. -/
def ellipticPointInOpen {W : _root_.WeierstrassCurve ℂ} (p : 𝟙_ (Over (Sp ℂ)) ⟶ schemeOver W)
    (U : (scheme W).Opens) : Prop :=
  (⊤ : (Sp ℂ).Opens) ≤ p.left ⁻¹ᵁ U

set_option maxHeartbeats 3000000 in
/-- The complete one-dimensional holomorphic atlas on an actual elliptic
scheme and its actual origin line bundle, with the specified period lattice. -/
structure EllipticHolUnif (W : _root_.WeierstrassCurve ℂ) [W.IsElliptic] (L : PeriodPair) where
  ex : ℂ → (𝟙_ (Over (Sp ℂ)) ⟶ schemeOver W)
  ex_add : ∀ z w : ℂ, ex (z + w) = ex z * ex w
  ex_onto : Function.Surjective ex
  ker : ∀ z, ex z = 1 ↔ z ∈ L.lattice
  hol : ∀ (U : (scheme W).Opens) (s : Γ(scheme W, U)),
    IsOpen {z | ellipticPointInOpen (W := W) (ex z) U} ∧
      DifferentiableOn ℂ (fun z => value (ex z).left U s) {z | ellipticPointInOpen (W := W) (ex z) U}
  fr : (originLB W).ι → ℂ → ℂ
  fr_hol : ∀ i, DifferentiableOn ℂ (fr i) {z | ellipticPointInOpen (W := W) (ex z) ((originLB W).U i)}
  fr_ne : ∀ i z, ellipticPointInOpen (W := W) (ex z) ((originLB W).U i) → fr i z ≠ 0
  fr_compat : ∀ (i j : (originLB W).ι) (z : ℂ)
    (h : ellipticPointInOpen (W := W) (ex z) ((originLB W).U i ⊓ (originLB W).U j)),
    fr i z = evalPt (ex z).left ((originLB W).U i ⊓ (originLB W).U j) h
      ((originLB W).g i j : Γ(scheme W, (originLB W).U i ⊓ (originLB W).U j)) * fr j z

namespace EllipticHolUnif

variable {W : _root_.WeierstrassCurve ℂ} [W.IsElliptic] {L : PeriodPair}
  (u : EllipticHolUnif W L)

/-- The actual scalar Hermitian form and character govern these same frames. -/
def IsAH (H : ℂ → ℂ → ℂ) (χ : ℂ → ℂ) : Prop :=
  (∀ z w, conj (H z w) = H w z) ∧
  (∀ z : ℂ, z ≠ 0 → 0 < (H z z).re) ∧
  (∀ w ∈ L.lattice, ‖χ w‖ = 1) ∧
  ∀ (w : ℂ), w ∈ L.lattice → ∀ i z,
    ⊤ ≤ (u.ex z).left ⁻¹ᵁ (originLB W).U i →
      u.fr i z = (χ w * exp (π * H z w + π / 2 * H w w)) * u.fr i (z + w)

/-- The one-dimensional differential equality is required on every actual
regular section, including its genuine domain around the epsilon point. -/
def HasTangentDirection (w : ℂ) (v : epsR ℂ ⟶ schemeOver W) : Prop :=
  IsTangent v ∧ ∀ (U : (scheme W).Opens) (h : ⊤ ≤ v.left ⁻¹ᵁ U) (s : Γ(scheme W, U)),
    ∃ d : ℂ, HasDerivAt (fun z : ℂ => value (u.ex z).left U s) d (0 : ℂ) ∧
      (evalPt v.left U h s).snd = d * w

end EllipticHolUnif

end RHLean.Geometry.NativeCM.SchemeTheory

namespace RHLean.Geometry.NativeCM.WeierstrassTheta

open SchemeTheory SchemeTheory.SectionPoints SchemeTheory.WeierstrassCurve
open SchemeTheory.WeierstrassLie SchemeTheory.WeierstrassSectionJet
open Weierstrass PeriodMean

variable (L : PeriodPair) (W : _root_.WeierstrassCurve ℂ) [W.IsElliptic]
  (C : _root_.WeierstrassCurve.VariableChange ℂ)
  (hC : C • W.baseChange ℂ = latticeCurve L)

/-- Every field of the holomorphic uniformization is supplied by the
actual equation, actual regular sections and the actual sigma frames. -/
def canonicalHolUnif : EllipticHolUnif W L where
  ex := expOver L W C hC
  ex_add := expOver_add L W C hC
  ex_onto := expOver_surjective L W C hC
  ker := expOver_kernel L W C hC
  hol := holomorphic_regular_sections L W C hC
  fr := atlasFrame W L C
  fr_hol := atlasFrame_differentiableOn W L C hC
  fr_ne i z := atlasFrame_ne_zero W L C hC i (z := z)
  fr_compat := atlasFrame_compat W L C hC

/-- The original canonical-sigma law is the Appell--Humbert law of the
actual algebraic origin bundle under this constructed uniformization. -/
theorem canonicalHolUnif_isAH :
    (canonicalHolUnif L W C hC).IsAH (latticeForm L) (sigmaSign L) := by
  refine ⟨conj_latticeForm L, ?_, fun w _ => norm_sigmaSign L w, ?_⟩
  · intro z hz
    rw [latticeForm_self, Complex.ofReal_re]
    exact div_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hz)) (latticeArea_pos L)
  · intro w hw i z _
    change atlasFrame W L C i z = multiplier L w z * atlasFrame W L C i (z + w)
    have e := atlasFrame_period W L C i hw z
    calc
      _ = atlasFrame W L C i (z + w) * multiplier L w z :=
        ((eq_div_iff (multiplier_ne_zero L w z)).mp e).symm
      _ = _ := mul_comm _ _

/-- The actual integral-coordinate epsilon generator has direction u;
this is proved on every regular section, rather than on coordinates alone. -/
theorem canonicalHolUnif_integral_tangent :
    (canonicalHolUnif L W C hC).HasTangentDirection (C.u : ℂ) (integralVector W) := by
  refine ⟨integralVector_isTangent W, ?_⟩
  intro U h s
  refine ⟨_, section_derivative L W C hC U h s, ?_⟩
  change (evalPt (vec W 1) U h s).snd =
    ((C.u : ℂ)⁻¹ * (evalPt (vec W 1) U h s).snd) * (C.u : ℂ)
  rw [mul_assoc, mul_comm _ (C.u : ℂ), ← mul_assoc,
    inv_mul_cancel₀ (Units.ne_zero C.u), one_mul]

/-- The exact positive Lie length comes from the actual bundle's proved
Appell--Humbert form and the actual epsilon-vector differential. -/
theorem canonicalHolUnif_exact_tangent_norm :
    (canonicalHolUnif L W C hC).IsAH (latticeForm L) (sigmaSign L) ∧
    (canonicalHolUnif L W C hC).HasTangentDirection (C.u : ℂ) (integralVector W) ∧
    0 < π * (latticeForm L (C.u : ℂ) (C.u : ℂ)).re ∧
    π * (latticeForm L (C.u : ℂ) (C.u : ℂ)).re =
      π * ‖(C.u : ℂ)‖ ^ 2 / ZLattice.covolume L.lattice :=
  ⟨canonicalHolUnif_isAH L W C hC, canonicalHolUnif_integral_tangent L W C hC,
    integral_direction_length_pos L C, integral_direction_length L C⟩

end RHLean.Geometry.NativeCM.WeierstrassTheta
