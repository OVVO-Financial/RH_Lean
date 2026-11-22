import RHLean.Geometry.NativeGenericFrameFaithfulness
import RHLean.Geometry.NativeGradedShortSectionConstruction

/-!
# Construct the short section on the original framed rule algebra

The ring, integer-weight spaces and generic evaluations are those constructed
from reduced polynomial test rings. The component-point evaluations are
evaluations at the actual chosen framed points. The same atlas chart that
contains such a point supplies homogeneous specialization, while the full
atlas supplies homogeneous faithfulness. These conclusions are derived here,
then applied to the existing integral short-section/determinant constructor.

Thus neither `hfaithful` nor `hspecialize` is a premise of this constructor.
Its remaining geometric inputs are the actual framed moduli and atlas,
translations, short theta lattices and component/orbit data. This does not
claim that those data have already been instantiated by a CM theta cover.

Source mechanism: `CocoSgt/riemann-hypothesis-lean` at
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/DivisorProofs/`
`SecZEqZeroOfGenVal.lean`, `IntegerExponentSectionMulEqZeroImpEqZero.lean`,
and `CardLeOfDetEqZero.lean`. The source archive/mirror states no license;
this notice preserves attribution without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators
open NumberField

namespace RHLean.Geometry

open NativeFramedRules

section Construction

variable {I K Z H P : Type}
  [Fintype I] [DecidableEq I]
  [Field K] [NumberField K] [Algebra K ℂ]
  [Fintype Z] [Group H] [Fintype H] [DecidableEq H]
  (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
  (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S]
    [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop)
  (borR : ∀ {S : Type} [CommRing S] [Algebra K S],
    (I → Sˣ) → pts S → pts S → Prop)
  (hL : EvaluationLaws pts mapR borR)
  (F : Z → Type) [∀ z, Field (F z)] [∀ z, Algebra K (F z)] [∀ z, CharZero (F z)]
  (genericPoint : ∀ z, pts (F z))

local notation "W" => secZ pts mapR borR
local notation "Wone" => one_mem_secZ pts mapR borR
local notation "Wmul" => secZ_mul_le pts mapR borR
local notation "Sec" => nativeGradedSectionAlgebra W Wone Wmul

/-- A chosen complex point retains the actual generic chart from which it
is reached. The component label is explicit, as required by the determinant
comparison; no identification of the two coefficient fields is made. -/
structure NativeComponentFramedPoints where
  point : Z → pts ℂ
  chart : Z → GenericChart pts mapR borR F genericPoint
  component_eq : ∀ z, (chart z).component = z
  specialize : ∀ z, (chart z).R →ₐ[K] ℂ
  middle : Z → pts ℂ
  torus : Z → I → ℂˣ
  map_spec : ∀ z, mapR (specialize z) (chart z).y (middle z)
  bor_spec : ∀ z, borR (torus z) (middle z) (point z)

/-- The coefficient-linear component evaluation used in the lattice's
orbit map is evaluation at that same actual framed point. -/
def nativeComponentFramedEvaluation
    (Q : NativeComponentFramedPoints pts mapR borR F genericPoint) (z : Z) :
    Rules pts →ₐ[K] ℂ :=
  evalAlgHom pts mapR (Q.point z) (hL.test ℂ (Q.point z))

omit [DecidableEq I] [NumberField K] [Fintype Z] [∀ z, CharZero (F z)] in
/-- Homogeneous specialization follows from the common chart and its
actual base-change/torus relations. -/
theorem nativeComponentFramedEvaluation_eq_zero
    (Q : NativeComponentFramedPoints pts mapR borR F genericPoint)
    (z : Z) (e : I → ℤ) (f : Rules pts) (hf : f ∈ W e)
    (h0 : genericHom pts mapR borR F genericPoint hL z f = 0) :
    nativeComponentFramedEvaluation pts mapR borR hL F genericPoint Q z f = 0 := by
  have hz : evalAt pts mapR f (genericPoint (Q.chart z).component) = 0 := by
    rw [Q.component_eq z]
    exact h0
  exact evalAt_eq_zero_of_chart pts mapR borR F genericPoint hL (Q.chart z) hf hz
    (Q.specialize z) (Q.middle z) (Q.point z) (Q.torus z) (Q.map_spec z) (Q.bor_spec z)

set_option backward.isDefEq.respectTransparency false in
/-- Construct the same short integral section on the reduced-test rule
algebra, deriving generic faithfulness, weight transformation and component
specialization from the supplied actual framed atlas. Every norm and rank
constant of the original finite lattice constructor is unchanged. -/
theorem nativeExists_framed_short_integral_injective_section
    (hA : Atlas pts mapR borR F genericPoint)
    (fr : ∀ z, (I → (F z)ˣ) → pts (F z))
    (hfr : ∀ z t, borR t (genericPoint z) (fr z t))
    (Q : NativeComponentFramedPoints pts mapR borR F genericPoint)
    (U : Submodule K Sec) [FiniteDimensional K U]
    (st : H → Rules pts →ₐ[K] Rules pts)
    (J : Z → Type) [∀ z, Fintype (J z)]
    (E : P → Type) [∀ p, SeminormedAddCommGroup (E p)]
    (D : NativeGradedShortSectionData W Wone Wmul U
      (nativeComponentFramedEvaluation pts mapR borR hL F genericPoint Q) st J E)
    (hst : ∀ h d f, f ∈ W d → st h f ∈ W d)
    (h1 : ∀ x, st 1 x = x)
    (hmul : ∀ h h' x, st (h * h') x = st h' (st h x))
    (χ : H →* Kˣ) (e : I → ℤ)
    (hUw : ∀ u : U, ((u : Sec) : Rules pts) ∈ W e) :
    let Λ := max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (D.rankBound : ℝ) *
      |(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * D.A)
    ∃ u : U, u ∈ D.lattice ∧
      (∀ p, ‖D.realize p u‖ ≤
        ((2 * Module.finrank ℚ K * D.rankBound : ℕ) : ℝ) *
          ((Fintype.card H : ℝ) ^ 2 * (D.beta * Λ))) ∧
      (Matrix.of fun h g : H =>
        nativeGradedSectionAction W Wone Wmul st hst (h * g) (u : Sec)).det ∈
        nonZeroDivisors Sec ∧
      ∀ f : Sec,
        (∀ h, ∑ g : H, (((χ g)⁻¹ : Kˣ) : K) •
          nativeGradedSectionAction W Wone Wmul st hst g
            (f * nativeGradedSectionAction W Wone Wmul st hst h (u : Sec)) = 0) →
        f = 0 := by
  exact nativeExists_graded_short_integral_injective_section W Wone Wmul U
    (nativeComponentFramedEvaluation pts mapR borR hL F genericPoint Q) st J E D F
    (genericHom pts mapR borR F genericPoint hL)
    (fun z t => evalHom pts mapR (fr z t) (hL.test (F z) (fr z t)))
    (fun z d f hf t => hL.wt d f hf (F z) t (genericPoint z) (fr z t) (hfr z t))
    (fun d f hf h0 => secZ_eq_zero_of_generic pts mapR borR F genericPoint hL hA hf h0)
    (nativeComponentFramedEvaluation_eq_zero pts mapR borR hL F genericPoint Q)
    hst h1 hmul χ e hUw

end Construction
end RHLean.Geometry

end
