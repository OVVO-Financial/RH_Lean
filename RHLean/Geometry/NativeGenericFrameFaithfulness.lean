import RHLean.Geometry.NativeGradedSectionRegularity

/-!
# Generic-frame faithfulness on the original reduced test rules

This file constructs the actual ring of rules on reduced, finitely generated
polynomial test rings and its integer-weight section spaces. Generic-frame
faithfulness is then proved from the original field-point atlas: a section
vanishing at the generic frame vanishes in the chart subalgebra, at every
field point, and finally in every reduced test ring by the Jacobson property.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Formalism/LocalToGlobal/ProjectiveLattices/AlgebraMapCAt.lean`,
`Formalism.L2.Pj.{TRing,Rules,IsNatural,FromTest,evalAt,EvalWD}`;
`Development/AbelianVarietyTheory/Definitions/Foundations/`
`IsProbabilityMeasureMuPart.lean`, `GlobalTheory.CompHt.secZ`; and
`Development/AbelianVarietyTheory/Proofs/DivisorProofs/`
`SecZEqZeroOfGenVal.lean`, `GlobalTheory.CompHt.secZ_eq_zero_of_genVal`.

The atlas data retain a subalgebra of the SAME generic field and the actual
base-change and torus relations. Neither faithfulness nor regularity is a
field of those data. Constructing the CM moduli, its framed points, and its
atlas remains a separate geometric obligation. No ambient rule-ring
regularity or identification of a generic field with the complex point field
is asserted. The source archive/mirror states no license; this notice
preserves attribution without assigning a new license to derived material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators

namespace RHLean.Geometry.NativeFramedRules

/-- The source's reduced finite-type polynomial test ring, constructed
without an abstract reducedness or field-separation premise. -/
structure TestRing (K : Type) [Field K] : Type where
  n : ℕ
  I : Ideal (MvPolynomial (Fin n) K)
  rad : I.IsRadical

abbrev TestRing.R {K : Type} [Field K] (p : TestRing K) : Type :=
  MvPolynomial (Fin p.n) K ⧸ p.I

section Rules

variable {K I : Type} [Field K]
  (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
  (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S]
    [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop)
  (borR : ∀ {S : Type} [CommRing S] [Algebra K S],
    (I → Sˣ) → pts S → pts S → Prop)

/-- The full ambient rule ring is a dependent product of the actual test
ring values. The section algebra will be a subalgebra of this ring. -/
abbrev Rules : Type := ∀ p : TestRing K, pts p.R → p.R

def IsNatural (f : Rules pts) : Prop :=
  ∀ (p q : TestRing K) (φ : p.R →ₐ[K] q.R) (y : pts p.R) (z : pts q.R),
    mapR φ y z → f q z = φ (f p y)

def FromTest {S : Type} [CommRing S] [Algebra K S] (y : pts S) : Prop :=
  ∃ (p : TestRing K) (φ : p.R →ₐ[K] S) (u : pts p.R), mapR φ u y

def evalAt (f : Rules pts) {S : Type} [CommRing S] [Algebra K S]
    (y : pts S) : S :=
  open Classical in
  if h : FromTest pts mapR y then
    h.choose_spec.choose (f h.choose h.choose_spec.choose_spec.choose)
  else 0

theorem evalAt_zero {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (0 : Rules pts) y = 0 := by
  unfold evalAt
  split_ifs <;> simp

theorem evalAt_one {S : Type} [CommRing S] [Algebra K S]
    (y : pts S) (hy : FromTest pts mapR y) :
    evalAt pts mapR (1 : Rules pts) y = 1 := by
  unfold evalAt
  rw [dite_eq_left hy]
  simp

theorem evalAt_add (f g : Rules pts) {S : Type} [CommRing S] [Algebra K S]
    (y : pts S) :
    evalAt pts mapR (f + g) y = evalAt pts mapR f y + evalAt pts mapR g y := by
  unfold evalAt
  split_ifs <;> simp

theorem evalAt_mul (f g : Rules pts) {S : Type} [CommRing S] [Algebra K S]
    (y : pts S) :
    evalAt pts mapR (f * g) y = evalAt pts mapR f y * evalAt pts mapR g y := by
  unfold evalAt
  split_ifs <;> simp

/-- Evaluation is a ring map at an actually tested point. -/
def evalHom {S : Type} [CommRing S] [Algebra K S]
    (y : pts S) (hy : FromTest pts mapR y) : Rules pts →+* S where
  toFun f := evalAt pts mapR f y
  map_zero' := evalAt_zero pts mapR y
  map_one' := evalAt_one pts mapR y hy
  map_add' f g := evalAt_add pts mapR f g y
  map_mul' f g := evalAt_mul pts mapR f g y

/-- The same evaluation preserves the actual coefficient field. -/
def evalAlgHom {S : Type} [CommRing S] [Algebra K S]
    (y : pts S) (hy : FromTest pts mapR y) : Rules pts →ₐ[K] S where
  __ := evalHom pts mapR y hy
  commutes' a := by
    change evalAt pts mapR (algebraMap K (Rules pts) a) y = algebraMap K S a
    unfold evalAt
    rw [dite_eq_left hy]
    exact hy.choose_spec.choose.commutes a

/-- Equality of values arising from two presentations of the same point.
This is the source's chart well-definedness law. -/
def EvalWD : Prop :=
  ∀ f : Rules pts, IsNatural pts mapR f →
    ∀ (S : Type) [CommRing S] [Algebra K S] (p q : TestRing K)
      (φ : p.R →ₐ[K] S) (ψ : q.R →ₐ[K] S)
      (y : pts p.R) (z : pts q.R) (w : pts S),
      mapR φ y w → mapR ψ z w → φ (f p y) = ψ (f q z)

theorem evalAt_of_map (hW : EvalWD pts mapR)
    {f : Rules pts} (hf : IsNatural pts mapR f)
    {S : Type} [CommRing S] [Algebra K S] {p : TestRing K}
    {φ : p.R →ₐ[K] S} {u : pts p.R} {y : pts S}
    (hu : mapR φ u y) : evalAt pts mapR f y = φ (f p u) := by
  have hT : FromTest pts mapR y := ⟨p, φ, u, hu⟩
  unfold evalAt
  rw [dite_eq_left hT]
  exact hW f hf S _ _ _ _ _ _ y hT.choose_spec.choose_spec.choose_spec hu

variable [Fintype I]

/-- The source's integer-exponent homogeneous sections, in the constructed
rule ring. Naturality and the torus law are the defining conditions. -/
def secZ (e : I → ℤ) : Submodule K (Rules pts) where
  carrier := {f | IsNatural pts mapR f ∧
    ∀ (p : TestRing K) (t : I → (p.R)ˣ) (y y' : pts p.R),
      borR t y y' → f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by
       simp only [Pi.add_apply, hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun a f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by
       simp only [Pi.smul_apply, hf.2 p t y y' h, mul_smul_comm]⟩

theorem one_mem_secZ : (1 : Rules pts) ∈ secZ pts mapR borR (0 : I → ℤ) := by
  constructor
  · intro p q φ y z _
    exact (map_one φ).symm
  · intro p t y y' _
    simp

theorem mul_mem_secZ {e e' : I → ℤ} {f g : Rules pts}
    (hf : f ∈ secZ pts mapR borR e) (hg : g ∈ secZ pts mapR borR e') :
    f * g ∈ secZ pts mapR borR (e + e') := by
  constructor
  · intro p q φ y z h
    change f q z * g q z = φ (f p y * g p y)
    rw [hf.1 p q φ y z h, hg.1 p q φ y z h, map_mul]
  · intro p t y y' h
    change f p y' * g p y' = _ * (f p y * g p y)
    rw [hf.2 p t y y' h, hg.2 p t y y' h]
    simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
    ring

theorem secZ_mul_le (e e' : I → ℤ) :
    secZ pts mapR borR e * secZ pts mapR borR e' ≤ secZ pts mapR borR (e + e') :=
  Submodule.mul_le.2 fun _ hf _ hg => mul_mem_secZ pts mapR borR hf hg

/-- The source evaluation and base-change laws used by the atlas proof.
They concern actual points, maps, and the defining integer-weight spaces;
they contain no section-faithfulness or regularity conclusion. -/
structure EvaluationLaws : Prop where
  wd : EvalWD pts mapR
  test : ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra K S]
    (y : pts S), FromTest pts mapR y
  wt : ∀ e (f : Rules pts), f ∈ secZ pts mapR borR e →
    ∀ (L : Type) [Field L] [Algebra K L] (t : I → Lˣ) (y y' : pts L),
      borR t y y' → evalAt pts mapR f y' =
        nativeWeightTorusCharacter L e t * evalAt pts mapR f y
  bc : ∀ (S T : Type) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    (φ : S →ₐ[K] T) (y : pts S), ∃ z : pts T, mapR φ y z
  trans : ∀ (S T U : Type) [CommRing S] [Algebra K S]
    [CommRing T] [Algebra K T] [CommRing U] [Algebra K U]
    (φ : S →ₐ[K] T) (ψ : T →ₐ[K] U) (y : pts S) (z : pts T) (w : pts U),
    mapR φ y z → mapR ψ z w → mapR (ψ.comp φ) y w

variable {Z : Type} (F : Z → Type) [∀ z, Field (F z)] [∀ z, Algebra K (F z)]
  (genericPoint : ∀ z, pts (F z))

/-- The precise part of an original framed chart used in faithfulness.
The chart ring is a subalgebra of the same component's generic field. -/
structure GenericChart where
  component : Z
  R : Subalgebra K (F component)
  y : pts R
  yg : pts (F component)
  t : I → (F component)ˣ
  gen : mapR R.val y yg
  bor : borR t (genericPoint component) yg

/-- Every framed field point is reached from an actual chart and a torus
change of frame, exactly as in the original `GlobalTheory.Reg.Atlas`. -/
def Atlas : Prop :=
  ∀ (L : Type) [Field L] [Algebra K L] (y : pts L),
    ∃ (C : GenericChart pts mapR borR F genericPoint)
      (ψ : C.R →ₐ[K] L) (z : pts L) (t : I → Lˣ),
      mapR ψ C.y z ∧ borR t z y

/-- Generic vanishing first gives zero in the literal chart subalgebra.
No equality between the generic and specialized fields is used. -/
theorem chart_value_eq_zero
    (hL : EvaluationLaws pts mapR borR)
    (C : GenericChart pts mapR borR F genericPoint)
    {e : I → ℤ} {f : Rules pts} (hf : f ∈ secZ pts mapR borR e)
    (h0 : evalAt pts mapR f (genericPoint C.component) = 0)
    {p : TestRing K} {φ : p.R →ₐ[K] C.R} {u : pts p.R}
    (hu : mapR φ u C.y) : φ (f p u) = 0 := by
  have hgen : evalAt pts mapR f C.yg = C.R.val (φ (f p u)) := by
    exact evalAt_of_map pts mapR hL.wd hf.1
      (hL.trans _ _ _ φ C.R.val u C.y C.yg hu C.gen)
  have hwt := hL.wt e f hf (F C.component) C.t
    (genericPoint C.component) C.yg C.bor
  rw [h0, mul_zero, hgen] at hwt
  exact Subtype.ext hwt

/-- The same chart specializes homogeneous vanishing to any field point
which it reaches, including a complex point when the geometric atlas says so. -/
theorem evalAt_eq_zero_of_chart
    (hL : EvaluationLaws pts mapR borR)
    (C : GenericChart pts mapR borR F genericPoint)
    {e : I → ℤ} {f : Rules pts} (hf : f ∈ secZ pts mapR borR e)
    (h0 : evalAt pts mapR f (genericPoint C.component) = 0)
    {L : Type} [Field L] [Algebra K L] (ψ : C.R →ₐ[K] L)
    (z y : pts L) (t : I → Lˣ) (hψ : mapR ψ C.y z) (hb : borR t z y) :
    evalAt pts mapR f y = 0 := by
  obtain ⟨p, φ, u, hu⟩ := hL.test C.R C.y
  have hz : evalAt pts mapR f z = ψ (φ (f p u)) :=
    evalAt_of_map pts mapR hL.wd hf.1
      (hL.trans _ _ _ φ ψ u C.y z hu hψ)
  rw [hL.wt e f hf L t z y hb, hz,
    chart_value_eq_zero pts mapR borR F genericPoint hL C hf h0 hu,
    map_zero, mul_zero]

/-- The original homogeneous faithfulness theorem, with the universal
faithfulness premise removed and replaced by its actual atlas proof. -/
theorem secZ_eq_zero_of_generic
    (hL : EvaluationLaws pts mapR borR)
    (hA : Atlas pts mapR borR F genericPoint)
    {e : I → ℤ} {f : Rules pts} (hf : f ∈ secZ pts mapR borR e)
    (h0 : ∀ z, evalAt pts mapR f (genericPoint z) = 0) : f = 0 := by
  have hfield : ∀ (L : Type) [Field L] [Algebra K L] (y : pts L),
      evalAt pts mapR f y = 0 := by
    intro L _ _ y
    obtain ⟨C, ψ, z, t, hψ, hb⟩ := hA L y
    exact evalAt_eq_zero_of_chart pts mapR borR F genericPoint hL C hf
      (h0 C.component) ψ z y t hψ hb
  funext p u
  obtain ⟨a, ha⟩ : ∃ a, Ideal.Quotient.mk p.I a = f p u :=
    Ideal.Quotient.mk_surjective _
  change f p u = 0
  rw [← ha, Ideal.Quotient.eq_zero_iff_mem]
  have hJ : p.I.jacobson = p.I := IsJacobsonRing.out' _ p.rad
  rw [← hJ, Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨hIm, hm⟩
  have : Ideal.IsMaximal m := hm
  let : Field (MvPolynomial (Fin p.n) K ⧸ m) := Ideal.Quotient.field m
  let φ : p.R →ₐ[K] MvPolynomial (Fin p.n) K ⧸ m :=
    Ideal.Quotient.factorₐ K hIm
  obtain ⟨z, hz⟩ := hL.bc p.R _ φ u
  have hv := evalAt_of_map pts mapR hL.wd hf.1 hz
  rw [hfield _ z, ← ha] at hv
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact hv.symm

/-- The original generic evaluation map is constructed from the same tested
generic framed point used throughout the atlas. -/
def genericHom (hL : EvaluationLaws pts mapR borR) (z : Z) : Rules pts →+* F z :=
  evalHom pts mapR (genericPoint z) (hL.test (F z) (genericPoint z))

/-- Regularity in the constructed section algebra now consumes the actual
reduced-test-ring atlas proof instead of a free homogeneous-faithfulness input. -/
theorem section_regular_of_atlas
    [DecidableEq I] [∀ z, CharZero (F z)]
    (hL : EvaluationLaws pts mapR borR)
    (hA : Atlas pts mapR borR F genericPoint)
    (fr : ∀ z, (I → (F z)ˣ) → pts (F z))
    (hfr : ∀ z t, borR t (genericPoint z) (fr z t))
    (e : I → ℤ)
    (u : nativeGradedSectionAlgebra (secZ pts mapR borR)
      (one_mem_secZ pts mapR borR) (secZ_mul_le pts mapR borR))
    (hu : (u : Rules pts) ∈ secZ pts mapR borR e)
    (hgeneric : ∀ z, genericHom pts mapR borR F genericPoint hL z u ≠ 0) :
    u ∈ nonZeroDivisors (nativeGradedSectionAlgebra (secZ pts mapR borR)
      (one_mem_secZ pts mapR borR) (secZ_mul_le pts mapR borR)) := by
  apply nativeGradedSection_regular (secZ pts mapR borR)
    (one_mem_secZ pts mapR borR) (secZ_mul_le pts mapR borR)
    F (genericHom pts mapR borR F genericPoint hL)
    (fun z t => evalHom pts mapR (fr z t) (hL.test (F z) (fr z t)))
    (fun z d f hf t => hL.wt d f hf (F z) t (genericPoint z) (fr z t) (hfr z t))
    (fun d f hf h0 => secZ_eq_zero_of_generic pts mapR borR F genericPoint hL hA hf h0)
    e u hu hgeneric

end Rules
end RHLean.Geometry.NativeFramedRules

end
