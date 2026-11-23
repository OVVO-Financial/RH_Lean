import RHLean.Geometry.NativeCMLineBundleAtlas

/-!
# Regular sections on the actual line-bundle charts

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean`

Regularity means non-zero-divisors on every restricted open, and is proved
equivalent to the stalk and affine-chart conditions. These are actual rings of
scheme sections, used below for the origin divisor.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace RHLean.Geometry.NativeCM.SchemeTheory.Cartier

open RHLean.Geometry.NativeCM.SchemeTheory

variable {X Y Z : Scheme.{0}}

theorem germ_resG {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (a : Γ(X, U)) :
    (X.presheaf.germ V x hx).hom (resG X h a) = (X.presheaf.germ U x (h hx)).hom a :=
  X.presheaf.germ_res_apply (homOfLE h) x hx a

theorem ext_germ {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ x (hx : x ∈ U), (X.presheaf.germ U x hx).hom a = (X.presheaf.germ U x hx).hom b) :
    a = b :=
  TopCat.Presheaf.section_ext X.sheaf U a b h

theorem app_resG (φ : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (φ.app V).hom (resG X h a) = resG Y (φ.preimage_mono h) ((φ.app U).hom a) := by
  change ((X.presheaf.map (homOfLE h).op ≫ φ.app V).hom) a = _
  rw [Scheme.Hom.naturality]
  rfl

def IsRegularFn {U : X.Opens} (a : Γ(X, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), resG X h a ∈ nonZeroDivisors Γ(X, V)

namespace IsRegularFn

variable {U : X.Opens} {a b : Γ(X, U)}

theorem mem (ha : IsRegularFn a) : a ∈ nonZeroDivisors Γ(X, U) := by
  have := ha U le_rfl
  rwa [resG_self] at this

theorem resG (ha : IsRegularFn a) {V : X.Opens} (h : V ≤ U) : IsRegularFn (resG X h a) :=
  fun W hW => by rw [resG_resG]; exact ha W _

theorem mul (ha : IsRegularFn a) (hb : IsRegularFn b) : IsRegularFn (a * b) :=
  fun W hW => by rw [map_mul]; exact mul_mem (ha W hW) (hb W hW)

theorem pow (ha : IsRegularFn a) (n : ℕ) : IsRegularFn (a ^ n) :=
  fun W hW => by rw [map_pow]; exact pow_mem (ha W hW) n

theorem of_isUnit (ha : IsUnit a) : IsRegularFn a :=
  fun _ hW => (ha.map (RHLean.Geometry.NativeCM.SchemeTheory.resG X hW)).mem_nonZeroDivisors

theorem of_dvd (hb : IsRegularFn b) (h : a ∣ b) : IsRegularFn a := fun W hW => by
  obtain ⟨c, rfl⟩ := h
  have := hb W hW
  rw [map_mul] at this
  exact (mul_mem_nonZeroDivisors.1 this).1

theorem mul_right_cancel (ha : IsRegularFn a) {c d : Γ(X, U)} (h : c * a = d * a) : c = d :=
  (mul_cancel_right_mem_nonZeroDivisors ha.mem).1 h

end IsRegularFn

theorem isRegularFn_iff_germ {U : X.Opens} {a : Γ(X, U)} :
    IsRegularFn a ↔ ∀ x (hx : x ∈ U),
      (X.presheaf.germ U x hx).hom a ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  constructor
  · intro ha x hx
    refine mem_nonZeroDivisors_iff_right.2 fun t ht => ?_
    obtain ⟨V, hV, b, rfl⟩ := X.presheaf.exists_germ_eq t
    have hm : x ∈ U ⊓ V := ⟨hx, hV⟩
    have e : (X.presheaf.germ (U ⊓ V) x hm).hom (resG X inf_le_right b * resG X inf_le_left a) =
        (X.presheaf.germ (U ⊓ V) x hm).hom 0 := by
      rw [map_mul, germ_resG, germ_resG, map_zero]; exact ht
    obtain ⟨W, hW, i₁, i₂, e'⟩ := X.presheaf.germ_eq x hm hm _ _ e
    have le : W ≤ U ⊓ V := i₁.le
    have e'' : resG X le (resG X inf_le_right b * resG X inf_le_left a) = resG X le 0 := e'
    rw [map_mul, resG_resG, resG_resG, map_zero] at e''
    have hb := mem_nonZeroDivisors_iff_right.1 (ha W _) _ e''
    rw [← germ_resG (le.trans inf_le_right) x hW b, hb, map_zero]
  · intro h V hV
    refine mem_nonZeroDivisors_iff_right.2 fun t ht => ext_germ fun x hx => ?_
    have := congrArg (X.presheaf.germ V x hx).hom ht
    rw [map_mul, germ_resG, map_zero] at this
    rw [map_zero]
    exact mem_nonZeroDivisors_iff_right.1 (h x (hV hx)) _ this

theorem isRegularFn_of_locally {U : X.Opens} {a : Γ(X, U)}
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ IsRegularFn (resG X hV a)) :
    IsRegularFn a := by
  refine isRegularFn_iff_germ.2 fun x hx => ?_
  obtain ⟨V, hV, hxV, hr⟩ := h x hx
  have := isRegularFn_iff_germ.1 hr x hxV
  rwa [germ_resG] at this

theorem isRegularFn_iff_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U) {a : Γ(X, U)} :
    IsRegularFn a ↔ a ∈ nonZeroDivisors Γ(X, U) := by
  refine ⟨IsRegularFn.mem, fun ha => isRegularFn_iff_germ.2 fun x hx => ?_⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.nonZeroDivisors_le_comap (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) ha

def IsRegularSec {L : LB X} (s : L.Sec) : Prop := ∀ i, IsRegularFn (s.f i)

end RHLean.Geometry.NativeCM.SchemeTheory.Cartier
