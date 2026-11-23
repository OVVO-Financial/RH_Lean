import RHLean.Geometry.NativeCMLineBundleAtlas

/-!
# Sections of the actual homogeneous-localization charts

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean`
- `src/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean`

The fractions are actual sections of Proj and their basic opens are proved exactly.
Only the section and structure-map cut required by the origin bundle is included.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

open RHLean.Geometry.NativeCM.SchemeTheory

namespace RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

instance isPrime_point (x : Proj 𝒜) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  ProjectiveSpectrum.isPrime x

def ev (U : (Proj 𝒜).Opens) (x : Proj 𝒜) (hx : x ∈ U) :
    Γ(Proj 𝒜, U) →+* Localization.AtPrime x.asHomogeneousIdeal.toIdeal :=
  (algebraMap (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) _).comp
    (openToLocalization 𝒜 U x hx).hom

variable {𝒜}

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in

theorem _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ext {U : (Proj 𝒜).Opens} {s t : Γ(Proj 𝒜, U)}
    (h : ∀ x hx, _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev 𝒜 U x hx s =
      _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev 𝒜 U x hx t) : s = t := by
  refine Subtype.ext (funext fun y => HomogeneousLocalization.val_injective _ ?_)
  exact h y.1 y.2

theorem ev_resG {U V : (Proj 𝒜).Opens} (h : V ≤ U) (x : Proj 𝒜) (hx : x ∈ V) (s : Γ(Proj 𝒜, U)) :
    ev 𝒜 V x hx (resG (Proj 𝒜) h s) = ev 𝒜 U x (h hx) s := rfl

theorem mem_basicOpen_iff {U : (Proj 𝒜).Opens} (s : Γ(Proj 𝒜, U)) (x : Proj 𝒜) (hx : x ∈ U) :
    x ∈ (Proj 𝒜).basicOpen s ↔ IsUnit (ev 𝒜 U x hx s) := by
  rw [Scheme.mem_basicOpen _ _ _ hx]
  refine Iff.trans ?_ (HomogeneousLocalization.isUnit_iff_isUnit_val 𝒜 x.asHomogeneousIdeal.toIdeal
    (s.1 ⟨x, hx⟩)).symm
  rw [← Proj.stalkIso'_germ 𝒜 U x hx s]
  exact (isUnit_map_iff (Proj.stalkIso' 𝒜 x) _).symm

variable (𝒜) in

def frac (U : (Proj 𝒜).Opens) {d : ℕ} (a b : A) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (hU : U ≤ Proj.basicOpen 𝒜 b) : Γ(Proj 𝒜, U) :=
  ⟨fun y => HomogeneousLocalization.mk ⟨d, ⟨a, ha⟩, ⟨b, hb⟩, hU y.2⟩, fun y =>
    ⟨U, y.2, 𝟙 _, d, ⟨a, ha⟩, ⟨b, hb⟩, _, fun _ => rfl⟩⟩

section

variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b} {hU' : U ≤ Proj.basicOpen 𝒜 b'}

theorem ev_frac (x : Proj 𝒜) (hx : x ∈ U) :
    ev 𝒜 U x hx (frac 𝒜 U a b ha hb hU) = Localization.mk a ⟨b, hU hx⟩ := rfl

theorem ev_frac_mul_den (x : Proj 𝒜) (hx : x ∈ U) :
    ev 𝒜 U x hx (frac 𝒜 U a b ha hb hU) * algebraMap A _ b = algebraMap A _ a := by
  rw [ev_frac, Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec _ a (⟨b, hU hx⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)

theorem resG_frac (h : V ≤ U) :
    resG (Proj 𝒜) h (frac 𝒜 U a b ha hb hU) = frac 𝒜 V a b ha hb (h.trans hU) := rfl

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac_eq (h : a * b' = a' * b) :
    _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a b ha hb hU =
      _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a' b' ha' hb' hU' := by
  refine _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ext fun x hx => ?_
  rw [_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac, _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; linear_combination h⟩

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac_mul :
    _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a b ha hb hU *
        _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a' b' ha' hb' hU' =
      _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U (a * a') (b * b') (SetLike.mul_mem_graded ha ha')
        (SetLike.mul_mem_graded hb hb') (by rw [Proj.basicOpen_mul]; exact le_inf hU hU') := by
  refine _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ext fun x hx => ?_
  rw [map_mul, _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac, _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac,
    _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac, Localization.mk_mul]
  rfl

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac_mul_eq {d'' : ℕ} {a'' b'' : A} {ha'' : a'' ∈ 𝒜 d''}
    {hb'' : b'' ∈ 𝒜 d''} {hU'' : U ≤ Proj.basicOpen 𝒜 b''} (h : a * a' * b'' = a'' * (b * b')) :
    _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a b ha hb hU *
        _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a' b' ha' hb' hU' =
      _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a'' b'' ha'' hb'' hU'' :=
  _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac_mul.trans (_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac_eq h)

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac_add {a₂ : A} {ha₂ : a₂ ∈ 𝒜 d} :
    _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U (a + a₂) b (add_mem ha ha₂) hb hU =
      _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a b ha hb hU +
        _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a₂ b ha₂ hb hU := by
  refine _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ext fun x hx => ?_
  rw [map_add, _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac, _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac,
    _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac, Localization.add_mk_self]

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac_self :
    _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U b b hb hb hU = 1 := by
  refine _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ext fun x hx => ?_
  rw [map_one, _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac]
  exact Localization.mk_self (⟨b, hU hx⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac_zero :
    _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U 0 b (zero_mem _) hb hU = 0 := by
  refine _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ext fun x hx => ?_
  rw [map_zero, _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac, Localization.mk_zero]

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac_pow (n : ℕ) :
    _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a b ha hb hU ^ n =
      _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U (a ^ n) (b ^ n) (SetLike.pow_mem_graded n ha)
        (SetLike.pow_mem_graded n hb) (fun x hx h => hU hx (x.isPrime.mem_of_pow_mem n h)) := by
  refine _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ext fun x hx => ?_
  rw [map_pow, _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac, Localization.mk_pow]
  exact (_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac (a := a ^ n) (b := b ^ n)
    (ha := SetLike.pow_mem_graded n ha) (hb := SetLike.pow_mem_graded n hb)
    (hU := fun x hx h => hU hx (x.isPrime.mem_of_pow_mem n h)) x hx).symm

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.basicOpen_frac :
    (Proj 𝒜).basicOpen (_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a b ha hb hU) =
      U ⊓ Proj.basicOpen 𝒜 a := by
  ext x
  constructor
  · intro hx
    have hVU : (Proj 𝒜).basicOpen (_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a b ha hb hU) ≤ U :=
      (Proj 𝒜).basicOpen_le _
    have hxU : x ∈ U := hVU hx
    have hres : IsUnit (_root_.RHLean.Geometry.NativeCM.SchemeTheory.resG (Proj 𝒜) hVU (_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a b ha hb hU)) :=
      (Proj 𝒜).toRingedSpace.isUnit_res_basicOpen _
    have hunit := hres.map (_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev 𝒜 _ x hx)
    have heq : _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev 𝒜 _ x hx
        (_root_.RHLean.Geometry.NativeCM.SchemeTheory.resG (Proj 𝒜) hVU (_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a b ha hb hU)) =
        Localization.mk a ⟨b, hU hxU⟩ :=
      (_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_resG hVU x hx _).trans
        (_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.ev_frac x hxU)
    rw [heq] at hunit
    have hnum : IsUnit (algebraMap A (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) a) := by
      rw [← IsLocalization.mk'_spec (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) a
        (⟨b, hU hxU⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl), ← Localization.mk_eq_mk']
      exact hunit.mul (IsLocalization.map_units _ _)
    exact ⟨hxU, (IsLocalization.AtPrime.isUnit_to_map_iff _ _ a).1 hnum⟩
  · rintro ⟨hxU, hxa⟩
    have hWU : U ⊓ Proj.basicOpen 𝒜 a ≤ U := inf_le_left
    have hunit : IsUnit (_root_.RHLean.Geometry.NativeCM.SchemeTheory.resG (Proj 𝒜) hWU
        (_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 U a b ha hb hU)) := by
      rw [_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.resG_frac]
      exact IsUnit.of_mul_eq_one (_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac 𝒜 _ b a hb ha inf_le_right)
        ((_root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac_mul_eq (a'' := a) (b'' := a) (ha'' := ha) (hb'' := ha)
          (hU'' := inf_le_right) (by ring)).trans _root_.RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac.frac_self)
    have hb := (Proj 𝒜).basicOpen_of_isUnit hunit
    have hx : x ∈ U ⊓ Proj.basicOpen 𝒜 a := ⟨hxU, hxa⟩
    rw [← hb] at hx
    exact ((Proj 𝒜).basicOpen_res _ (homOfLE hWU).op ▸ hx).2

end

variable (𝒜) in

def fracUnit (U : (Proj 𝒜).Opens) {d : ℕ} (a b : A) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (hUa : U ≤ Proj.basicOpen 𝒜 a) (hUb : U ≤ Proj.basicOpen 𝒜 b) : Γ(Proj 𝒜, U)ˣ where
  val := frac 𝒜 U a b ha hb hUb
  inv := frac 𝒜 U b a hb ha hUa
  val_inv := (frac_mul_eq (by ring)).trans (frac_self (hb := ha) (hU := hUa))
  inv_val := (frac_mul_eq (by ring)).trans (frac_self (hb := ha) (hU := hUa))

theorem awayToSection_mk {f a : A} {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (ha : a ∈ 𝒜 (n • d)) :
    (Proj.awayToSection 𝒜 f).hom (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
      frac 𝒜 (Proj.basicOpen 𝒜 f) a (f ^ n) ha (SetLike.pow_mem_graded n hf)
        (fun x hx h => hx (x.isPrime.mem_of_pow_mem n h)) := rfl

theorem awayToSection_fromZero (f : A) (a : 𝒜 0) :
    (Proj.awayToSection 𝒜 f).hom (HomogeneousLocalization.fromZeroRingHom 𝒜 _ a) =
      frac 𝒜 (Proj.basicOpen 𝒜 f) a 1 a.2 (SetLike.one_mem_graded 𝒜) (by simp) := rfl


end RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac

namespace RHLean.Geometry.NativeCM.SchemeTheory

section Proj

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem toSpecZero_appLE_basicOpen {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫ (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top =
      CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫ Proj.awayToSection 𝒜 f := by
  have hg : Proj.basicOpenToSpec 𝒜 f ≫ Proj.awayι 𝒜 f f_deg hm = (Proj.basicOpen 𝒜 f).ι := by
    show (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom ≫
      ((Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι) = _
    rw [Iso.hom_inv_id_assoc]
  have hB : (Proj.basicOpen 𝒜 f).ι ≫ Proj.toSpecZero 𝒜 = Proj.basicOpenToSpec 𝒜 f ≫
      Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f))) := by
    rw [← Proj.awayι_toSpecZero 𝒜 f f_deg hm, ← Category.assoc, hg]
  have h1 : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top ≫
      (Proj.basicOpen 𝒜 f).topIso.inv =
      (Proj.toSpecZero 𝒜).appTop ≫ (Proj.basicOpen 𝒜 f).ι.appTop := by
    rw [Scheme.Opens.topIso_inv]
    erw [Scheme.Hom.appLE_map]
  have h2 : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top ≫
      (Proj.basicOpen 𝒜 f).topIso.inv =
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).hom ≫
        CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫ Proj.awayToSection 𝒜 f) ≫
        (Proj.basicOpen 𝒜 f).topIso.inv := by
    rw [h1, ← Scheme.Hom.comp_appTop, hB, Scheme.Hom.comp_appTop]
    have hA : Scheme.Hom.appTop (Proj.basicOpenToSpec 𝒜 f) =
        (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom ≫
          Proj.awayToSection 𝒜 f ≫ (Proj.basicOpen 𝒜 f).topIso.inv :=
      Proj.basicOpenToSpec_app_top 𝒜 f
    rw [hA]
    rw [← Category.assoc, Scheme.ΓSpecIso_naturality]
    simp only [Category.assoc]
  have h3 := (cancel_mono (Proj.basicOpen 𝒜 f).topIso.inv).1 h2
  rw [h3, Iso.inv_hom_id_assoc]

end Proj

end RHLean.Geometry.NativeCM.SchemeTheory
