import RHLean.Geometry.NativeCMLineBundleAtlas
import RHLean.Geometry.NativeCMWeierstrassProjSections
import RHLean.Geometry.NativeCMWeierstrassScheme

/-!
# The actual origin line bundle on the integral Weierstrass cubic

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean`
- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/ExistsUniqueEqConstMulOriginSec.lean`

The cover, unit transition, and canonical section are constructed from the SAME
projective cubic. The nonzero locus is exactly the affine chart. This module does
not claim the remaining ampleness, symmetry, rigidification, or principal-kernel
properties of the polarization.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

open RHLean.Geometry.NativeCM.SchemeTheory RHLean.Geometry.NativeCM.SchemeTheory.LB RHLean.Geometry.NativeCM.SchemeTheory.ProjFrac

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

def constOn (U : (scheme W).Opens) : R →+* Γ(scheme W, U) := (baseRingHom (toSpec W) U).hom

def ratioOn (U : (scheme W).Opens) (i : Fin 3) (hU : U ≤ coordOpen W i) (j : Fin 3) :
    Γ(scheme W, U) :=
  frac (grading W) U (coord W j) (coord W i) (coord_mem W j) (coord_mem W i) hU

abbrev ratio (i j : Fin 3) : Γ(scheme W, coordOpen W i) := ratioOn W (coordOpen W i) i le_rfl j

section

variable {W} {U V : (scheme W).Opens} {i j k : Fin 3}

theorem resG_constOn (h : V ≤ U) (r : R) : resG _ h (constOn W U r) = constOn W V r :=
  baseRingHom_res (toSpec W) h r

theorem resG_ratioOn (hi : U ≤ coordOpen W i) (h : V ≤ U) :
    resG _ h (ratioOn W U i hi j) = ratioOn W V i (h.trans hi) j := rfl

@[simp] theorem ratioOn_self (hi : U ≤ coordOpen W i) : ratioOn W U i hi i = 1 := frac_self

theorem ratioOn_mul_ratioOn (hi : U ≤ coordOpen W i) (hj : U ≤ coordOpen W j) :
    ratioOn W U i hi j * ratioOn W U j hj k = ratioOn W U i hi k :=
  frac_mul_eq (by ring)

theorem isUnit_ratioOn (hi : U ≤ coordOpen W i) (hj : U ≤ coordOpen W j) :
    IsUnit (ratioOn W U i hi j) :=
  IsUnit.of_mul_eq_one _ ((ratioOn_mul_ratioOn hi hj).trans (ratioOn_self hi))

theorem basicOpen_ratioOn (hi : U ≤ coordOpen W i) :
    (scheme W).basicOpen (ratioOn W U i hi j) = U ⊓ coordOpen W j :=
  basicOpen_frac

end

def awayFnEquiv (i : Fin 3) : AwayRing W i ≃+* Γ(scheme W, coordOpen W i) :=
  (Proj.basicOpenIsoAway (grading W) (coord W i) (coord_mem W i) one_pos).commRingCatIsoToRingEquiv

@[simp] theorem awayFnEquiv_awayCoord (i j : Fin 3) :
    awayFnEquiv W i (awayCoord W i j) = ratio W i j :=
  (awayToSection_mk (coord_mem W i) 1 (coord_mem W j)).trans (frac_eq (by ring))

@[simp] theorem awayFnEquiv_awayConst (i : Fin 3) (r : R) :
    awayFnEquiv W i (awayConst W i r) = constOn W (coordOpen W i) r := by
  have h := baseRingHom_comp_SpecMap (Proj.toSpecZero (grading W))
    (CommRingCat.ofHom (algebraMap R (grading W 0))) (coordOpen W i)
  have h' := toSpecZero_appLE_basicOpen (grading W) (coord_mem W i) one_pos
  exact (congrArg (fun φ => φ.hom r) (h.trans (congrArg (_ ≫ ·) h'))).symm

section

variable {W} {U : (scheme W).Opens} {i : Fin 3}

theorem equation_ratioOn (hi : U ≤ coordOpen W i) :
    (W.map (constOn W U)).toProjective.Equation (ratioOn W U i hi) := by
  have h := ((isUnimodularSol_awayCoord W i).map_comp
    ((resG _ hi).comp (awayFnEquiv W i : AwayRing W i →+* _))).equation
  have e₁ : ((resG _ hi).comp (awayFnEquiv W i : AwayRing W i →+* _)).comp (awayConst W i) =
      constOn W U := RingHom.ext fun r =>
    (congrArg (resG _ hi) (awayFnEquiv_awayConst W i r)).trans (resG_constOn hi r)
  have e₂ : ((resG _ hi).comp (awayFnEquiv W i : AwayRing W i →+* _)) ∘ awayCoord W i =
      ratioOn W U i hi := funext fun j => congrArg (resG _ hi) (awayFnEquiv_awayCoord W i j)
  rwa [e₁, e₂] at h

end


def originCofactor (U : (scheme W).Opens) (hU : U ≤ coordOpen W 1) : Γ(scheme W, U) :=
  1 + constOn W U W.a₁ * ratioOn W U 1 hU 0 + constOn W U W.a₃ * ratioOn W U 1 hU 2
    - constOn W U W.a₂ * ratioOn W U 1 hU 0 ^ 2
    - constOn W U W.a₄ * ratioOn W U 1 hU 0 * ratioOn W U 1 hU 2
    - constOn W U W.a₆ * ratioOn W U 1 hU 2 ^ 2

section

variable {W} {U V : (scheme W).Opens}

theorem resG_originCofactor (hU : U ≤ coordOpen W 1) (h : V ≤ U) :
    resG _ h (originCofactor W U hU) = originCofactor W V (h.trans hU) := by
  simp only [originCofactor, map_add, map_sub, map_mul, map_pow, map_one, resG_constOn,
    resG_ratioOn]

theorem ratioOn_mul_originCofactor (hU : U ≤ coordOpen W 1) :
    ratioOn W U 1 hU 2 * originCofactor W U hU = ratioOn W U 1 hU 0 ^ 3 := by
  have h := (WeierstrassCurve.Projective.equation_iff _).1 (equation_ratioOn hU)
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, ratioOn_self] at h
  rw [originCofactor]
  linear_combination h

end

def originOpen : (scheme W).Opens := (scheme W).basicOpen (originCofactor W (coordOpen W 1) le_rfl)

theorem originOpen_le : originOpen W ≤ coordOpen W 1 := (scheme W).basicOpen_le _

theorem isAffineOpen_originOpen : IsAffineOpen (originOpen W) :=
  (isAffineOpen_coordOpen W 1).basicOpen _

variable {W} in

theorem isUnit_originCofactor {U : (scheme W).Opens} (h : U ≤ originOpen W) :
    IsUnit (originCofactor W U (h.trans (originOpen_le W))) := by
  have : IsUnit (resG _ (originOpen_le W) (originCofactor W (coordOpen W 1) le_rfl)) :=
    (scheme W).toRingedSpace.isUnit_res_basicOpen _
  have := this.map (resG _ h)
  rwa [resG_originCofactor, resG_originCofactor] at this

theorem originOpen_sup_coordOpen_two : originOpen W ⊔ coordOpen W 2 = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  rcases (coordOpen_one_sup_coordOpen_two W).ge (Set.mem_univ x) with hx | hx
  swap
  · exact Or.inr hx
  have key : ∀ {S : Type} [CommRing S] [IsLocalRing S] (z w u a b : S), w * u = z ^ 3 →
      u + (z * a + w * b) = 1 → IsUnit u ∨ IsUnit w := by
    intro S _ _ z w u a b h₁ h₂
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one h₂ with h | h
    · exact Or.inl h
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
    · exact Or.inl (isUnit_of_mul_isUnit_right (h₁ ▸ (isUnit_of_mul_isUnit_left h).pow 3))
    · exact Or.inr (isUnit_of_mul_isUnit_left h)
  let γ := ((scheme W).presheaf.germ (coordOpen W 1) x hx).hom
  rcases key (γ (ratio W 1 0)) (γ (ratio W 1 2)) (γ (originCofactor W _ le_rfl))
    (γ (constOn W _ W.a₂ * ratio W 1 0 + constOn W _ W.a₄ * ratio W 1 2 - constOn W _ W.a₁))
    (γ (constOn W _ W.a₆ * ratio W 1 2 - constOn W _ W.a₃))
    (by rw [← map_mul, ratioOn_mul_originCofactor, map_pow])
    (by rw [← map_mul, ← map_mul, ← map_add, ← map_add, ← map_one γ, originCofactor]
        congr 1
        ring) with h | h
  · exact Or.inl (((scheme W).mem_basicOpen _ x hx).2 h)
  · exact Or.inr ((basicOpen_ratioOn le_rfl).le (((scheme W).mem_basicOpen _ x hx).2 h)).2

abbrev originParam : Γ(scheme W, originOpen W) := ratioOn W (originOpen W) 1 (originOpen_le W) 0

variable {W} in

theorem isUnit_ratioOn_one_zero {U : (scheme W).Opens} (h₀ : U ≤ originOpen W)
    (h₁ : U ≤ coordOpen W 2) : IsUnit (ratioOn W U 1 (h₀.trans (originOpen_le W)) 0) := by
  rw [← isUnit_pow_iff three_ne_zero, ← ratioOn_mul_originCofactor]
  exact (isUnit_ratioOn _ h₁).mul (isUnit_originCofactor h₀)

theorem basicOpen_originParam :
    (scheme W).basicOpen (originParam W) = originOpen W ⊓ coordOpen W 2 := by
  rw [← (scheme W).basicOpen_pow _ three_pos, ← ratioOn_mul_originCofactor, Scheme.basicOpen_mul,
    basicOpen_ratioOn, (scheme W).basicOpen_of_isUnit (isUnit_originCofactor le_rfl)]
  exact inf_eq_left.2 inf_le_left


def originUnit : Γ(scheme W, originOpen W ⊓ coordOpen W 2)ˣ :=
  (isUnit_ratioOn_one_zero inf_le_left inf_le_right).unit

@[simp] theorem val_originUnit : (originUnit W : Γ(scheme W, originOpen W ⊓ coordOpen W 2)) =
    ratioOn W _ 1 (inf_le_left.trans (originOpen_le W)) 0 := rfl

def originLB : LB (scheme W) := twoChart (originOpen W) (coordOpen W 2) (originUnit W)

@[simp] theorem originLB_U_true : (originLB W).U true = originOpen W := rfl

@[simp] theorem originLB_U_false : (originLB W).U false = coordOpen W 2 := rfl

@[simp] theorem originLB_g_true_false : (originLB W).g true false = originUnit W := rfl

theorem originLB_isLB : (originLB W).IsLB := twoChart_isLB (originOpen_sup_coordOpen_two W) _

def originSecMk (f₀ : Γ(scheme W, originOpen W)) (f₁ : Γ(scheme W, coordOpen W 2))
    (h : resG _ inf_le_left f₀ = (originUnit W : Γ(scheme W, originOpen W ⊓ coordOpen W 2)) *
      resG _ inf_le_right f₁) : (originLB W).Sec :=
  twoChartSec (originUnit W) f₀ f₁ h

def originSec : (originLB W).Sec :=
  originSecMk W (originParam W) 1 (by rw [map_one, mul_one]; rfl)

@[simp] theorem originSec_f_true : (originSec W).f true = originParam W := rfl

@[simp] theorem originSec_f_false : (originSec W).f false = (1 : Γ(scheme W, coordOpen W 2)) := rfl


theorem nonzeroLocus_originSec : nonzeroLocus (originSec W) = coordOpen W 2 := by
  refine le_antisymm (iSup_le ?_) ?_
  · rintro (_ | _)
    · exact (scheme W).basicOpen_le _
    · exact (basicOpen_originParam W).le.trans inf_le_right
  · exact ((scheme W).basicOpen_of_isUnit (isUnit_one (M := Γ(scheme W, coordOpen W 2)))).ge.trans
      (basicOpen_le_nonzeroLocus (originSec W) false)

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve
