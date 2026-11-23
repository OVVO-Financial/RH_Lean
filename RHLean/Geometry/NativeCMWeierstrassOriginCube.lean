import RHLean.Geometry.NativeCMLineBundlePowers
import RHLean.Geometry.NativeCMWeierstrassOriginDivisor

/-!
# Three actual coordinate sections of the cubed origin bundle

Native declaration cuts from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/ExistsUniqueEqConstMulOriginSec.lean`

The three sections of the cube of the original origin bundle have exactly
the projective coordinate opens as nonzero loci. Their literal ratios are the
projective coordinate ratios. This is the explicit section input for relative
ampleness of the same integral seed, not an ampleness hypothesis.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open scoped BigOperators

namespace RHLean.Geometry.NativeCM.SchemeTheory

variable {X Y Z : Scheme.{0}}

open LBGerm LB

namespace WeierstrassCurve

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

def coordFn (j : Fin 3) : ∀ i, Γ(scheme W, (originLB W).U i) :=
  twoChartFn (originUnit W)
    (originCofactor W _ (originOpen_le W) * ratioOn W _ 1 (originOpen_le W) j) (ratio W 2 j)

theorem coordFn_overlap (j : Fin 3) :
    resG _ (inf_le_left : originOpen W ⊓ coordOpen W 2 ≤ _)
        (originCofactor W _ (originOpen_le W) * ratioOn W _ 1 (originOpen_le W) j) =
      (originUnit W : Γ(scheme W, originOpen W ⊓ coordOpen W 2)) ^ 3 *
        resG _ inf_le_right (ratio W 2 j) := by
  rw [map_mul, resG_originCofactor, resG_ratioOn, resG_ratioOn, val_originUnit,
    ← ratioOn_mul_originCofactor, mul_right_comm, ratioOn_mul_ratioOn, mul_comm]

theorem coordFn_compat (j : Fin 3) (i k : (originLB W).ι) :
    resG _ (inf_le_left : (originLB W).U i ⊓ (originLB W).U k ≤ _) (coordFn W j i) =
      ((originLB W).g i k).val ^ 3 * resG _ inf_le_right (coordFn W j k) :=
  twoChartFn_compat (originUnit W) 3 (coordFn_overlap W j) i k

def coordSec (j : Fin 3) : (lbPow (originLB W) 3).Sec :=
  powSecMk 3 (coordFn W j) (coordFn_compat W j)

@[simp] theorem powSecFn_coordSec (j : Fin 3) (i : (originLB W).ι) :
    powSecFn (coordSec W j) i = coordFn W j i :=
  (resG_resG _ _ _).trans (resG_self _ _)

theorem basicOpen_coordFn (j : Fin 3) : ∀ i,
    (scheme W).basicOpen (coordFn W j i) = (originLB W).U i ⊓ coordOpen W j
  | true => by
    change (scheme W).basicOpen (originCofactor W _ (originOpen_le W) *
      ratioOn W _ 1 (originOpen_le W) j) = originOpen W ⊓ coordOpen W j
    rw [Scheme.basicOpen_mul, basicOpen_ratioOn, (scheme W).basicOpen_of_isUnit (isUnit_originCofactor le_rfl)]
    exact inf_eq_right.2 inf_le_left
  | false => basicOpen_ratioOn le_rfl

theorem nonzeroLocus_coordSec (j : Fin 3) : nonzeroLocus (coordSec W j) = coordOpen W j := by
  rw [coordSec, nonzeroLocus_powSecMk]
  simp only [basicOpen_coordFn]
  rw [← iSup_inf_eq, (originLB_isLB W).cover, top_inf_eq]

variable {W} in

theorem resG_coordFn {V : (scheme W).Opens} {i : Fin 3} (hi : V ≤ coordOpen W i) (j : Fin 3) :
    ∀ (k : (originLB W).ι) (hk : V ≤ (originLB W).U k),
      resG _ hk (coordFn W j k) = ratioOn W V i hi j * resG _ hk (coordFn W i k)
  | true, hk => by
    have e : ∀ l, resG _ hk (coordFn W l true) = originCofactor W V (hk.trans (originOpen_le W)) *
        ratioOn W V 1 (hk.trans (originOpen_le W)) l := fun l =>
      (map_mul (resG _ hk) _ _).trans (congrArg (· * _) (resG_originCofactor (originOpen_le W) hk))
    rw [e, e, ← ratioOn_mul_ratioOn (hk.trans (originOpen_le W)) hi]
    ring
  | false, hk => (ratioOn_mul_ratioOn (U := V) (i := 2) hk hi).symm.trans (mul_comm _ _)

variable {W} in

theorem gs_coordFn {Z : Scheme.{0}} (r : Z ⟶ scheme W) (z : Z) {i : Fin 3} (j : Fin 3)
    {k : (originLB W).ι} (hi : r z ∈ coordOpen W i) (hk : r z ∈ (originLB W).U k) :
    gs r z _ (coordFn W j k) = gs r z _ (ratio W i j) * gs r z _ (coordFn W i k) := by
  have hm : r z ∈ coordOpen W i ⊓ (originLB W).U k := ⟨hi, hk⟩
  have e := congrArg (gs r z _) (resG_coordFn (i := i) inf_le_left j k inf_le_right)
  rwa [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, ← resG_ratioOn le_rfl inf_le_left,
    gs_res _ z _ hm] at e

end WeierstrassCurve

end RHLean.Geometry.NativeCM.SchemeTheory
