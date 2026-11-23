import RHLean.Geometry.NativeCMWeierstrassNormalizedModel
import RHLean.Geometry.NativeCMWeierstrassPeriodUniqueness

/-!
# The actual equation's periods in its integral tangent coordinate

For an arbitrary exact comparison C of an equation W with a period curve,
the period lattice in W's integral tangent coordinate is u^-1 times the
original lattice. Its invariants are c4(W)/12 and c6(W)/216. The comparison
back to the same W is the already constructed translation `shortChange W`.
The original exponential is recovered at u*z, and the actual origin bundle
has tangent direction one in this reparametrized uniformization.

The covolume identity retains the original u and proves the exact equality
with pi*|u|^2/covol(L). When W has discriminant one, the normalized periods
also have discriminant one and their log covolume is the original exact
logarithmic period. No algebraicity of u, ideal-isogeny derivative, or
arithmetic class mean is assumed.

This is native glue generalizing the actual coordinate calculation in
`NativeCMWeierstrassCMAction` and `NativeCMWeierstrassNormalizedModel` to
every period pair, together with the lattice uniqueness and actual
Appell--Humbert suppliers already attributed in the imported leaves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open PeriodPair NumberField

namespace RHLean.Geometry.NativeCM.Weierstrass

variable (L : PeriodPair) (C : _root_.WeierstrassCurve.VariableChange ℂ)

/-- Periods in the integral tangent coordinate, with the original u retained. -/
def tangentCoordinatePeriods : PeriodPair :=
  scalePeriods L (C.u : ℂ)⁻¹ (inv_ne_zero C.u.ne_zero)

theorem tangentCoordinatePeriods_mem (z : ℂ) :
    z ∈ (tangentCoordinatePeriods L C).lattice ↔ (C.u : ℂ) * z ∈ L.lattice := by
  have h := isHomothetic_scalePeriods L (C.u : ℂ)⁻¹
    (inv_ne_zero C.u.ne_zero) ((C.u : ℂ) * z)
  simpa only [tangentCoordinatePeriods, inv_mul_cancel_left₀ C.u.ne_zero] using h

theorem tangentCoordinatePeriods_g₂ :
    (tangentCoordinatePeriods L C).g₂ = (C.u : ℂ) ^ 4 * L.g₂ := by
  have h := (isHomothetic_scalePeriods L (C.u : ℂ)⁻¹
    (inv_ne_zero C.u.ne_zero)).g₂_eq
  simpa only [tangentCoordinatePeriods, inv_pow, inv_inv] using h

theorem tangentCoordinatePeriods_g₃ :
    (tangentCoordinatePeriods L C).g₃ = (C.u : ℂ) ^ 6 * L.g₃ := by
  have h := (isHomothetic_scalePeriods L (C.u : ℂ)⁻¹
    (inv_ne_zero C.u.ne_zero)).g₃_eq
  simpa only [tangentCoordinatePeriods, inv_pow, inv_inv] using h

theorem tangentCoordinatePeriods_weierstrassP (z : ℂ) :
    ℘[tangentCoordinatePeriods L C] z = (C.u : ℂ) ^ 2 * ℘[L] ((C.u : ℂ) * z) := by
  have h := (isHomothetic_scalePeriods L (C.u : ℂ)⁻¹
    (inv_ne_zero C.u.ne_zero)).weierstrassP_mul ((C.u : ℂ) * z)
  simpa only [tangentCoordinatePeriods, inv_mul_cancel_left₀ C.u.ne_zero,
    inv_pow, inv_inv] using h

theorem tangentCoordinatePeriods_derivWeierstrassP (z : ℂ) :
    ℘'[tangentCoordinatePeriods L C] z = (C.u : ℂ) ^ 3 * ℘'[L] ((C.u : ℂ) * z) := by
  have h := (isHomothetic_scalePeriods L (C.u : ℂ)⁻¹
    (inv_ne_zero C.u.ne_zero)).derivWeierstrassP_mul ((C.u : ℂ) * z)
  simpa only [tangentCoordinatePeriods, inv_mul_cancel_left₀ C.u.ne_zero,
    inv_pow, inv_inv] using h

variable (W : _root_.WeierstrassCurve ℂ) (hC : C • W = latticeCurve L)

include hC in
theorem tangentCoordinatePeriods_g₂_eq_invariant :
    (tangentCoordinatePeriods L C).g₂ = W.c₄ / 12 := by
  have h4 : (C.u : ℂ) ^ 4 * (latticeCurve L).c₄ = W.c₄ := by
    rw [← hC, _root_.WeierstrassCurve.variableChange_c₄, ← mul_assoc, ← mul_pow]
    simp
  rw [latticeCurve_c₄] at h4
  rw [tangentCoordinatePeriods_g₂]
  apply (eq_div_iff (by norm_num : (12 : ℂ) ≠ 0)).2
  linear_combination h4

include hC in
theorem tangentCoordinatePeriods_g₃_eq_invariant :
    (tangentCoordinatePeriods L C).g₃ = W.c₆ / 216 := by
  have h6 : (C.u : ℂ) ^ 6 * (latticeCurve L).c₆ = W.c₆ := by
    rw [← hC, _root_.WeierstrassCurve.variableChange_c₆, ← mul_assoc, ← mul_pow]
    simp
  rw [latticeCurve_c₆] at h6
  rw [tangentCoordinatePeriods_g₃]
  apply (eq_div_iff (by norm_num : (216 : ℂ) ≠ 0)).2
  linear_combination h6

include hC in
theorem shortModel_eq_tangentCoordinate_latticeCurve :
    shortModel W = latticeCurve (tangentCoordinatePeriods L C) := by
  ext
  · rfl
  · rfl
  · rfl
  · change -W.c₄ / 48 = -(tangentCoordinatePeriods L C).g₂ / 4
    rw [tangentCoordinatePeriods_g₂_eq_invariant L C W hC]
    ring
  · change -W.c₆ / 864 = -(tangentCoordinatePeriods L C).g₃ / 4
    rw [tangentCoordinatePeriods_g₃_eq_invariant L C W hC]
    ring

include hC in
theorem shortChange_eq_tangentCoordinate_latticeCurve :
    shortChange W • W = latticeCurve (tangentCoordinatePeriods L C) :=
  (shortChange_spec W).trans (shortModel_eq_tangentCoordinate_latticeCurve L C W hC)

include hC in
theorem tangentCoordinatePeriods_discriminant :
    (tangentCoordinatePeriods L C).g₂ ^ 3 -
      27 * (tangentCoordinatePeriods L C).g₃ ^ 2 = W.Δ := by
  rw [← latticeCurve_Δ, ← shortChange_eq_tangentCoordinate_latticeCurve L C W hC,
    _root_.WeierstrassCurve.variableChange_Δ, shortChange_u]
  simp

/-- The normalized lattice is determined by the same equation, independently
of the original analytic comparison choices. -/
include hC in
theorem tangentCoordinatePeriods_lattice_eq (L' : PeriodPair)
    (C' : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC' : C' • W = latticeCurve L') :
    (tangentCoordinatePeriods L C).lattice = (tangentCoordinatePeriods L' C').lattice := by
  apply lattice_eq_of_g₂_eq_of_g₃_eq
  · rw [tangentCoordinatePeriods_g₂_eq_invariant L C W hC,
      tangentCoordinatePeriods_g₂_eq_invariant L' C' W hC']
  · rw [tangentCoordinatePeriods_g₃_eq_invariant L C W hC,
      tangentCoordinatePeriods_g₃_eq_invariant L' C' W hC']

/-- This is the same equation's actual exponential, at the exact scaled
parameter u*z. The original coordinate-change unit has not been discarded. -/
theorem tangentCoordinate_exponential_eq (z : ℂ) :
    AllPlaceTangentPeriod.exponential (tangentCoordinatePeriods L C) W (shortChange W)
      (shortChange_eq_tangentCoordinate_latticeCurve L C W hC) z =
    AllPlaceTangentPeriod.exponential L W C hC ((C.u : ℂ) * z) := by
  by_cases hz : z ∈ (tangentCoordinatePeriods L C).lattice
  · have hz' := (tangentCoordinatePeriods_mem L C z).1 hz
    rw [(AllPlaceTangentPeriod.exponential_ker _ _ _ _ z).2 hz,
      (AllPlaceTangentPeriod.exponential_ker _ _ _ _ _).2 hz']
  · have hz' : (C.u : ℂ) * z ∉ L.lattice :=
      fun h => hz ((tangentCoordinatePeriods_mem L C z).2 h)
    obtain ⟨hr, hs, ht⟩ := variableChange_translations W L C hC
    rw [AllPlaceTangentPeriod.exponential_apply,
      AllPlaceTangentPeriod.exponential_apply,
      latticePoint_of_notMem _ hz, latticePoint_of_notMem _ hz',
      variableChangePoint_some, variableChangePoint_some,
      _root_.WeierstrassCurve.Affine.Point.some.injEq]
    simp only [shortChange_u, Units.val_one, one_pow, one_mul]
    rw [tangentCoordinatePeriods_weierstrassP, tangentCoordinatePeriods_derivWeierstrassP,
      ← hr, ← hs, ← ht]
    constructor
    · rfl
    · ring

include hC in
theorem tangentCoordinatePeriods_exact_length :
    Real.pi / ZLattice.covolume (tangentCoordinatePeriods L C).lattice =
      Real.pi * ‖(C.u : ℂ)‖ ^ 2 / ZLattice.covolume L.lattice := by
  have h := equation_comparison_tangent_length W L (tangentCoordinatePeriods L C)
    C (shortChange W) hC (shortChange_eq_tangentCoordinate_latticeCurve L C W hC)
  simpa only [shortChange_u, Units.val_one, norm_one, one_pow, mul_one] using h

include hC in
theorem tangentCoordinatePeriods_log_covolume (hΔ : W.Δ = 1) :
    Real.log (ZLattice.covolume (tangentCoordinatePeriods L C).lattice) - Real.log Real.pi =
      PeriodArithmetic.latticeLogPeriod L := by
  have h := equation_comparison_logarithmic_period W L (tangentCoordinatePeriods L C)
    C (shortChange W) hC (shortChange_eq_tangentCoordinate_latticeCurve L C W hC)
  rw [PeriodArithmetic.latticeLogPeriod,
    tangentCoordinatePeriods_discriminant L C W hC, hΔ, norm_one,
    Real.log_one, zero_div, add_zero,
    Real.log_div (PeriodMean.latticeArea_pos (tangentCoordinatePeriods L C)).ne'
      Real.pi_ne_zero] at h
  exact h

include hC in
def tangentCoordinate_holomorphicComparison :
    shortChange W • W.baseChange ℂ = latticeCurve (tangentCoordinatePeriods L C) := by
  change shortChange W • W.map (RingHom.id ℂ) = _
  rw [_root_.WeierstrassCurve.map_id]
  exact shortChange_eq_tangentCoordinate_latticeCurve L C W hC

variable [W.IsElliptic]

/-- The actual origin bundle and integral vector of the original W under
the normalized comparison, on all regular sections. -/
def tangentCoordinateHolUnif :
    SchemeTheory.EllipticHolUnif W (tangentCoordinatePeriods L C) :=
  WeierstrassTheta.canonicalHolUnif (tangentCoordinatePeriods L C) W (shortChange W)
    (tangentCoordinate_holomorphicComparison L C W hC)

theorem tangentCoordinateHolUnif_isAH :
    (tangentCoordinateHolUnif L C W hC).IsAH
      (latticeForm (tangentCoordinatePeriods L C)) (sigmaSign (tangentCoordinatePeriods L C)) :=
  WeierstrassTheta.canonicalHolUnif_isAH _ _ _ _

theorem tangentCoordinateHolUnif_integral_tangent :
    (tangentCoordinateHolUnif L C W hC).HasTangentDirection 1
      (SchemeTheory.WeierstrassLie.integralVector W) := by
  simpa only [shortChange_u, Units.val_one] using
    WeierstrassTheta.canonicalHolUnif_integral_tangent
      (tangentCoordinatePeriods L C) W (shortChange W)
      (tangentCoordinate_holomorphicComparison L C W hC)

end RHLean.Geometry.NativeCM.Weierstrass

namespace RHLean.Geometry.NativeCM.AllPlaceTangentPeriod

variable {F : Type} [Field F] (W : _root_.WeierstrassCurve (𝓞 F)) (hΔ : W.Δ = 1)

def tangentPeriods (v : InfinitePlace F) : PeriodPair :=
  Weierstrass.tangentCoordinatePeriods (lattice W hΔ v) (coordinateChange W hΔ v)

theorem tangentPeriods_discriminant (v : InfinitePlace F) :
    (tangentPeriods W hΔ v).g₂ ^ 3 - 27 * (tangentPeriods W hΔ v).g₃ ^ 2 = 1 :=
  (Weierstrass.tangentCoordinatePeriods_discriminant _ _ _ (comparison W hΔ v)).trans
    (complexEquation_discriminant W hΔ v)

theorem tangentPeriods_exact_profile (v : InfinitePlace F) :
    Real.pi / ZLattice.covolume (tangentPeriods W hΔ v).lattice = placeProfile W hΔ v :=
  Weierstrass.tangentCoordinatePeriods_exact_length _ _ _ (comparison W hΔ v)

theorem tangentPeriods_log_covolume (v : InfinitePlace F) :
    Real.log (ZLattice.covolume (tangentPeriods W hΔ v).lattice) - Real.log Real.pi =
      -Real.log (placeProfile W hΔ v) := by
  rw [neg_log_placeProfile]
  exact Weierstrass.tangentCoordinatePeriods_log_covolume _ _ _ (comparison W hΔ v)
    (complexEquation_discriminant W hΔ v)

end RHLean.Geometry.NativeCM.AllPlaceTangentPeriod
