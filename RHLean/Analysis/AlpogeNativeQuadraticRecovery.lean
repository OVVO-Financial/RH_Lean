import RHLean.Analysis.AlpogeNativeZetaBalance
import RHLean.Analysis.AlpogeNativeCostNormalization

/-!
# Native signed quadratic recovery and a joint three-cost budget

The full principal prime-power sum has a supporting line at every
positive real coordinate, including integer jumps. The logarithmic
curvature is explicit, and log(y/x) <= y/x-1 bounds its remainder by
(y-x)^2/x. The affine Euler centering is retained. Consequently signed
mean displacement cancels *before* any absolute-value estimate, and
mean-square displacement, not mean absolute displacement, is the cost.

Independently, the exact already-earned normalized geometric bracket
needs only a joint ratio budget. At m=R, its scalar lower window on k
can be reduced from (R^2-1)*R to R^2, its upper window replaced by
n*T*R, and the density conditions expressed using a single allowance E.
This reduces the required numerical rank scale; it does not construct
a geometric family or prove its gain at that smaller rank.

No new source bound, assigned period, or RH hypothesis is imported.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- The actual supporting-line coefficient of the complete native
source; the jump at an integer uses the original right-hand prime-power
contribution. The Euler term has the original sign. -/
def alpogeNativeGzTangentSlope (x : ℝ) : ℝ :=
  nativeLambdaRecip ⌊x⌋₊ - Real.log x + Real.eulerMascheroniConstant

/-- The deterministic logarithmic curvature bound holds at every
pair of positive coordinates, without a unit-window restriction. -/
theorem alpogeNative_mul_log_tangent_debt (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    y * Real.log y - x * Real.log x -
      (Real.log x + 1) * (y - x) ≤ (y - x)^2 / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have hmul := mul_le_mul_of_nonneg_left h hy.le
  calc
    _ = y * (Real.log y - Real.log x) - (y - x) := by ring
    _ ≤ y * (y / x - 1) - (y - x) := sub_le_sub_right hmul _
    _ = _ := by
      field_simp [hx.ne']
      <;> ring

/-- The principal arithmetic supporting-line inequality follows from
the existing ordered finite-sum bounds, in either direction. No prime
distribution estimate is used. -/
theorem alpogeNativePrincipalPrimeSum_tangent_lower
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (y - x) * nativeLambdaRecip ⌊x⌋₊ ≤
      alpogeNativePrincipalPrimeSum y - alpogeNativePrincipalPrimeSum x := by
  rcases le_total x y with hxy | hyx
  · exact (alpogeNativePrincipalPrimeSum_sub_bounds y x hx hxy).1
  · have h := (alpogeNativePrincipalPrimeSum_sub_bounds x y hy hyx).2
    linarith only [h]

/-- One-sided quadratic recovery on the complete real Gz source. The
signed first-order term is not replaced by an absolute value. -/
theorem alpogeNativeGzArithmetic_tangent_lower
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    alpogeNativeGzArithmetic x ≤
      alpogeNativeGzArithmetic y + alpogeNativeGzTangentSlope x * (x - y) +
        (x - y)^2 / x := by
  have hp := alpogeNativePrincipalPrimeSum_tangent_lower x y hx.le hy.le
  have hd := alpogeNative_mul_log_tangent_debt x y hx hy
  rw [alpogeNativeGzArithmetic_eq_principal x,
    alpogeNativeGzArithmetic_eq_principal y]
  unfold alpogeNativeGzTangentSlope
  have heq : (x - y)^2 / x = (y - x)^2 / x := by ring
  rw [heq]
  linarith only [hp, hd]

/-- Recovery from the actual finite mean. The exact signed first moment
and the second moment of the SAME height family are retained. -/
theorem alpogeNativeGzArithmetic_le_mean_add_quadratic
    {ι : Type*} (TT : Finset ι) (hTT : TT.Nonempty)
    (x : ℝ) (v : ι → ℝ) (hx : 0 < x) (hv : ∀ t ∈ TT, 0 < v t) :
    alpogeNativeGzArithmetic x ≤
      (1 / (TT.card : ℝ)) * (∑ t ∈ TT, alpogeNativeGzArithmetic (v t)) +
      alpogeNativeGzTangentSlope x *
        ((1 / (TT.card : ℝ)) * ∑ t ∈ TT, (x - v t)) +
      ((1 / (TT.card : ℝ)) * ∑ t ∈ TT, (x - v t)^2) / x := by
  classical
  have hcard : (0 : ℝ) < TT.card := by exact_mod_cast hTT.card_pos
  have hs := Finset.sum_le_sum (s := TT)
    (fun t ht => alpogeNativeGzArithmetic_tangent_lower x (v t) hx (hv t ht))
  have hsum : (TT.card : ℝ) * alpogeNativeGzArithmetic x ≤
      (∑ t ∈ TT, alpogeNativeGzArithmetic (v t)) +
        alpogeNativeGzTangentSlope x * (∑ t ∈ TT, (x - v t)) +
          (∑ t ∈ TT, (x - v t)^2) / x := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_div] using hs
  calc
    _ = (1 / (TT.card : ℝ)) * ((TT.card : ℝ) * alpogeNativeGzArithmetic x) := by
      field_simp [hcard.ne']
    _ ≤ (1 / (TT.card : ℝ)) *
          ((∑ t ∈ TT, alpogeNativeGzArithmetic (v t)) +
            alpogeNativeGzTangentSlope x * (∑ t ∈ TT, (x - v t)) +
            (∑ t ∈ TT, (x - v t)^2) / x) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- If the actual signed first moment is zero, only the variance debt
remains. This does not require individual height proximity. -/
theorem alpogeNativeGzArithmetic_le_mean_add_variance
    {ι : Type*} (TT : Finset ι) (hTT : TT.Nonempty)
    (x : ℝ) (v : ι → ℝ) (hx : 0 < x) (hv : ∀ t ∈ TT, 0 < v t)
    (hcenter : ∑ t ∈ TT, (x - v t) = 0) :
    alpogeNativeGzArithmetic x ≤
      (1 / (TT.card : ℝ)) * (∑ t ∈ TT, alpogeNativeGzArithmetic (v t)) +
        ((1 / (TT.card : ℝ)) * ∑ t ∈ TT, (x - v t)^2) / x := by
  simpa only [hcenter, mul_zero, add_zero] using
    alpogeNativeGzArithmetic_le_mean_add_quadratic TT hTT x v hx hv

/-- Pay all three normalized costs with joint ratios instead of the
literal SizeWindows record. The rank parameter k may be as small as m^2.
The density and count requirements apply to the actual earned divisor.
No geometric gain is assumed in this finite numerical calculation. -/
theorem alpogeNativeNormalizedCosts_le_jointRatios
    (T Delta n m b k aE E : ℝ)
    (hT : 0 < T) (hDelta : 0 < Delta) (hn : 0 < n)
    (hm : 0 < m) (hb : 0 < b) (hk : 0 < k) (haE0 : 0 ≤ aE)
    (hE : 1 ≤ E) (haE : aE ≤ 2 * m^2 * b)
    (hLower : m^2 ≤ k) (hUpper : k ≤ n * T * m)
    (hCount : n ≤ 2 * E * T) (hDensity : 1 ≤ E * Delta) :
    alpogeNativeNormalizedGeometricCosts T Delta n m b k aE E ≤
      18 * m * E^3 := by
  have hE0 : 0 < E := by linarith
  have hA : 2 * aE / (m * b) ≤ 4 * m := by
    apply (div_le_iff₀ (mul_pos hm hb)).2
    nlinarith only [haE]
  have hD : 1 / Delta ≤ E := (div_le_iff₀ hDelta).2 hDensity
  have hR : 1 + m^2 / k ≤ 2 := by
    have h : m^2 / k ≤ (1 : ℝ) :=
      (div_le_iff₀ hk).2 (by simpa only [one_mul] using hLower)
    linarith only [h]
  have hN : n / T ≤ 2 * E := (div_le_iff₀ hT).2 hCount
  have hK : k / (n * T) ≤ m := by
    apply (div_le_iff₀ (mul_pos hn hT)).2
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hUpper
  have hfirst : 2 * aE / (m * b * Delta) * (1 + m^2 / k) ≤ 8 * m * E := by
    calc
      _ = (2 * aE / (m * b)) * (1 / Delta) * (1 + m^2 / k) := by
        field_simp [hm.ne', hb.ne', hDelta.ne', hk.ne']
        <;> ring
      _ ≤ (4 * m) * E * 2 := by
        exact mul_le_mul (mul_le_mul hA hD (by positivity) (by positivity))
          hR (by positivity) (by positivity)
      _ = _ := by ring
  have hmid : 4 * n * m * E / (T * Delta) ≤ 8 * m * E^3 := by
    calc
      _ = (4 * m * E) * (n / T) * (1 / Delta) := by
        field_simp [hT.ne', hDelta.ne']
        <;> ring
      _ ≤ (4 * m * E) * (2 * E) * E := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hN (by positivity))
          hD (by positivity) (by positivity)
      _ = _ := by ring
  have hlast : 2 * k * E^2 / (n * T) ≤ 2 * m * E^2 := by
    calc
      _ = (2 * E^2) * (k / (n * T)) := by ring
      _ ≤ (2 * E^2) * m := mul_le_mul_of_nonneg_left hK (by positivity)
      _ = _ := by ring
  have hE2 : E ≤ E^2 := by
    nlinarith only [mul_nonneg hE0.le (sub_nonneg.mpr hE)]
  have hE3 : E^2 ≤ E^3 := by
    nlinarith only [mul_nonneg (sq_nonneg E) (sub_nonneg.mpr hE)]
  have hfirst' := hfirst.trans
    (show 8 * m * E ≤ 8 * m * E^3 from
      mul_le_mul_of_nonneg_left (hE2.trans hE3) (by positivity))
  have hlast' := hlast.trans
    (show 2 * m * E^2 ≤ 2 * m * E^3 from
      mul_le_mul_of_nonneg_left hE3 (by positivity))
  unfold alpogeNativeNormalizedGeometricCosts
  linarith only [hfirst', hmid, hlast']

/-- Direct payment of the native scalar estimate from the actual centered
height mean and joint costs, without the original SizeWindows record.
The physical mean inequality is still a premise: the same-family complete
signed excess must supply it through the constructed dyadic payment. -/
theorem alpogeNativeGzArithmetic_le_of_centeredJointRatios
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (C ε x : ℝ) (TT T2 : Finset H) (m : ℕ) (b k aE : ℝ) (v : H → ℝ)
    (hx1 : 1 ≤ x) (hxR : x ≤ (m : ℝ)^2)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hTT : TT.Nonempty) (hT2 : T2.Nonempty) (hm : 0 < m)
    (hb : 0 < b) (hk : 0 < k) (haE0 : 0 ≤ aE)
    (haE : aE ≤ 2 * (m : ℝ)^2 * b)
    (hLower : (m : ℝ)^2 ≤ k)
    (hUpper : k ≤ (Fintype.card H : ℝ) * TT.card * m)
    (hCount : (Fintype.card H : ℝ) ≤ 2 * x^ε * TT.card)
    (hDensity : 1 ≤ x^ε * alpogeNativeProjectionDensity T2)
    (hv : ∀ t ∈ TT, 0 < v t)
    (hcenter : ∑ t ∈ TT, (x - v t) = 0)
    (hMean : (1 / (TT.card : ℝ)) * (∑ t ∈ TT, alpogeNativeGzArithmetic (v t)) ≤
      x ^ (C * ε) * alpogeNativeNormalizedGeometricCosts TT.card
        (alpogeNativeProjectionDensity T2) (Fintype.card H) m b k aE (x^ε) +
        x ^ ((1 : ℝ) / 2 + ε))
    (hVar : ((1 / (TT.card : ℝ)) * ∑ t ∈ TT, (x - v t)^2) / x ≤
        3 * x ^ ((1 : ℝ) / 2 + ε)) :
    alpogeNativeGzArithmetic x ≤ 22 * (m : ℝ) * x ^ ((C + 3) * ε) := by
  have hx0 : 0 < x := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hT : (0 : ℝ) < TT.card := by exact_mod_cast hTT.card_pos
  have hT2R : (0 : ℝ) < T2.card := by exact_mod_cast hT2.card_pos
  have hn : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hDelta : 0 < alpogeNativeProjectionDensity T2 := by
    unfold alpogeNativeProjectionDensity
    exact div_pos hT2R hn
  have hE : 1 ≤ x^ε := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hx1 hε)
  have hcost := alpogeNativeNormalizedCosts_le_jointRatios
    (TT.card : ℝ) (alpogeNativeProjectionDensity T2)
    (Fintype.card H : ℝ) (m : ℝ) b k aE (x^ε)
    hT hDelta hn hmR hb hk haE0 hE haE hLower hUpper hCount hDensity
  have hscale : x ^ (C * ε) * (x^ε)^3 = x ^ ((C + 3) * ε) := by
    calc
      _ = x ^ (C * ε) * (x^ε * x^ε * x^ε) := by ring
      _ = x ^ (C * ε) * x ^ (ε + ε + ε) := by
        rw [Real.rpow_add hx0 (ε + ε) ε, Real.rpow_add hx0 ε ε]
      _ = x ^ (C * ε + (ε + ε + ε)) := (Real.rpow_add hx0 _ _).symm
      _ = _ := by congr 1 <;> ring
  have hgeom : x ^ (C * ε) * alpogeNativeNormalizedGeometricCosts TT.card
      (alpogeNativeProjectionDensity T2) (Fintype.card H) m b k aE (x^ε) ≤
        18 * (m : ℝ) * x ^ ((C + 3) * ε) := by
    calc
      _ ≤ x ^ (C * ε) * (18 * (m : ℝ) * (x^ε)^3) :=
        mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg hx0.le _)
      _ = 18 * (m : ℝ) * (x ^ (C * ε) * (x^ε)^3) := by ring
      _ = _ := by rw [hscale]
  have hs : Real.sqrt x ≤ (m : ℝ) := by
    nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt hx0.le]
  have hexp : ε ≤ (C + 3) * ε := by
    nlinarith only [mul_nonneg hC hε, hε]
  have hrem : x ^ ((1 : ℝ) / 2 + ε) ≤ (m : ℝ) * x ^ ((C + 3) * ε) := by
    calc
      _ = Real.sqrt x * x^ε := by
        rw [Real.rpow_add hx0, Real.sqrt_eq_rpow]
      _ ≤ (m : ℝ) * x^ε := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hx0.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1 hexp) hmR.le
  have hrec := alpogeNativeGzArithmetic_le_mean_add_variance TT hTT x v hx0 hv hcenter
  linarith only [hrec, hMean, hVar, hgeom, hrem]

end RHLean.Analysis

end
