import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»

/-!
# Floored-Li fantasy prime-count closure

This file isolates the simplest integer-valued discretization of the continuous
Li proxy:

  Pi_floorLi(x) = floor(Li_2(x)).

The rounding error is strictly less than one at every real cutoff. Therefore,
under the explicit fantasy identification that this integer-valued staircase is
the actual prime-counting staircase, the classical von-Koch prime-count error
holds with room to spare and the existing RH criterion closes immediately.

No statement here identifies the proxy with the actual prime-counting function.
That identification is kept as an explicit hypothesis.
-/

noncomputable section

namespace RHLean.Analysis

/-- Real-valued presentation of the integer floor of the repository-normalized
logarithmic integral. The value lies in the integers even though the codomain
is Real, which makes comparison with vfMidPrimeCount direct. -/
def liFloorPrimeCountProxy (x : ℝ) : ℝ :=
  ((⌊vfMidLogarithmicIntegralFromTwo x⌋ : ℤ) : ℝ)

/-- The floored-Li proxy never exceeds Li. -/
theorem liFloorPrimeCountProxy_le_li (x : ℝ) :
    liFloorPrimeCountProxy x ≤ vfMidLogarithmicIntegralFromTwo x := by
  unfold liFloorPrimeCountProxy
  simpa using (Int.floor_le (vfMidLogarithmicIntegralFromTwo x))

/-- Li is strictly below the next integer after its floor. -/
theorem li_lt_liFloorPrimeCountProxy_add_one (x : ℝ) :
    vfMidLogarithmicIntegralFromTwo x < liFloorPrimeCountProxy x + 1 := by
  unfold liFloorPrimeCountProxy
  exact Int.lt_floor_add_one (vfMidLogarithmicIntegralFromTwo x)

/-- Flooring Li costs strictly less than one count, uniformly in x. -/
theorem abs_liFloorPrimeCountProxy_sub_li_lt_one (x : ℝ) :
    |liFloorPrimeCountProxy x - vfMidLogarithmicIntegralFromTwo x| < 1 := by
  have hle := liFloorPrimeCountProxy_le_li x
  have hlt := li_lt_liFloorPrimeCountProxy_add_one x
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

/-- Uniform bounded-error statement for the floored-Li fantasy model. -/
def LiFloorPrimeCountProxyUniformBoundedStatement : Prop :=
  ∀ x : ℝ,
    |liFloorPrimeCountProxy x - vfMidLogarithmicIntegralFromTwo x| ≤ 1

/-- The floored-Li proxy is uniformly within one count of Li. -/
theorem liFloorPrimeCountProxy_uniformBounded :
    LiFloorPrimeCountProxyUniformBoundedStatement := by
  intro x
  exact le_of_lt (abs_liFloorPrimeCountProxy_sub_li_lt_one x)

/-- Explicit fantasy identification: on the prime-counting range, actual
prime count is postulated to equal the integer floor of Li. -/
def LiFloorPrimeCountIdentifiesActualPrimes : Prop :=
  ∀ x : ℝ, 4 ≤ x →
    vfMidPrimeCount x = liFloorPrimeCountProxy x

/-- Under the floored-Li fantasy identification, the actual prime-minus-Li
error satisfies the classical von-Koch scale. The proxy itself has O(1)
error, so this is much stronger than needed. -/
theorem primeLiVonKochBounded_of_liFloorPrimeCountIdentification
    (hident : LiFloorPrimeCountIdentifiesActualPrimes) :
    PrimeLiVonKochBoundedStatement := by
  let d : ℝ := 2 * Real.log 4
  let C : ℝ := 1 / d
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos (by norm_num) hlog4
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hround :
      |liFloorPrimeCountProxy x - vfMidLogarithmicIntegralFromTwo x| ≤ 1 :=
    liFloorPrimeCountProxy_uniformBounded x
  have hscale0 := two_log_four_le_sqrt_mul_log hx
  have hscale : 1 ≤ C * Real.sqrt x * Real.log x := by
    calc
      1 = C * d := by
        dsimp [C]
        field_simp [hd.ne']
      _ ≤ C * (Real.sqrt x * Real.log x) := by
        change d ≤ Real.sqrt x * Real.log x at hscale0
        exact mul_le_mul_of_nonneg_left hscale0 hC
      _ = C * Real.sqrt x * Real.log x := by ring
  unfold vfMidPrimeLiError
  rw [hident x hx]
  exact hround.trans hscale

/-- Floored-Li fantasy closure. If the actual prime-counting staircase is
identified with the integer floor of Li, the repository's classical von-Koch
criterion yields Mathlib's Riemann Hypothesis proposition. -/
theorem riemannHypothesis_of_liFloorPrimeCountIdentification
    (criterion : ClassicalVonKochRHCriterion)
    (hident : LiFloorPrimeCountIdentifiesActualPrimes) :
    VFMidRiemannHypothesisStatement :=
  criterion.iff_riemannHypothesis.mp
    (primeLiVonKochBounded_of_liFloorPrimeCountIdentification hident)

end RHLean.Analysis
