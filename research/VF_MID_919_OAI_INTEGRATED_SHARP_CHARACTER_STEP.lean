import Mathlib
import «research.VF_MID_919_OAI_SHARP_SMOOTH_NO_GAP»

/-!
# #919: seminorm-free integrated character-prefix recovery

A pointwise bound on a derivative window W_h = u * V_h'(u) cannot be
uniform in shrinking widths h: its maximum can grow like 1/h.

However the *signed, integrated* convolution has an exact arithmetic
stability property at the half-integer cutoffs T = N + 1/2.

For any nonnegative integer ideal norm m and rational convolution index d,
the condition d*m <= T*u has the same truth value for EVERY
u in [1-h, 1+h], provided h*T < 1/2. Consequently any finite
signed character/ideal-norm convolution is literally constant across
the whole transition. Integrating against ANY signed smoothing density
supported there multiplies that fixed convolution by the total mass of
the density. No sup bound on W_h, derivatives or seminorms is required.

This is an exact finite character-convolution integration theorem, not
an OAI sixth-power moment bound or an RH-strength estimate. Identifying
the unbounded ideal series and the t-to-u change of variables remains
a separate analytic interface.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Multiplicative sites d*m are **integers**. A relative h-transition at
T=N+1/2 with h*T<1/2 cannot move across any integer site. -/
theorem vf919HalfIntegerMovingMultiplicativeSite_iff
    (N d m : ℕ) (h u : ℝ)
    (hwidth : h * ((N : ℝ) + 1 / 2) < 1 / 2)
    (hlo : 1 - h ≤ u) (hhi : u ≤ 1 + h) :
    ((d * m : ℕ) : ℝ) ≤ ((N : ℝ) + 1 / 2) * u ↔
      d * m ≤ N := by
  have hx : (0 : ℝ) ≤ (N : ℝ) + 1 / 2 := by positivity
  have hlow :
      ((N : ℝ) + 1 / 2) * (1 - h) ≤
        ((N : ℝ) + 1 / 2) * u :=
    mul_le_mul_of_nonneg_left hlo hx
  have hhigh :
      ((N : ℝ) + 1 / 2) * u ≤
        ((N : ℝ) + 1 / 2) * (1 + h) :=
    mul_le_mul_of_nonneg_left hhi hx
  have hbetween :
      (N : ℝ) < ((N : ℝ) + 1 / 2) * u ∧
      ((N : ℝ) + 1 / 2) * u < (N : ℝ) + 1 := by
    constructor <;> nlinarith
  constructor
  · intro hm
    have hs : ((d * m : ℕ) : ℝ) < (N : ℝ) + 1 :=
      lt_of_le_of_lt hm hbetween.2
    have hsNat : d * m < N + 1 := by exact_mod_cast hs
    omega
  · intro hm
    have hs : ((d * m : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
    exact hs.trans hbetween.1.le

/-- Signed coefficients over a *finite* norm index and a finite quadratic
character index. No positivity assumption on either coefficient. -/
def vf919FiniteSharpNormConvolution
    (ms ds : Finset ℕ) (a chi : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ ms, a m *
    ∑ d ∈ ds, if d * m ≤ N then chi d else 0

/-- The same full signed convolution evaluated at a moving smooth scale. -/
def vf919FiniteMovingNormConvolution
    (ms ds : Finset ℕ) (a chi : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ ms, a m *
    ∑ d ∈ ds,
      if ((d * m : ℕ) : ℝ) ≤ ((N : ℝ) + 1 / 2) * u then
        chi d else 0

/-- Even with all signed *cross-coefficient* cancellations retained,
the full finite ideal/rational convolution is unchanged at every point
of the transition window. -/
theorem vf919FiniteMovingNormConvolution_eq_sharp
    (ms ds : Finset ℕ) (a chi : ℕ → ℝ) (N : ℕ) (h u : ℝ)
    (hwidth : h * ((N : ℝ) + 1 / 2) < 1 / 2)
    (hlo : 1 - h ≤ u) (hhi : u ≤ 1 + h) :
    vf919FiniteMovingNormConvolution ms ds a chi N u =
      vf919FiniteSharpNormConvolution ms ds a chi N := by
  unfold vf919FiniteMovingNormConvolution vf919FiniteSharpNormConvolution
  apply Finset.sum_congr rfl
  intro m _hm
  congr 1
  apply Finset.sum_congr rfl
  intro d _hd
  have heq := vf919HalfIntegerMovingMultiplicativeSite_iff
    N d m h u hwidth hlo hhi
  by_cases hdm : d * m ≤ N
  · simp [hdm, heq.mpr hdm]
  · have hnot : ¬ (((d * m : ℕ) : ℝ) ≤ ((N : ℝ) + 1 / 2) * u) := by
      exact fun hh => hdm (heq.mp hh)
    simp [hdm, hnot]

/-- Key pointwise reduction **before** integration: any signed test density
rho supported in the transition window multiplies a constant complete
arithmetic convolution, even if rho has spikes of size O(1/h). -/
theorem vf919FiniteSignedWindowIntegrand_eq_sharp
    (ms ds : Finset ℕ) (a chi : ℕ → ℝ) (N : ℕ) (h : ℝ)
    (rho : ℝ → ℝ)
    (hwidth : h * ((N : ℝ) + 1 / 2) < 1 / 2)
    (hsupport : ∀ u : ℝ, rho u ≠ 0 → 1 - h ≤ u ∧ u ≤ 1 + h) :
    ∀ u : ℝ,
      rho u * vf919FiniteMovingNormConvolution ms ds a chi N u =
      rho u * vf919FiniteSharpNormConvolution ms ds a chi N := by
  intro u
  by_cases hu : rho u = 0
  · simp [hu]
  · rcases hsupport u hu with ⟨hlo, hhi⟩
    rw [vf919FiniteMovingNormConvolution_eq_sharp
      ms ds a chi N h u hwidth hlo hhi]

/-- **Seminorm-independent integrated recovery**: the integral depends on
the signed window ONLY through its total mass. This is an exact equality,
not a bound obtained by applying triangle inequality to ideal rows. -/
theorem vf919FiniteIntegratedNormConvolution_eq_mass_mul_sharp
    (ms ds : Finset ℕ) (a chi : ℕ → ℝ) (N : ℕ) (h : ℝ)
    (rho : ℝ → ℝ)
    (hwidth : h * ((N : ℝ) + 1 / 2) < 1 / 2)
    (hsupport : ∀ u : ℝ, rho u ≠ 0 → 1 - h ≤ u ∧ u ≤ 1 + h) :
    (∫ u : ℝ, rho u *
        vf919FiniteMovingNormConvolution ms ds a chi N u) =
      (∫ u : ℝ, rho u) *
        vf919FiniteSharpNormConvolution ms ds a chi N := by
  have hintegrands :
      (fun u : ℝ => rho u *
          vf919FiniteMovingNormConvolution ms ds a chi N u) =
      (fun u : ℝ => rho u *
          vf919FiniteSharpNormConvolution ms ds a chi N) := by
    funext u
    exact vf919FiniteSignedWindowIntegrand_eq_sharp
      ms ds a chi N h rho hwidth hsupport u
  rw [hintegrands, MeasureTheory.integral_mul_const]

/-- In particular, ANY unit-mass signed mollifier produces the sharp
convolution *exactly*: its peak size and all derivative seminorms vanish
from the formula. The remaining difficulty is bounding the recovered
signed arithmetic sum. -/
theorem vf919FiniteIntegratedNormConvolution_unit_mass
    (ms ds : Finset ℕ) (a chi : ℕ → ℝ) (N : ℕ) (h : ℝ)
    (rho : ℝ → ℝ)
    (hwidth : h * ((N : ℝ) + 1 / 2) < 1 / 2)
    (hsupport : ∀ u : ℝ, rho u ≠ 0 → 1 - h ≤ u ∧ u ≤ 1 + h)
    (hmass : (∫ u : ℝ, rho u) = 1) :
    (∫ u : ℝ, rho u *
        vf919FiniteMovingNormConvolution ms ds a chi N u) =
      vf919FiniteSharpNormConvolution ms ds a chi N := by
  rw [vf919FiniteIntegratedNormConvolution_eq_mass_mul_sharp
    ms ds a chi N h rho hwidth hsupport, hmass, one_mul]

end RHLean.Analysis
