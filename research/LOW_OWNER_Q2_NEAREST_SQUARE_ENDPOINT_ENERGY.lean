import Mathlib
import RHLean.Proof.PhysicalQ2ExceptionalTerminalSynthesis
import «research.LOW_OWNER_Q2_ENDPOINT_FREQUENCY_DISTANCE»

/-!
# Energy consumer for the nearest-square reciprocal q² column

The midpoint reduction separates the literal reciprocal daughter column into
completed-square endpoint values plus a root-scale shell.  This file records the
quantitative consumer for the endpoint column itself.

Because the endpoint column still carries the physical reciprocal coefficient
`1/q`, finite Cauchy--Schwarz gives the same odd-prime quarter budget:

  || sum_q M(E_q)/q ||² <= (1/4) sum_q ||M(E_q)||².

The selected nearest-square root is either `sqrt(Y_q)` or `sqrt(Y_q)+1`.
Therefore the existing deterministic theorem

  sum_q (roundedRoot_q + 1)² <= 2 R²

also bounds the total selected-root square scale.  Consequently, if every
selected completed-square endpoint obeys a lower-scale envelope

  ||M(E_q)||² <= A * root_q² * K,

then the complete reciprocal endpoint column costs at most

  (A/2) R² K.

This theorem is only a consumer of endpoint bounds.  It does not assert the
parent reconstruction or an RH-scale endpoint envelope on its own.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Sum of unweighted completed-square endpoint energies selected by the
midpoint rule. -/
def lowOwnerNearestSquareEndpointEnergy (R : ℕ) : ℝ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    ‖lowOwnerNearestSquareMertensAmplitude R q‖ ^ 2

/-- The selected endpoint amplitude is exactly the existing terminal
square-endpoint energy at the selected nearest-square root. -/
theorem norm_sq_lowOwnerNearestSquareMertensAmplitude_eq_squareEndpointEnergy
    (R q : ℕ) :
    ‖lowOwnerNearestSquareMertensAmplitude R q‖ ^ 2 =
      squareEndpointMertensEnergyReal
        (q2NearestSquareRoot (rawQ2ChildCutoff R q)) := by
  unfold lowOwnerNearestSquareMertensAmplitude squareEndpointMertensEnergyReal
  rw [q2NearestSquareEndpoint_eq_rootEndpoint]
  rw [Complex.norm_intCast]
  exact sq_abs (((mertensSummatoryInt
    (squareRootEndpoint (q2NearestSquareRoot (rawQ2ChildCutoff R q))) : ℤ) : ℝ))

/-- **Quarter-frame endpoint bound.**  The reciprocal nearest-square endpoint
column has squared norm at most one quarter of the unweighted endpoint energy. -/
theorem norm_sq_lowOwnerNearestSquareReciprocalColumn_le_quarter_endpointEnergy
    (R : ℕ) :
    ‖lowOwnerNearestSquareReciprocalColumn R‖ ^ 2 ≤
      (1 / 4 : ℝ) * lowOwnerNearestSquareEndpointEnergy R := by
  have htri :
      ‖lowOwnerNearestSquareReciprocalColumn R‖ ≤
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) *
            ‖lowOwnerNearestSquareMertensAmplitude R q‖ := by
    unfold lowOwnerNearestSquareReciprocalColumn
    calc
      ‖∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℂ)) * lowOwnerNearestSquareMertensAmplitude R q‖ ≤
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          ‖(1 / (q : ℂ)) * lowOwnerNearestSquareMertensAmplitude R q‖ :=
        norm_sum_le _ _
      _ = ∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) *
            ‖lowOwnerNearestSquareMertensAmplitude R q‖ := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hsq :
      ‖lowOwnerNearestSquareReciprocalColumn R‖ ^ 2 ≤
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) *
            ‖lowOwnerNearestSquareMertensAmplitude R q‖) ^ 2 := by
    nlinarith [norm_nonneg (lowOwnerNearestSquareReciprocalColumn R)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (R := ℝ) (canonicalRoughLowQ2Owners R)
    (fun q => (1 : ℝ) / (q : ℝ))
    (fun q => ‖lowOwnerNearestSquareMertensAmplitude R q‖)
  have hbudget := lowOwnerReciprocalSquareBudgetReal_le_quarter R
  have henergy0 : 0 ≤ lowOwnerNearestSquareEndpointEnergy R := by
    unfold lowOwnerNearestSquareEndpointEnergy
    positivity
  calc
    ‖lowOwnerNearestSquareReciprocalColumn R‖ ^ 2 ≤
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) *
            ‖lowOwnerNearestSquareMertensAmplitude R q‖) ^ 2 := hsq
    _ ≤ (∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) ^ 2) *
        lowOwnerNearestSquareEndpointEnergy R := by
      simpa [lowOwnerNearestSquareEndpointEnergy] using hcs
    _ = (∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 : ℝ) / (q : ℝ) ^ 2) *
        lowOwnerNearestSquareEndpointEnergy R := by
      congr 1
      apply Finset.sum_congr rfl
      intro q _hq
      ring
    _ ≤ (1 / 4 : ℝ) * lowOwnerNearestSquareEndpointEnergy R :=
      mul_le_mul_of_nonneg_right hbudget henergy0

/-- The midpoint-selected completed-square root is never larger than the lower
rounded root plus one. -/
theorem q2NearestSquareRoot_le_sqrt_add_one (x : ℕ) :
    q2NearestSquareRoot x ≤ Nat.sqrt x + 1 := by
  by_cases hmid : x < (Nat.sqrt x) ^ 2 + Nat.sqrt x
  · simp [q2NearestSquareRoot, hmid]
  · simp [q2NearestSquareRoot, hmid]

/-- Hence one q² daughter selected root is bounded by the existing rounded-root
shell scale. -/
theorem lowOwnerQ2NearestSquareRoot_le_rounded_add_one
    (R q : ℕ) :
    q2NearestSquareRoot (rawQ2ChildCutoff R q) ≤
      roundedQ2ChildRoot R q + 1 := by
  simpa [roundedQ2ChildRoot, rawQ2ChildCutoff] using
    q2NearestSquareRoot_le_sqrt_add_one (rawQ2ChildCutoff R q)

/-- **Selected-root square budget.**  Across all genuine low q² owners, the
nearest completed-square roots have total square scale at most `2 R²`. -/
theorem sum_lowOwnerQ2NearestSquareRoot_sq_le_two_root_sq
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ q ∈ canonicalRoughLowQ2Owners R,
      (q2NearestSquareRoot (rawQ2ChildCutoff R q) : ℝ) ^ 2) ≤
        2 * (R : ℝ) ^ 2 := by
  let S : Finset ℕ := canonicalRoughLowQ2Owners R
  let T : Finset ℕ := (primesUpTo (R - 1)).erase 2
  have hsub : S ⊆ T := Finset.sdiff_subset
  have hpoint : ∀ q ∈ S,
      (q2NearestSquareRoot (rawQ2ChildCutoff R q) : ℝ) ^ 2 ≤
        ((roundedQ2ChildRoot R q : ℝ) + 1) ^ 2 := by
    intro q _hq
    have hnat := lowOwnerQ2NearestSquareRoot_le_rounded_add_one R q
    have hreal :
        (q2NearestSquareRoot (rawQ2ChildCutoff R q) : ℝ) ≤
          (roundedQ2ChildRoot R q : ℝ) + 1 := by exact_mod_cast hnat
    have hleft0 : 0 ≤ (q2NearestSquareRoot (rawQ2ChildCutoff R q) : ℝ) := by positivity
    have hright0 : 0 ≤ (roundedQ2ChildRoot R q : ℝ) + 1 := by positivity
    nlinarith
  calc
    (∑ q ∈ S,
        (q2NearestSquareRoot (rawQ2ChildCutoff R q) : ℝ) ^ 2) ≤
      ∑ q ∈ S, ((roundedQ2ChildRoot R q : ℝ) + 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        exact hpoint q hq
    _ ≤ ∑ q ∈ T, ((roundedQ2ChildRoot R q : ℝ) + 1) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q _hq _hnot
      positivity
    _ ≤ 2 * (R : ℝ) ^ 2 := by
      simpa [T] using sum_roundedQ2ChildRoot_succ_sq_le_two_root_sq R hR

/-- Per-daughter endpoint envelope consumed by the nearest-square reciprocal
column.  `K` is deliberately an external lower-scale envelope parameter. -/
def LowOwnerNearestSquareEndpointEnvelope
    (R : ℕ) (A K : ℝ) : Prop :=
  ∀ q ∈ canonicalRoughLowQ2Owners R,
    ‖lowOwnerNearestSquareMertensAmplitude R q‖ ^ 2 ≤
      A * (q2NearestSquareRoot (rawQ2ChildCutoff R q) : ℝ) ^ 2 * K

/-- Endpoint envelope summed over the low-owner schedule. -/
theorem lowOwnerNearestSquareEndpointEnergy_le_two_A_root_sq_K
    {R : ℕ} {A K : ℝ}
    (hR : 2 ≤ R) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (henv : LowOwnerNearestSquareEndpointEnvelope R A K) :
    lowOwnerNearestSquareEndpointEnergy R ≤
      2 * A * (R : ℝ) ^ 2 * K := by
  have hsum := sum_lowOwnerQ2NearestSquareRoot_sq_le_two_root_sq R hR
  unfold lowOwnerNearestSquareEndpointEnergy
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R,
      ‖lowOwnerNearestSquareMertensAmplitude R q‖ ^ 2) ≤
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        A * (q2NearestSquareRoot (rawQ2ChildCutoff R q) : ℝ) ^ 2 * K := by
          apply Finset.sum_le_sum
          intro q hq
          exact henv q hq
    _ = A * K *
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          (q2NearestSquareRoot (rawQ2ChildCutoff R q) : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring
    _ ≤ A * K * (2 * (R : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hsum (mul_nonneg hA hK)
    _ = 2 * A * (R : ℝ) ^ 2 * K := by ring

/-- **Half-coefficient endpoint consumer.**  Under a lower-scale endpoint
envelope, the entire reciprocal nearest-square endpoint column has energy at
most `(A/2) R² K`. -/
theorem norm_sq_lowOwnerNearestSquareReciprocalColumn_le_half_A_root_sq_K
    {R : ℕ} {A K : ℝ}
    (hR : 2 ≤ R) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (henv : LowOwnerNearestSquareEndpointEnvelope R A K) :
    ‖lowOwnerNearestSquareReciprocalColumn R‖ ^ 2 ≤
      (A / 2) * (R : ℝ) ^ 2 * K := by
  have hquarter :=
    norm_sq_lowOwnerNearestSquareReciprocalColumn_le_quarter_endpointEnergy R
  have henergy :=
    lowOwnerNearestSquareEndpointEnergy_le_two_A_root_sq_K
      hR hA hK henv
  calc
    ‖lowOwnerNearestSquareReciprocalColumn R‖ ^ 2 ≤
      (1 / 4 : ℝ) * lowOwnerNearestSquareEndpointEnergy R := hquarter
    _ ≤ (1 / 4 : ℝ) * (2 * A * (R : ℝ) ^ 2 * K) :=
      mul_le_mul_of_nonneg_left henergy (by norm_num)
    _ = (A / 2) * (R : ℝ) ^ 2 * K := by ring

end RHLean.Proof
