import Mathlib
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Inert owner coefficient-transfer obstruction

For an inert rational prime `q`, the original OAI one-slot rescaled term has
coefficient `q⁻³`, while the native CORR-4 reciprocal daughter has coefficient
`q⁻¹`. This file isolates the resulting coefficient bill.

An owner-preserving diagonal map matching the two coefficients must multiply
the `q` coordinate by `q²`. Since primes congruent to `2 mod 3` are
arbitrarily large, these coordinatewise maps have no uniform bound in the
unweighted owner norm.

This is a source-carrier obstruction, not a signed estimate. It does not rule
out weighted norms, non-diagonal maps, use of the marked top term, or
cancellation in the complete compensated packet.
-/

namespace RHLean.Proof

/-- The scalar coefficient of the rescaled term in an inert OAI one-slot
compensation packet. -/
def oaiInertRescaledCoefficient (q : ℕ) : ℝ :=
  1 / (q : ℝ) ^ 3

/-- The reciprocal coefficient of the native low-owner CORR-4 daughter. -/
def nativeInertOwnerCoefficient (q : ℕ) : ℝ :=
  1 / (q : ℝ)

/-- Exact coordinatewise coefficient matching at one inert owner. -/
def InertOwnerwiseCoefficientMatch (q : ℕ) (t : ℝ) : Prop :=
  t * oaiInertRescaledCoefficient q = nativeInertOwnerCoefficient q

/-- A scalar multiplier bounded by `C` in the unweighted real owner norm. -/
def IsUnweightedMultiplierBound (t C : ℝ) : Prop :=
  ∀ x : ℝ, |t * x| ≤ C * |x|

/-- Exact local distortion: matching `q⁻³` to `q⁻¹` forces multiplier
`q²`. -/
theorem inertOwnerwiseCoefficientMatch_iff
    (q : ℕ) (hq : q ≠ 0) (t : ℝ) :
    InertOwnerwiseCoefficientMatch q t ↔ t = (q : ℝ) ^ 2 := by
  have hqR : (q : ℝ) ≠ 0 := by
    exact_mod_cast hq
  unfold InertOwnerwiseCoefficientMatch
  unfold oaiInertRescaledCoefficient nativeInertOwnerCoefficient
  constructor
  · intro h
    field_simp [hqR] at h
    nlinarith
  · intro h
    rw [h]
    field_simp [hqR]
    ring

/-- Any unweighted operator bound for the local coefficient match must pay the
full `q²` distortion. -/
theorem inertCoefficientMatch_sq_le_bound
    (q : ℕ) (hq : q ≠ 0) (t C : ℝ)
    (hmatch : InertOwnerwiseCoefficientMatch q t)
    (hbound : IsUnweightedMultiplierBound t C) :
    (q : ℝ) ^ 2 ≤ C := by
  have ht := (inertOwnerwiseCoefficientMatch_iff q hq t).mp hmatch
  have hb := hbound 1
  rw [ht] at hb
  simpa [abs_of_nonneg (sq_nonneg (q : ℝ))] using hb

/-- There are arbitrarily large inert-prime coordinates whose exact matching
multiplier exceeds any prescribed natural threshold. -/
theorem arbitrarily_large_inert_coefficient_multiplier (N : ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ≡ 2 [MOD 3] ∧
      ∀ t : ℝ, InertOwnerwiseCoefficientMatch q t →
        (N : ℝ) < |t| := by
  obtain ⟨q, hNq, hprime, hmod⟩ :=
    DirichletsTheorem.Nat.forall_exists_prime_gt_and_modEq N
      (q := 3) (a := 2) (by norm_num) (by norm_num)
  refine ⟨q, hprime, hmod, ?_⟩
  intro t hmatch
  have ht := (inertOwnerwiseCoefficientMatch_iff q hprime.ne_zero t).mp hmatch
  rw [ht, abs_of_nonneg (sq_nonneg (q : ℝ))]
  have hNqR : (N : ℝ) < (q : ℝ) := by
    exact_mod_cast hNq
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hprime.two_le
  nlinarith

/-- No constant uniformly bounds every owner-preserving coefficientwise
transfer from the inert OAI rescaled column to the native reciprocal column in
the unweighted owner norm. -/
theorem no_uniform_unweighted_inert_coefficient_transfer :
    ¬ ∃ C : ℝ, ∀ q : ℕ, q.Prime → q ≡ 2 [MOD 3] →
      ∀ t : ℝ, InertOwnerwiseCoefficientMatch q t →
        IsUnweightedMultiplierBound t C := by
  rintro ⟨C, hC⟩
  obtain ⟨N : ℕ, hCN⟩ := exists_nat_gt C
  obtain ⟨q, hprime, hmod, hlarge⟩ :=
    arbitrarily_large_inert_coefficient_multiplier N
  let t : ℝ := (q : ℝ) ^ 2
  have hmatch : InertOwnerwiseCoefficientMatch q t :=
    (inertOwnerwiseCoefficientMatch_iff q hprime.ne_zero t).2 rfl
  have hlarge' := hlarge t hmatch
  have hbound := hC q hprime hmod t hmatch
  have htle : |t| ≤ C := by
    simpa using hbound 1
  linarith

#print axioms inertOwnerwiseCoefficientMatch_iff
#print axioms inertCoefficientMatch_sq_le_bound
#print axioms arbitrarily_large_inert_coefficient_multiplier
#print axioms no_uniform_unweighted_inert_coefficient_transfer

end RHLean.Proof
