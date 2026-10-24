import Mathlib
import «research.VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP»
import RHLean.Analysis.PrimeSieveCollapseIdentity

/-!
# Frozen rational Mobius cofactors, actual moving prime availability, and OAI norm lift

The only Mobius signs in the transport are indexed by c < R and never
change during a post-root prime insertion. The response weight counts the
GENUINE primes p > R with c*p <= R^2-1, including the original sharp masks.
At R prime, the p=R fibre belongs to the smooth side of THIS non-strict
cutoff; it is not silently lost. The strict historical cutoff p>=R is a
different presentation requiring an explicit boundary transfer.

The OAI-facing theorem below uses the already proved, completely restored
quadratic norm/chi_-3 identity. The physical Hecke kernel retains its
3,4,12 restoration and the actual c*p cutoff. This is not a claim that the
weighted operator is an original cubic-theta OAI detector row, nor does
it assert a new moment bound.

The last theorem is a SOURCE-SCALE NONADMISSION: directly treating p>R
as an OAI marked prime slot cannot meet the published marked inverse moment
inequality when the row exponent m <= 5/6. OAI's selected primes are
auxiliary small slots, not the physical post-root prime itself.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Analysis

open RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- Actual square endpoint, inclusive. -/
def vf919FrozenCofactorEndpoint (R : ℕ) : ℕ := R ^ 2 - 1

/-- Genuine, nonnegative prime-availability response of one FROZEN cofactor.
The prime cutoff is STRICT p > R as in the repository's standard wheel. -/
def vf919FrozenCofactorPrimeWeight (R c : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc R (vf919FrozenCofactorEndpoint R),
    if p.Prime ∧ c * p ≤ vf919FrozenCofactorEndpoint R then (1 : ℂ) else 0

/-- Nothing beyond the real physical integer endpoint can respond. -/
theorem vf919FrozenCofactorPrimeWeight_zero_above_endpoint
    (R c : ℕ) (hc : vf919FrozenCofactorEndpoint R < c) :
    vf919FrozenCofactorPrimeWeight R c = 0 := by
  unfold vf919FrozenCofactorPrimeWeight
  apply Finset.sum_eq_zero
  intro p hp
  have hpR : R < p := (Finset.mem_Ioc.mp hp).1
  have hp1 : 1 ≤ p := by omega
  have hcp : vf919FrozenCofactorEndpoint R < c * p := by
    have hmult : c ≤ c * p := by nlinarith
    omega
  have hnot : ¬ (p.Prime ∧ c * p ≤ vf919FrozenCofactorEndpoint R) := by
    intro h
    omega
  simp [hnot]

/-- Only the already processed historical coefficients c < R can have
nonzero post-root prime availability. This is source geometry, not a rate. -/
theorem vf919FrozenCofactorPrimeWeight_zero_of_root_le
    (R c : ℕ) (hR : 2 ≤ R) (hc : R ≤ c) :
    vf919FrozenCofactorPrimeWeight R c = 0 := by
  unfold vf919FrozenCofactorPrimeWeight
  apply Finset.sum_eq_zero
  intro p hp
  have hpR : R < p := (Finset.mem_Ioc.mp hp).1
  have hprod : R * (R + 1) ≤ c * p :=
    Nat.mul_le_mul hc (by omega : R + 1 ≤ p)
  have hroot : vf919FrozenCofactorEndpoint R < R * (R + 1) := by
    unfold vf919FrozenCofactorEndpoint
    have hpow : 1 ≤ R ^ 2 := by nlinarith
    have hcancel : (R ^ 2 - 1) + 1 = R ^ 2 := Nat.sub_add_cancel hpow
    have hcompare : R ^ 2 ≤ R * (R + 1) := by nlinarith
    omega
  have hnot : ¬ (p.Prime ∧ c * p ≤ vf919FrozenCofactorEndpoint R) := by
    intro h
    omega
  simp [hnot]

/-- The original low-Mobius population responds with genuine prime counts,
but NONE of its sign coefficients changes under insertion of p>R. -/
def vf919FrozenCofactorPhysicalResponse (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    (ArithmeticFunction.moebius c : ℂ) * vf919FrozenCofactorPrimeWeight R c

/-- The complete OAI-facing source: original norm coefficient a_F and
chi_-3 with all deleted factors restored at physical weights. -/
def vf919FrozenCofactorHeckeResponse (R : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (vf919FrozenCofactorEndpoint R),
    vf919ExcludedNormCoefficients m *
      vf919PhysicalHeckeKernel (vf919FrozenCofactorEndpoint R)
        (vf919FrozenCofactorPrimeWeight R) m

/-- Exact transport of the FROZEN signed cofactor response into the complete
quadratic Hecke norm kernel; no implicit OAI coefficient estimates. -/
theorem vf919FrozenCofactorPhysicalResponse_eq_completeHecke
    (R : ℕ) (hR : 4 ≤ R) :
    vf919FrozenCofactorPhysicalResponse R =
      vf919FrozenCofactorHeckeResponse R := by
  let X := vf919FrozenCofactorEndpoint R
  have hX : 12 ≤ X := by
    dsimp [X, vf919FrozenCofactorEndpoint]
    have hpow : (4 : ℕ) ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hR 2
    have hcancel : (R ^ 2 - 1) + 1 = R ^ 2 :=
      Nat.sub_add_cancel (by omega)
    omega
  have hsub : Finset.Ico 1 R ⊆ Finset.Icc 1 X := by
    intro c hc
    simp only [Finset.mem_Ico, Finset.mem_Icc] at hc ⊢
    constructor
    · exact hc.1
    · have hRX : R ≤ X := by
        dsimp [X, vf919FrozenCofactorEndpoint]
        have htwice : R * 2 ≤ R * R :=
          Nat.mul_le_mul_left R (by omega : 2 ≤ R)
        have hpoly : R + 1 ≤ R ^ 2 := by nlinarith
        have hcancel : (R ^ 2 - 1) + 1 = R ^ 2 :=
          Nat.sub_add_cancel (by omega)
        omega
      omega
  have hsum :
      (∑ c ∈ Finset.Ico 1 R,
        (ArithmeticFunction.moebius c : ℂ) * vf919FrozenCofactorPrimeWeight R c) =
      ∑ c ∈ Finset.Icc 1 X,
        (ArithmeticFunction.moebius c : ℂ) * vf919FrozenCofactorPrimeWeight R c := by
    apply Finset.sum_subset hsub
    intro c hcX hnot
    have hcR : R ≤ c := by
      simp only [Finset.mem_Ico, not_and, not_lt] at hnot
      have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcX).1
      exact hnot hc1
    rw [vf919FrozenCofactorPrimeWeight_zero_of_root_le R c (by omega) hcR]
    ring
  unfold vf919FrozenCofactorPhysicalResponse
    vf919FrozenCofactorHeckeResponse
  rw [hsum]
  exact vf919WeightedMobius_eq_excludedNormKernel X hX
    (vf919FrozenCofactorPrimeWeight R)
    (vf919FrozenCofactorPrimeWeight_zero_above_endpoint R)

/-- Physical root-smooth mass with the same wheel p <= R. -/
def vf919FrozenWheelSmoothMass (R : ℕ) : ℂ :=
  primeSieveSmoothMobiusMass R (vf919FrozenCofactorEndpoint R)

/-- Genuine prime-first transport with p > R. -/
def vf919FrozenWheelPrimeTail (R : ℕ) : ℂ :=
  primeSieveMertensPrimeTail R (vf919FrozenCofactorEndpoint R)

/-- The actual Mertens prefix is the signed combination of the fixed-wheel
smooth population and the still-changing prime tail, not either separately. -/
theorem vf919FrozenWheelMertens_eq_smooth_sub_primeTail
    (R : ℕ) (hR : 2 ≤ R) :
    mertensSummatory (vf919FrozenCofactorEndpoint R) =
      vf919FrozenWheelSmoothMass R - vf919FrozenWheelPrimeTail R := by
  have hroot : Nat.sqrt (vf919FrozenCofactorEndpoint R) < R := by
    unfold vf919FrozenCofactorEndpoint
    apply (Nat.sqrt_lt').2
    have hpos : 0 < R ^ 2 := pow_pos (by omega) 2
    omega
  have hmain :=
    mertensSummatory_eq_neg_signedSum_add_smoothMass
      R (vf919FrozenCofactorEndpoint R) hroot
  rw [primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail] at hmain
  unfold vf919FrozenWheelSmoothMass vf919FrozenWheelPrimeTail
  linear_combination hmain

/-- Original full signed NNS zero-target two-source Gram: the OFF-DIAGONAL
mixed term is essential and never estimated by triangle inequality here. -/
theorem vf919FrozenWheel_full_signedNNS_gram
    (R : ℕ) (hR : 2 ≤ R) :
    ‖mertensSummatory (vf919FrozenCofactorEndpoint R)‖ ^ 2 =
      ‖vf919FrozenWheelSmoothMass R‖ ^ 2 +
      ‖vf919FrozenWheelPrimeTail R‖ ^ 2 -
      2 * (vf919FrozenWheelSmoothMass R *
        star (vf919FrozenWheelPrimeTail R)).re := by
  rw [vf919FrozenWheelMertens_eq_smooth_sub_primeTail R hR]
  simpa [Complex.sq_norm] using
    Complex.normSq_sub (vf919FrozenWheelSmoothMass R)
      (vf919FrozenWheelPrimeTail R)

/-- What any externally justified Mertens amplitude bound actually pays in
the two historical sources. A bound is an explicit hypothesis, not assumed. -/
theorem vf919FrozenWheel_antiAlignment_of_externalBound
    (R : ℕ) (hR : 2 ≤ R) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ‖mertensSummatory (vf919FrozenCofactorEndpoint R)‖ ≤ A) :
    ‖vf919FrozenWheelSmoothMass R‖ ^ 2 +
        ‖vf919FrozenWheelPrimeTail R‖ ^ 2 - A ^ 2 ≤
      2 * (vf919FrozenWheelSmoothMass R *
        star (vf919FrozenWheelPrimeTail R)).re := by
  have hsquared :
      ‖mertensSummatory (vf919FrozenCofactorEndpoint R)‖ ^ 2 ≤ A ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hA).mpr hbound
  rw [vf919FrozenWheel_full_signedNNS_gram R hR] at hsquared
  linarith

/-- Quantified direct-transplant obstruction for OpenAI's ACTUAL marked
inverse moment r+2z <= m-c1. Any physical post-root prime has z>=1/2,
whereas the moderate OAI rows have m<=h+zeta<5/6. The marked primes
must therefore be auxiliary short slots, NOT the moving physical primes. -/
theorem vf919FrozenWheel_postRootPrime_not_directMarkedSlot
    (r z m margin : ℝ) (hr : 0 ≤ r) (hz : (1 / 2 : ℝ) ≤ z)
    (hm : m ≤ 5 / 6) (hmargin : 0 < margin) :
    ¬ r + 2 * z ≤ m - margin := by
  intro h
  linarith

/-- The companion 2r+8z<=3m-c2 marked moment budget fails as well. -/
theorem vf919FrozenWheel_postRootPrime_not_directSixthMoment
    (r z m margin : ℝ) (hr : 0 ≤ r) (hz : (1 / 2 : ℝ) ≤ z)
    (hm : m ≤ 5 / 6) (hmargin : 0 < margin) :
    ¬ 2 * r + 8 * z ≤ 3 * m - margin := by
  intro h
  linarith

#print axioms vf919FrozenCofactorPrimeWeight_zero_above_endpoint
#print axioms vf919FrozenCofactorPrimeWeight_zero_of_root_le
#print axioms vf919FrozenCofactorPhysicalResponse_eq_completeHecke
#print axioms vf919FrozenWheelMertens_eq_smooth_sub_primeTail
#print axioms vf919FrozenWheel_full_signedNNS_gram
#print axioms vf919FrozenWheel_antiAlignment_of_externalBound
#print axioms vf919FrozenWheel_postRootPrime_not_directMarkedSlot
#print axioms vf919FrozenWheel_postRootPrime_not_directSixthMoment

end RHLean.Analysis
