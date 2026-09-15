import Mathlib
import «research.GLOBAL_RETURNED_CORE_COMPENSATED_FOUR_CORNER»

/-!
# Finite threshold-incidence kernel for the returned-core AMP coordinate

The q² daughter crossings and the root crossing are samples of one nested
threshold process.  To keep the statement exactly on the finite AMP clock,
write

  F_R(n) = sum_{q in Q_R} 1/q * 1_{n <= Y_q} - 1_{n <= R-1}.

This is not a new analytic quantity: it is exactly the common-clock AMP site
weight minus the constant one mode.  Therefore its owner incidence gradient is

  F_R(a) - F_R(p*a) = w_R(a) - w_R(p*a)
                    = daughterCrossing - rootCrossing.

The shift of the root atom to `R-1` is forced by the half-open crossing
convention `a <= y < p*a`: over naturals,

  a < R <= p*a  <->  a <= R-1 < p*a.

Thus the compensated first-owner channel is literally a discrete incidence
gradient of a finite threshold potential.  When `p*a` leaves the physical
clock, the child potential is exactly zero; the only failure of a complete
edge is therefore the already-named clipped boundary.

No norm, Cauchy--Schwarz estimate, spectral approximation, or Mertens bound is
introduced here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Half-open threshold crossing of the owner edge `a -> p*a`. -/
def lowOwnerThresholdCrossingIndicator (p a y : ℕ) : ℝ :=
  if a ≤ y ∧ y < p * a then 1 else 0

/-- Tail transform of the finite signed threshold measure

    sum_q (1/q) delta_{Y_q} - delta_{R-1}.

Equivalently this is the AMP common-clock site weight with its constant-one
mode removed. -/
def lowOwnerThresholdPotential (R n : ℕ) : ℝ :=
  lowOwnerReciprocalDaughterWeight R n - (if n < R then 1 else 0)

/-- The finite threshold potential is exactly the AMP site coefficient minus
its constant mode. -/
theorem lowOwnerThresholdPotential_eq_weight_sub_one (R n : ℕ) :
    lowOwnerThresholdPotential R n =
      lowOwnerZeroFrequencyMobiusWeight R n - 1 := by
  unfold lowOwnerThresholdPotential lowOwnerZeroFrequencyMobiusWeight
    lowOwnerFarTailWeight
  by_cases hRn : R ≤ n
  · have hnR : ¬ n < R := Nat.not_lt_of_ge hRn
    simp [hRn, hnR]
  · have hnR : n < R := Nat.lt_of_not_ge hRn
    simp [hRn, hnR]

/-- Owner incidence kills the constant mode, so the threshold-potential
difference is exactly the compiled AMP owner difference. -/
theorem lowOwnerThresholdPotential_sub_mul
    {R p n : ℕ} (hp : 1 ≤ p) :
    lowOwnerThresholdPotential R n -
        lowOwnerThresholdPotential R (p * n) =
      lowOwnerDaughterCrossingWeight R p n -
        lowOwnerRootCrossingIndicator R p n := by
  calc
    lowOwnerThresholdPotential R n -
        lowOwnerThresholdPotential R (p * n) =
      (lowOwnerZeroFrequencyMobiusWeight R n - 1) -
        (lowOwnerZeroFrequencyMobiusWeight R (p * n) - 1) := by
          rw [lowOwnerThresholdPotential_eq_weight_sub_one,
            lowOwnerThresholdPotential_eq_weight_sub_one]
    _ = lowOwnerZeroFrequencyMobiusWeight R n -
        lowOwnerZeroFrequencyMobiusWeight R (p * n) := by ring
    _ = lowOwnerDaughterCrossingWeight R p n -
        lowOwnerRootCrossingIndicator R p n :=
      lowOwnerZeroFrequencyMobiusWeight_sub_mul hp

/-- Exact endpoint correction for the root wall.  With the common half-open
threshold convention, the root crossing lives at `R-1`, not at `R`. -/
theorem lowOwnerRootCrossingIndicator_eq_threshold_R_sub_one
    {R p a : ℕ} (hR : 1 ≤ R) :
    lowOwnerRootCrossingIndicator R p a =
      lowOwnerThresholdCrossingIndicator p a (R - 1) := by
  unfold lowOwnerRootCrossingIndicator lowOwnerThresholdCrossingIndicator
  have hiff :
      (a < R ∧ R ≤ p * a) ↔
        (a ≤ R - 1 ∧ R - 1 < p * a) := by
    omega
  by_cases h : a < R ∧ R ≤ p * a
  · have h' := hiff.mp h
    simp [h, h']
  · have h' : ¬ (a ≤ R - 1 ∧ R - 1 < p * a) := by
      intro hh
      exact h (hiff.mpr hh)
    simp [h, h']

/-- Each daughter-window crossing is one sample of the same half-open threshold
indicator. -/
theorem lowOwnerDaughterCrossingWeight_eq_threshold_sum
    (R p a : ℕ) :
    lowOwnerDaughterCrossingWeight R p a =
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          lowOwnerThresholdCrossingIndicator
            p a (rawQ2ChildCutoff R q) := by
  unfold lowOwnerDaughterCrossingWeight lowOwnerThresholdCrossingIndicator
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases h :
      a ≤ rawQ2ChildCutoff R q ∧
        rawQ2ChildCutoff R q < p * a
  · simp [h]
  · simp [h]

/-- Threshold-channel amplitude on one actual admitted first-owner cell. -/
def lowOwnerFirstOwnerThresholdAmplitude
    (R p : ℕ) (sig : Finset ℕ) (y : ℕ) : ℝ :=
  ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
    lowOwnerThresholdCrossingIndicator p a y * realMoebiusStep a

/-- The reciprocal daughter channels Fubini exactly into the daughter-crossing
part of one compensated cell. -/
theorem lowOwnerFirstOwnerDaughterChannels_eq_crossingAmplitude
    (R p : ℕ) (sig : Finset ℕ) :
    (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          lowOwnerFirstOwnerThresholdAmplitude
            R p sig (rawQ2ChildCutoff R q)) =
      ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerDaughterCrossingWeight R p a * realMoebiusStep a := by
  unfold lowOwnerFirstOwnerThresholdAmplitude
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
            lowOwnerThresholdCrossingIndicator
              p a (rawQ2ChildCutoff R q) * realMoebiusStep a)) =
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
          ((1 / (q : ℝ)) *
            lowOwnerThresholdCrossingIndicator
              p a (rawQ2ChildCutoff R q)) * realMoebiusStep a := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
    _ = ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 / (q : ℝ)) *
            lowOwnerThresholdCrossingIndicator
              p a (rawQ2ChildCutoff R q)) * realMoebiusStep a := by
      rw [Finset.sum_comm]
    _ = ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerDaughterCrossingWeight R p a * realMoebiusStep a := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [← Finset.sum_mul]
      rw [← lowOwnerDaughterCrossingWeight_eq_threshold_sum R p a]

/-- The root channel is the same threshold process evaluated at `R-1`. -/
theorem lowOwnerFirstOwnerThresholdAmplitude_R_sub_one
    {R p : ℕ} {sig : Finset ℕ} (hR : 1 ≤ R) :
    lowOwnerFirstOwnerThresholdAmplitude R p sig (R - 1) =
      ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerRootCrossingIndicator R p a * realMoebiusStep a := by
  unfold lowOwnerFirstOwnerThresholdAmplitude
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← lowOwnerRootCrossingIndicator_eq_threshold_R_sub_one hR]

/-- **Exact finite threshold evaluation of one compensated first-owner cell.**
This is the kernel experiment's identity on the actual finite support, with the
root atom at `R-1`. -/
theorem lowOwnerFirstOwnerCompensatedInterior_eq_finiteThresholdEval
    {R p : ℕ} {sig : Finset ℕ} (hR : 1 ≤ R) :
    lowOwnerFirstOwnerCompensatedInteriorAmplitude R p sig =
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          lowOwnerFirstOwnerThresholdAmplitude
            R p sig (rawQ2ChildCutoff R q)) -
        lowOwnerFirstOwnerThresholdAmplitude R p sig (R - 1) := by
  unfold lowOwnerFirstOwnerCompensatedInteriorAmplitude
  have hd := lowOwnerFirstOwnerDaughterChannels_eq_crossingAmplitude R p sig
  have hr := lowOwnerFirstOwnerThresholdAmplitude_R_sub_one
    (R := R) (p := p) (sig := sig) hR
  calc
    (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
      (lowOwnerDaughterCrossingWeight R p a -
        lowOwnerRootCrossingIndicator R p a) * realMoebiusStep a) =
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerDaughterCrossingWeight R p a * realMoebiusStep a) -
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerRootCrossingIndicator R p a * realMoebiusStep a) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _ha
          ring
    _ = _ := by rw [← hd, ← hr]

/-- One compensated signed site is exactly the incidence gradient of the finite
threshold potential, multiplied by the physical Möbius sign. -/
theorem lowOwnerFirstOwnerCompensatedSite_eq_thresholdIncidence
    {R p a : ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerCompensatedSite R p a =
      (lowOwnerThresholdPotential R a -
          lowOwnerThresholdPotential R (p * a)) * realMoebiusStep a := by
  unfold lowOwnerFirstOwnerCompensatedSite
  rw [lowOwnerThresholdPotential_sub_mul hp.one_le]

/-- Beyond the physical endpoint every daughter indicator vanishes. -/
theorem lowOwnerReciprocalDaughterWeight_eq_zero_of_endpoint_lt
    {R n : ℕ} (hn : squareRootEndpoint R < n) :
    lowOwnerReciprocalDaughterWeight R n = 0 := by
  unfold lowOwnerReciprocalDaughterWeight
  apply Finset.sum_eq_zero
  intro q _hq
  have hY : rawQ2ChildCutoff R q ≤ squareRootEndpoint R := by
    unfold rawQ2ChildCutoff
    exact Nat.div_le_self _ _
  have hnot : ¬ n ≤ rawQ2ChildCutoff R q := by omega
  simp [hnot]

/-- A clipped child has zero threshold potential.  Thus clipping is literally a
Dirichlet boundary of the incidence lift, not a new residual coordinate. -/
theorem lowOwnerThresholdPotential_eq_zero_of_endpoint_lt
    {R n : ℕ} (hR : 2 ≤ R) (hn : squareRootEndpoint R < n) :
    lowOwnerThresholdPotential R n = 0 := by
  have hRleX : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    apply Nat.le_sub_of_add_le
    nlinarith
  have hRn : R ≤ n := hRleX.trans (Nat.le_of_lt hn)
  unfold lowOwnerThresholdPotential
  rw [lowOwnerReciprocalDaughterWeight_eq_zero_of_endpoint_lt hn]
  simp [Nat.not_lt_of_ge hRn]

/-- On a clipped owner edge the incidence gradient has exactly one surviving
endpoint. -/
theorem lowOwnerThresholdPotential_sub_mul_eq_parent_of_clipped
    {R p a : ℕ} (hR : 2 ≤ R)
    (hclip : squareRootEndpoint R < p * a) :
    lowOwnerThresholdPotential R a -
        lowOwnerThresholdPotential R (p * a) =
      lowOwnerThresholdPotential R a := by
  rw [lowOwnerThresholdPotential_eq_zero_of_endpoint_lt hR hclip]
  ring

end RHLean.Proof
