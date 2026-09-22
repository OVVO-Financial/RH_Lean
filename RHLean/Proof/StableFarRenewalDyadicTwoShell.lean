import Mathlib
import RHLean.Proof.StableFarWallCrossingOwnerWindow
import RHLean.Proof.SurvivorDyadicStaticCancellation

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

def stableFarRenewalOwnerGeometry
    (R q r e p : ℕ) : Prop :=
  q * r * e * p ≤ squareRootEndpoint R ∧
    squareRootEndpoint R < q * q * r * e * p

def stableFarRenewalOwnerActive
    (R q r e p : ℕ) : Prop :=
  q ∈ primesUpTo (R - 1) ∧ r < q ∧
    stableFarRenewalOwnerGeometry R q r e p

theorem mem_crossingOuterOwnerSet_iff_active
    {R q r e p : ℕ} :
    q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p)) ↔
      stableFarRenewalOwnerActive R q r e p := by
  simp [lowWheelFarPrimeQ2CrossingOuterOwnerSet,
    stableFarRenewalOwnerActive, stableFarRenewalOwnerGeometry]

theorem renewalOwner_child_cut_implies_parent
    {R q r e p : ℕ}
    (hchild : q * r * (2 * e) * p ≤ squareRootEndpoint R) :
    q * r * e * p ≤ squareRootEndpoint R := by
  have hmono : q * r * e * p ≤ q * r * (2 * e) * p := by
    gcongr
    omega
  exact hmono.trans hchild

theorem renewalOwner_parent_cross_implies_child
    {R q r e p : ℕ}
    (hparent : squareRootEndpoint R < q * q * r * e * p) :
    squareRootEndpoint R < q * q * r * (2 * e) * p := by
  have hmono : q * q * r * e * p ≤ q * q * r * (2 * e) * p := by
    gcongr
    omega
  exact hparent.trans_le hmono

theorem renewalOwner_activity_mismatch_iff_two_shells
    {R q r e p : ℕ} :
    ¬ (stableFarRenewalOwnerGeometry R q r e p ↔
        stableFarRenewalOwnerGeometry R q r (2 * e) p) ↔
      ((q * r * e * p ≤ squareRootEndpoint R ∧
          squareRootEndpoint R < q * q * r * e * p ∧
          ¬ (q * r * (2 * e) * p ≤ squareRootEndpoint R)) ∨
       (q * r * (2 * e) * p ≤ squareRootEndpoint R ∧
          squareRootEndpoint R < q * q * r * (2 * e) * p ∧
          ¬ (squareRootEndpoint R < q * q * r * e * p))) := by
  have hcut :
      q * r * (2 * e) * p ≤ squareRootEndpoint R →
        q * r * e * p ≤ squareRootEndpoint R :=
    renewalOwner_child_cut_implies_parent
  have hcross :
      squareRootEndpoint R < q * q * r * e * p →
        squareRootEndpoint R < q * q * r * (2 * e) * p :=
    renewalOwner_parent_cross_implies_child
  unfold stableFarRenewalOwnerGeometry
  tauto

theorem crossingOuterOwnerSet_membership_mismatch_iff_two_shells
    {R q r e p : ℕ} :
    ¬ (q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p)) ↔
        q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p))) ↔
      (q ∈ primesUpTo (R - 1) ∧ r < q ∧
        ((q * r * e * p ≤ squareRootEndpoint R ∧
            squareRootEndpoint R < q * q * r * e * p ∧
            ¬ (q * r * (2 * e) * p ≤ squareRootEndpoint R)) ∨
         (q * r * (2 * e) * p ≤ squareRootEndpoint R ∧
            squareRootEndpoint R < q * q * r * (2 * e) * p ∧
            ¬ (squareRootEndpoint R < q * q * r * e * p)))) := by
  rw [mem_crossingOuterOwnerSet_iff_active,
    mem_crossingOuterOwnerSet_iff_active]
  unfold stableFarRenewalOwnerActive
  rw [renewalOwner_activity_mismatch_iff_two_shells]
  tauto

def stableFarCenteredRenewalCoeff
    (R r e p : ℕ) : ℂ :=
  1 - ((lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p))).card : ℂ)

def stableFarCenteredRenewalWeight
    (R r e p : ℕ) : ℂ :=
  stableFarCenteredRenewalCoeff R r e p * canonicalMoebiusWeight e

theorem stableFarCenteredRenewalWeight_add_double
    {R r e p : ℕ} (he : Odd e) :
    stableFarCenteredRenewalWeight R r e p +
        stableFarCenteredRenewalWeight R r (2 * e) p =
      (((lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p))).card : ℂ) -
        ((lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p))).card : ℂ)) *
          canonicalMoebiusWeight e := by
  unfold stableFarCenteredRenewalWeight stableFarCenteredRenewalCoeff
  rw [canonicalMoebiusWeight_two_mul, if_pos he]
  ring

def stableFarRenewalOwnerIndicatorDifference
    (R q r e p : ℕ) : ℤ :=
  (if q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p))
    then 1 else 0) -
  (if q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p))
    then 1 else 0)

theorem renewalOwnerIndicatorDifference_ne_zero_imp_two_shells
    {R q r e p : ℕ}
    (hne : stableFarRenewalOwnerIndicatorDifference R q r e p ≠ 0) :
    q ∈ primesUpTo (R - 1) ∧ r < q ∧
      ((q * r * e * p ≤ squareRootEndpoint R ∧
          squareRootEndpoint R < q * q * r * e * p ∧
          ¬ (q * r * (2 * e) * p ≤ squareRootEndpoint R)) ∨
       (q * r * (2 * e) * p ≤ squareRootEndpoint R ∧
          squareRootEndpoint R < q * q * r * (2 * e) * p ∧
          ¬ (squareRootEndpoint R < q * q * r * e * p))) := by
  have hmismatch :
      ¬ (q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p)) ↔
          q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p))) := by
    intro hiff
    unfold stableFarRenewalOwnerIndicatorDifference at hne
    by_cases hparent :
        q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (e, p))
    · have hchild := hiff.mp hparent
      simp [hparent, hchild] at hne
    · have hchild :
          q ∉ lowWheelFarPrimeQ2CrossingOuterOwnerSet R (r, (2 * e, p)) := by
        intro hc
        exact hparent (hiff.mpr hc)
      simp [hparent, hchild] at hne
  exact (crossingOuterOwnerSet_membership_mismatch_iff_two_shells).mp hmismatch

end RHLean.Proof
