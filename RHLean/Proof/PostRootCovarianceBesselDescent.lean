import Mathlib
import RHLean.Analysis.MertensCovarianceDescent
import RHLean.Proof.GlobalFirstJumpCriticalCorrelationBridge

open scoped BigOperators

/-!
# Post-root covariance Bessel descent

The post-root prime families from `BlockCovarianceRefinement` are exact lower-scale
copies in pair covariance.  This file keeps all of those copies signed and isolates
what remains of the global covariance after they are removed.

For `p > sqrt W`, the `p`-family covariance is exactly

```text
C(floor(W/p) + 1).
```

Summing those families gives the inherited lower-scale covariance.  The difference
between the global covariance and that inherited sum is the only genuinely new
same-scale quantity.  Green--Kubo rewrites twice that remainder as

```text
|M(W)|^2
  - (Q(W+1) - sum_p Q(floor(W/p)+1))
  - sum_p |M(floor(W/p))|^2.
```

Thus the desired one-sided linear remainder estimate is exactly a Bessel-type
inequality for the largest-prime decomposition.  No norm is taken on the inherited
covariance sum, and no prime-density estimate is inserted.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis

/-- The literal post-root prime coordinates at endpoint `W`. -/
def postRootPrimeFamilySet (W : ℕ) : Finset ℕ :=
  (Finset.Ioc (Nat.sqrt W) W).filter Nat.Prime

@[simp] theorem mem_postRootPrimeFamilySet {W p : ℕ} :
    p ∈ postRootPrimeFamilySet W ↔ Nat.sqrt W < p ∧ p ≤ W ∧ p.Prime := by
  simp [postRootPrimeFamilySet, and_assoc]

/-- Total covariance inherited from the complete post-root prime families. -/
def postRootPrimeFamilyCovarianceTotal (W : ℕ) : ℝ :=
  ∑ p ∈ postRootPrimeFamilySet W,
    realMertensPositiveLagPairSum (W / p + 1)

/-- The same inherited covariance written on the actual prime-family carrier. -/
theorem postRootPrimeFamilyCovarianceTotal_eq_actualFamilies (W : ℕ) :
    postRootPrimeFamilyCovarianceTotal W =
      ∑ p ∈ postRootPrimeFamilySet W,
        largePrimeFamilyPairSum p (W / p + 1) := by
  unfold postRootPrimeFamilyCovarianceTotal
  apply Finset.sum_congr rfl
  intro p hp
  rcases mem_postRootPrimeFamilySet.mp hp with ⟨hpRoot, _hpW, hpPrime⟩
  have hW : W < p * p := (Nat.sqrt_lt).1 hpRoot
  exact (largePrimeFamilyPairSum_postRoot hpPrime hW).symm

/-- The signed same-scale remainder after all complete post-root family
covariances have been removed. -/
def postRootCovarianceRemainder (W : ℕ) : ℝ :=
  realMertensPositiveLagPairSum (W + 1) -
    postRootPrimeFamilyCovarianceTotal W

/-- Sum of the lower-scale Mertens energies carried by the post-root families. -/
def postRootFamilyMertensSquareEnergy (W : ℕ) : ℝ :=
  ∑ p ∈ postRootPrimeFamilySet W,
    ‖mertensSummatory (W / p)‖ ^ 2

/-- Sum of the exact lower-scale squarefree diagonals carried by those families. -/
def postRootFamilyDiagonalEnergy (W : ℕ) : ℝ :=
  ∑ p ∈ postRootPrimeFamilySet W,
    realMertensDiagonal (W / p + 1)

/-- The part of the global squarefree diagonal not already assigned to the
post-root prime families.  The definition is algebraic; no positivity claim is
needed for the identities below. -/
def postRootComplementDiagonalResidual (W : ℕ) : ℝ :=
  realMertensDiagonal (W + 1) - postRootFamilyDiagonalEnergy W

/-- The inherited post-root covariance is exactly one half of lower-scale
Mertens energy minus lower-scale diagonal energy. -/
theorem postRootPrimeFamilyCovarianceTotal_eq_energyDifference (W : ℕ) :
    postRootPrimeFamilyCovarianceTotal W =
      (postRootFamilyMertensSquareEnergy W -
        postRootFamilyDiagonalEnergy W) / 2 := by
  unfold postRootPrimeFamilyCovarianceTotal
    postRootFamilyMertensSquareEnergy postRootFamilyDiagonalEnergy
  simp_rw [realMertensPositiveLagPairSum_eq_norm_sq_sub_diagonal]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]

/-- **Exact Bessel-defect identity.**  Twice the unexplained covariance is the
global Mertens energy minus the complementary diagonal and the complete inherited
lower-scale family energies. -/
theorem two_mul_postRootCovarianceRemainder_eq_besselDefect (W : ℕ) :
    2 * postRootCovarianceRemainder W =
      ‖mertensSummatory W‖ ^ 2 -
        postRootComplementDiagonalResidual W -
        postRootFamilyMertensSquareEnergy W := by
  unfold postRootCovarianceRemainder postRootComplementDiagonalResidual
  rw [realMertensPositiveLagPairSum_eq_norm_sq_sub_diagonal W,
    postRootPrimeFamilyCovarianceTotal_eq_energyDifference W]
  ring

/-- The proposed arithmetic leap in its weakest useful one-sided form: after
removing every complete lower-scale post-root family covariance, the remaining
positive same-scale covariance is only linear in the physical endpoint. -/
def PostRootCovarianceLinearRemainderStatement : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ W : ℕ, 2 ≤ W →
      postRootCovarianceRemainder W ≤ D * (W : ℝ)

/-- Equivalent Bessel form of the same one-sided linear statement. -/
def PostRootCovarianceBesselLinearStatement : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ W : ℕ, 2 ≤ W →
      ‖mertensSummatory W‖ ^ 2 ≤
        postRootComplementDiagonalResidual W +
          postRootFamilyMertensSquareEnergy W +
          2 * D * (W : ℝ)

/-- The covariance-remainder formulation and the Bessel-defect formulation are
literally equivalent; this is only the exact Green--Kubo algebra above. -/
theorem postRootCovarianceLinearRemainder_iff_besselLinear :
    PostRootCovarianceLinearRemainderStatement ↔
      PostRootCovarianceBesselLinearStatement := by
  constructor
  · rintro ⟨D, hD, hrem⟩
    refine ⟨D, hD, ?_⟩
    intro W hW
    have h := hrem W hW
    have hid := two_mul_postRootCovarianceRemainder_eq_besselDefect W
    nlinarith
  · rintro ⟨D, hD, hbessel⟩
    refine ⟨D, hD, ?_⟩
    intro W hW
    have h := hbessel W hW
    have hid := two_mul_postRootCovarianceRemainder_eq_besselDefect W
    nlinarith

/-- The linear remainder statement gives the exact recurrence used by the
exponent-halving bootstrap: global covariance is at most inherited lower-scale
covariance plus a linear same-scale charge. -/
theorem globalCovariance_le_postRootFamilies_add_linear
    (hlin : PostRootCovarianceLinearRemainderStatement) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ W : ℕ, 2 ≤ W →
        realMertensPositiveLagPairSum (W + 1) ≤
          postRootPrimeFamilyCovarianceTotal W + D * (W : ℝ) := by
  rcases hlin with ⟨D, hD, hrem⟩
  refine ⟨D, hD, ?_⟩
  intro W hW
  have h := hrem W hW
  unfold postRootCovarianceRemainder at h
  linarith

end RHLean.Proof
