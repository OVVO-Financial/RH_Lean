import Mathlib
import RHLean.Proof.PrefixCarrierOthelloWalls
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_CLIPPED_FUBINI»

/-!
# A threshold crossing wall is exactly a Mertens amplitude

For a fixed prime p and cutoff y, the p-free half-open crossing

  n <= y < p*n

is precisely the upper Othello wall of the positive prefix (0,y].  At lower
anchor zero the anchor wall is empty.  The global Othello identity therefore
says that the signed crossing wall is the whole Mertens prefix.

This is an exact pre-square identity.  No PNT, prime-gap estimate, absolute
value, or norm is used.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The p-free upper threshold wall at cutoff y. -/
def lowOwnerThresholdMertensCrossingCarrier
    (p y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter fun n =>
    ¬ p ∣ n ∧ y < p * n

/-- The threshold carrier is literally the zero-anchor Othello cutoff wall. -/
theorem lowOwnerThresholdMertensCrossingCarrier_eq_cutoffWall
    (p y : ℕ) :
    lowOwnerThresholdMertensCrossingCarrier p y =
      primeCarrierCutoffWall p 0 y := by
  ext n
  simp [lowOwnerThresholdMertensCrossingCarrier,
    primeCarrierCutoffWall, Nat.mul_comm]
  omega

/-- At zero anchor there is no lower Othello wall. -/
@[simp] theorem primeCarrierAnchorWall_zero (p y : ℕ) :
    primeCarrierAnchorWall p 0 y = ∅ := by
  ext n
  simp [primeCarrierAnchorWall]
  omega

/-- The positive prefix (0,y] is the usual 1,...,y carrier. -/
theorem Ioc_zero_eq_Icc_one (y : ℕ) :
    Finset.Ioc 0 y = Finset.Icc 1 y := by
  ext n
  simp
  omega

/-- **Exact signed threshold-wall reconstruction of Mertens.** -/
theorem sum_moebius_thresholdMertensCrossingCarrier_eq_mertens
    {p y : ℕ} (hp : p.Prime) :
    (∑ n ∈ lowOwnerThresholdMertensCrossingCarrier p y, μ n) =
      mertensSummatoryInt y := by
  have h := sum_moebius_Ioc_eq_wallMass hp 0 y
  rw [primeCarrierAnchorWall_zero, Finset.sum_empty, zero_add,
    ← lowOwnerThresholdMertensCrossingCarrier_eq_cutoffWall,
    Ioc_zero_eq_Icc_one, ← mertensSummatoryInt_eq_Icc] at h
  exact h.symm

/-- Real-valued form used by the returned-core amplitude chain. -/
theorem sum_realMoebius_thresholdMertensCrossingCarrier_eq_mertens
    {p y : ℕ} (hp : p.Prime) :
    (∑ n ∈ lowOwnerThresholdMertensCrossingCarrier p y,
      realMoebiusStep n) =
      (mertensSummatoryInt y : ℝ) := by
  have h :=
    sum_moebius_thresholdMertensCrossingCarrier_eq_mertens
      (p := p) (y := y) hp
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at hcast
  simpa [realMoebiusStep] using hcast

/-- On the p-free positive prefix, the half-open threshold indicator is exactly
the cutoff-wall characteristic function. -/
theorem sum_pFree_thresholdCrossing_eq_mertens
    {p y : ℕ} (hp : p.Prime) :
    (∑ n ∈ Finset.Icc 1 y,
      if ¬ p ∣ n then
        realMoebiusStep n *
          lowOwnerThresholdCrossingIndicator p n y
      else 0) =
      (mertensSummatoryInt y : ℝ) := by
  rw [← sum_realMoebius_thresholdMertensCrossingCarrier_eq_mertens hp]
  unfold lowOwnerThresholdMertensCrossingCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hnIcc := Finset.mem_Icc.mp hn
  by_cases hfree : ¬ p ∣ n
  · by_cases hcross : y < p * n
    · have hind :
          lowOwnerThresholdCrossingIndicator p n y = 1 := by
        unfold lowOwnerThresholdCrossingIndicator
        simp [hnIcc.2, hcross]
      simp [hfree, hcross, hind]
    · have hnot : ¬ (n ≤ y ∧ y < p * n) := by
        intro hh
        exact hcross hh.2
      have hind :
          lowOwnerThresholdCrossingIndicator p n y = 0 := by
        unfold lowOwnerThresholdCrossingIndicator
        simp [hnot]
      simp [hfree, hcross, hind]
  · simp [hfree]

end RHLean.Proof
