import Mathlib
import «research.CANONICAL_ROUGH_Q2_TAIL_REDUCTION»
import RHLean.Proof.PostRootPartnerLogAlignment

/-!
# Exact scalar cancellation of the nonrecursive q^2 owner tail

PR #706 proves that every odd q^2 owner with `q^2 >= R` has daughter cutoff

  Y_q = floor((R^2-1)/q^2) < R.

At the signed scalar-synthesis level one can say more.  Since `Y_q < R`, the
far-prime portion of that owner's high-transport column is empty: no prime
`p > R+7` can also satisfy `p <= Y_q`.  Hence the near high-transport is the
entire high-transport column.  The already-compiled prime coboundary

  High_q = Go_q - M(Y_q)

then gives the exact cancellation

  M(Y_q) + NearHigh_q - Go_q = 0.

Thus the nonrecursive high-owner q^2 tail disappears algebraically from the
`Mertens + near transport - Go` part of the ownerwise synthesis before any
norm is taken.  This does *not* cancel the stable-far crossing-renewal/terminal
seam, whose source uses first-power q geometry; no LOW-A estimate is asserted.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A high q^2 owner has no far-prime high-transport population at all. -/
theorem q2DaughterFarHighTransport_eq_zero_of_mem_highQ2Owners
    {R q : ℕ} (hR : 2 ≤ R)
    (hq : q ∈ canonicalRoughHighQ2Owners R) :
    q2DaughterFarHighTransport R q = 0 := by
  have hY : rawQ2ChildCutoff R q < R :=
    rawQ2ChildCutoff_lt_parent_of_mem_highQ2Owners hR hq
  have hempty :
      frozenPrimeUniverseHighPrimeSet (R + 7)
          (squareRootEndpoint R / (q * q)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
    have hpLower : R + 7 < p := hpData.2.1
    have hpUpper : p ≤ squareRootEndpoint R / (q * q) := hpData.2.2
    have hY' : squareRootEndpoint R / (q * q) < R := by
      simpa [rawQ2ChildCutoff] using hY
    omega
  unfold q2DaughterFarHighTransport
  rw [hempty]
  simp

/-- Therefore `near` is the whole high-transport column for every high q^2
owner. -/
theorem q2DaughterNearHighTransport_eq_highTransport_of_mem_highQ2Owners
    {R q : ℕ} (hR : 2 ≤ R)
    (hq : q ∈ canonicalRoughHighQ2Owners R) :
    q2DaughterNearHighTransport R q =
      q2DaughterHighTransport q (squareRootEndpoint R) := by
  unfold q2DaughterNearHighTransport
  rw [q2DaughterFarHighTransport_eq_zero_of_mem_highQ2Owners hR hq]
  ring

/-- **Exact high-owner scalar cancellation.**  The q^2 Mertens daughter,
near high-transport, and Go source cancel identically on every odd owner with
`q^2 >= R`.  No lower-envelope estimate and no norm is used. -/
theorem highQ2Owner_mertens_add_near_sub_go_eq_zero
    {R q : ℕ} (hR : 2 ≤ R)
    (hq : q ∈ canonicalRoughHighQ2Owners R) :
    (((mertensSummatoryInt (squareRootEndpoint R / (q * q)) : ℤ) : ℂ)) +
        (((q2DaughterNearHighTransport R q : ℤ) : ℂ)) -
        (((squareRootLowPrimeGoWallSquareResidual q
          (squareRootEndpoint R) : ℤ) : ℂ)) = 0 := by
  have hbase := (Finset.mem_filter.mp hq).1
  have hqPrime := (mem_primesUpTo.mp (Finset.mem_erase.mp hbase).2).1
  have hnear :=
    q2DaughterNearHighTransport_eq_highTransport_of_mem_highQ2Owners hR hq
  have hcob := q2DaughterHighTransport_eq_go_sub_mertens_all
    (q := q) (X := squareRootEndpoint R) hqPrime
  rw [hnear, hcob]
  push_cast
  ring

/-- The complete nonrecursive odd-owner scalar tail is therefore zero before
energy. -/
theorem sum_highQ2Owner_mertens_add_near_sub_go_eq_zero
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ q ∈ canonicalRoughHighQ2Owners R,
      ((((mertensSummatoryInt (squareRootEndpoint R / (q * q)) : ℤ) : ℂ)) +
        (((q2DaughterNearHighTransport R q : ℤ) : ℂ)) -
        (((squareRootLowPrimeGoWallSquareResidual q
          (squareRootEndpoint R) : ℤ) : ℂ)))) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  exact highQ2Owner_mertens_add_near_sub_go_eq_zero hR hq

end RHLean.Proof
