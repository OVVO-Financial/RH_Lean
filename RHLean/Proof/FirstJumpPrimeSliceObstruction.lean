import Mathlib
import RHLean.Proof.OrderedEulerCutProjection
import RHLean.Proof.VanishingTransitionRelevance

/-!
# Upper-half obstruction to a fixed first-jump-prime seat bound

The product-packing reduction in `VanishingTransitionRelevance` is exact, but
its proposed fixed-prime input is too strong.  This file isolates the upper-half
geometry responsible for the obstruction.

For a post-root prime `p` with `R / 2 < p`, the numerical packing factor is
`R / p = 1`.  Nevertheless, the same first-jump prime can remain live under
many later oriented owners `k`.  The first theorem below makes that owner
column literal: every prime

`p < k <= (R^2 - 1) / p`

produces the actual oriented state `(1,k)` carrying the singleton low face
`{p}`.  The next step is to identify the `p`-slice on each such state with
`-1` and prove that no other state survives in the upper half.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

attribute [local instance] Classical.propDecidable

/-- Later prime owners available to one upper-half first-jump prime. -/
def upperHalfFirstJumpOwnerSet (R p : ℕ) : Finset ℕ :=
  frozenPrimeUniverseHighPrimeSet p (squareRootEndpoint R / p)

@[simp] theorem mem_upperHalfFirstJumpOwnerSet
    {R p k : ℕ} :
    k ∈ upperHalfFirstJumpOwnerSet R p ↔
      k.Prime ∧ p < k ∧ k ≤ squareRootEndpoint R / p := by
  simp [upperHalfFirstJumpOwnerSet, mem_frozenPrimeUniverseHighPrimeSet]

/-- **The upper-half owner column is physically real.**

If `p` is a surviving first-jump prime above `R/2`, every later prime
`k <= (R^2-1)/p` gives an actual oriented state `(1,k)`.  The witness is the
singleton low face `{p}`.  This is an exact lifetime statement; there is no
prime-gap, PNT, iid, or norm estimate here. -/
theorem upperHalfFirstJumpOwner_state_mem
    {R p k : ℕ}
    (hR : 3 ≤ R)
    (hpSet : p ∈ signedFirstJumpPostRootPrimeSet R)
    (hhalf : R / 2 < p)
    (hkSet : k ∈ upperHalfFirstJumpOwnerSet R p) :
    (1, k) ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R := by
  have hpData : p.Prime ∧ Nat.sqrt R < p ∧ p ≤ R := by
    simpa [signedFirstJumpPostRootPrimeSet] using
      (mem_frozenPrimeUniverseHighPrimeSet.mp hpSet)
  have hkData : k.Prime ∧ p < k ∧ k ≤ squareRootEndpoint R / p :=
    mem_upperHalfFirstJumpOwnerSet.mp hkSet
  let y : OrderedEulerCutTaggedState := (({p} : Finset ℕ), (1, k))
  have hshape : OrderedEulerCutShape y := by
    dsimp [y, OrderedEulerCutShape]
    refine ⟨hkData.1, by norm_num, by simp, ?_, ?_, ?_⟩
    · intro hdiv
      have hkOne : k = 1 := Nat.dvd_one.mp hdiv
      exact hkData.1.ne_one hkOne
    · intro q hq
      have hqp : q = p := by simpa using hq
      subst q
      exact ⟨hpData.1, hkData.2.1⟩
    · simp [RoughAbove]
  have hkp : k * p ≤ squareRootEndpoint R :=
    (Nat.le_div_iff_mul_le hpData.1.pos).1 hkData.2.2
  have hchild : orderedEulerCutChildInteger y ≤ squareRootEndpoint R := by
    simpa [y, orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
      orderedEulerCutPivot, orderedEulerCutLowProduct, primeFaceProduct] using hkp
  have hsqrt : Nat.sqrt (orderedEulerCutChildInteger y) < R :=
    (orderedEulerCutChild_le_endpoint_iff (R := R) hshape).1 hchild
  have hbirth : orderedEulerCutBirthRoot y ≤ R := by
    unfold orderedEulerCutBirthRoot
    apply Nat.max_le.mpr
    constructor
    · simpa [y, orderedEulerCutLowProduct, primeFaceProduct] using hpData.2.2
    · apply Nat.max_le.mpr
      constructor
      · dsimp [y, orderedEulerCutHighCofactor]
        omega
      · exact Nat.succ_le_iff.mpr hsqrt
  have hR2p : R < p * 2 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 hhalf
  have hp2k : p * 2 ≤ p * k :=
    Nat.mul_le_mul_left p hkData.1.two_le
  have hdeathNat : R < k * p := by
    calc
      R < p * 2 := hR2p
      _ ≤ p * k := hp2k
      _ = k * p := by omega
  have hdeath : R < orderedEulerCutDeathRoot y := by
    simpa [y, orderedEulerCutDeathRoot, orderedEulerCutPivot,
      orderedEulerCutLowProduct, primeFaceProduct] using hdeathNat
  have hocc : OrderedEulerCutOccursAt R y :=
    (orderedEulerCutOccursAt_iff_lifetime hshape).2 ⟨hbirth, hdeath⟩
  have hcharge :
      ({p} : Finset ℕ) ∈
        lowWheelCanonicalDowncrossOrientedChargingFaces R (1, k) := by
    exact mem_lowWheelCanonicalDowncrossOrientedChargingFaces.mpr hocc
  exact mem_orientedStateCarrier_of_chargingFaces_nonempty ⟨{p}, hcharge⟩

end RHLean.Proof
