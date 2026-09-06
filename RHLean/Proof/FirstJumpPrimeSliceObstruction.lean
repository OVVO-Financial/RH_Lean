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
`{p}`.  The second step shows that, once the owner window is below `2p`, the
entire canonical `p`-slice is literally the singleton Boolean face `{p}` and
therefore has signed mass `-1`.
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

/-- **Upper-half first-jump slices are singleton faces.**

The repository already proves that a square-root first-jump face has no later
high-prime tail.  If moreover the full window lies below `2p`, it cannot contain
any earlier prime coordinate either: adjoining any prime `r >= 2` to `p` would
force the face product to at least `2p`.  Thus the complete canonical `p`-slice
is exactly `{{p}}`. -/
theorem upperHalfFirstJumpFrozenWindowSlice_eq_singleton
    {R q A B p : ℕ}
    (hpPrime : p.Prime)
    (hpRoot : Nat.sqrt R < p)
    (hpq : p < q)
    (hAp : A < p)
    (hpB : p ≤ B)
    (hBR : B ≤ R)
    (hR2p : R < p * 2) :
    predecessorFirstJumpFrozenWindowSlice
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B p =
      {{p}} := by
  have hpS : p ∈ primesUpTo (q - 1) := by
    exact mem_primesUpTo.mpr ⟨hpPrime, by omega⟩
  have hwindow :
      ({p} : Finset ℕ) ∈
        frozenPrimeUniverseWindowFaces (primesUpTo (q - 1)) A B := by
    apply mem_frozenPrimeUniverseWindowFaces.mpr
    refine ⟨?_, ?_, ?_⟩
    · apply Finset.mem_powerset.mpr
      intro r hr
      have hrp : r = p := by simpa using hr
      simpa [hrp] using hpS
    · simpa [primeFaceProduct] using hAp
    · simpa [primeFaceProduct] using hpB
  have hfirst : IsPredecessorFirstJumpAt 3 (Nat.sqrt R) ({p} : Finset ℕ) p := by
    refine ⟨by simp, hpRoot, ?_, ?_⟩
    · simp [predecessorPrimeFaceProduct, predecessorPrimeFace, primeFaceProduct]
      nlinarith [hpPrime.two_le]
    · intro r hr hrp _hrRoot
      have hrEq : r = p := by simpa using hr
      omega
  have hjump :
      ({p} : Finset ℕ) ∈
        predecessorFirstJumpFrozenWindowFaces
          3 (Nat.sqrt R) (primesUpTo (q - 1)) A B := by
    apply mem_predecessorFirstJumpFrozenWindowFaces.mpr
    refine ⟨hwindow, ?_⟩
    intro hdense
    have hdenseP := hdense p (by simp) hpRoot
    exact (Nat.not_lt_of_ge hdenseP) hfirst.2.2.1
  have hpSlice :
      ({p} : Finset ℕ) ∈
        predecessorFirstJumpFrozenWindowSlice
          3 (Nat.sqrt R) (primesUpTo (q - 1)) A B p :=
    mem_predecessorFirstJumpFrozenWindowSlice.mpr ⟨hjump, hfirst⟩
  ext t
  constructor
  · intro ht
    have hslice := mem_predecessorFirstJumpFrozenWindowSlice.mp ht
    have hwindowT :=
      (mem_predecessorFirstJumpFrozenWindowFaces.mp hslice.1).1
    have htPow := (mem_frozenPrimeUniverseWindowFaces.mp hwindowT).1
    have htSub := Finset.mem_powerset.mp htPow
    have hshape := sqrtFirstJumpSlice_face_eq_insert_predecessor hBR ht
    have hpredEmpty : predecessorPrimeFace t p = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have hrData := mem_predecessorPrimeFace.mp hr
      have hrPrime : r.Prime := prime_of_mem_primesUpTo (htSub hrData.1)
      have hsub : insert p {r} ⊆ t := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · subst z
          exact hslice.2.1
        · subst z
          exact hrData.1
      have hprodLower : p * r ≤ primeFaceProduct t := by
        unfold primeFaceProduct
        have hle := Finset.prod_le_prod_of_subset_of_one_le' hsub (by
          intro z hzt _hzsmall
          exact (prime_of_mem_primesUpTo (htSub hzt)).one_le)
        have hne : p ≠ r := by omega
        simpa [hne, Nat.mul_comm] using hle
      have hprodLeR : primeFaceProduct t ≤ R :=
        (mem_frozenPrimeUniverseWindowFaces.mp hwindowT).2.2.trans hBR
      have htwo : p * 2 ≤ p * r :=
        Nat.mul_le_mul_left p hrPrime.two_le
      have : p * 2 ≤ R := htwo.trans (hprodLower.trans hprodLeR)
      omega
    have htEq : t = {p} := by
      rw [hshape, hpredEmpty]
      simp
    simpa [htEq]
  · intro ht
    have htEq : t = {p} := by simpa using ht
    subst t
    exact hpSlice

/-- Consequently the signed mass of every upper-half frozen `p`-slice is
exactly `-1`; there is no cancellation left inside that fixed owner state. -/
theorem upperHalfFirstJumpFrozenWindowSliceMass_eq_neg_one
    {R q A B p : ℕ}
    (hpPrime : p.Prime)
    (hpRoot : Nat.sqrt R < p)
    (hpq : p < q)
    (hAp : A < p)
    (hpB : p ≤ B)
    (hBR : B ≤ R)
    (hR2p : R < p * 2) :
    predecessorFirstJumpFrozenWindowSliceMass
        3 (Nat.sqrt R) (primesUpTo (q - 1)) A B p = -1 := by
  unfold predecessorFirstJumpFrozenWindowSliceMass
  rw [upperHalfFirstJumpFrozenWindowSlice_eq_singleton
    hpPrime hpRoot hpq hAp hpB hBR hR2p]
  simp [booleanCubeSign]

end RHLean.Proof
