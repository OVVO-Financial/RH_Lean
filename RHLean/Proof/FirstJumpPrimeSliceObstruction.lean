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
      _ = k * p := Nat.mul_comm p k
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
    · have hpCube : Nat.sqrt R < p ^ 3 :=
        hpRoot.trans_le (Nat.le_self_pow (by norm_num : 3 ≠ 0) p)
      simpa [predecessorPrimeFaceProduct, predecessorPrimeFace,
        primeFaceProduct] using hpCube
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
    exact Finset.mem_singleton.mpr htEq
  · intro ht
    have htEq : t = {p} := Finset.mem_singleton.mp ht
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

/-- **Nontrivial cofactors cannot carry an upper-half first jump.**

For `R / 2 < p` and a high-owner state with `c ≠ 1`, the ordered-triangle
classification gives prime inequalities `p < k < c`.  Once `R ≥ 9` we have
`p ≥ 5`, hence

`R^2 - 1 < R^2 < (2p)^2 ≤ p^3 ≤ p*c*k`.

Therefore the physical ownership upper endpoint `X/(c*k)` lies below `p`, so
the complete canonical `p`-slice is empty. -/
theorem upperHalfFirstJumpPrimeStateSlice_eq_zero_of_cofactor_ne_one
    {R p c k : ℕ}
    (hR : 9 ≤ R)
    (hhalf : R / 2 < p)
    (hx : (c, k) ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R)
    (hc : c ≠ 1) :
    signedFirstJumpPrimeStateSlice R p (c, k) = 0 := by
  classical
  unfold signedFirstJumpPrimeStateSlice
  split_ifs with hstate hpMem
  · have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
    have hne := hxData.2
    have hkPivot : k = lowWheelCanonicalDowncrossPivot (c, k) :=
      lowWheelCanonicalDowncrossOrientedChargingFaces_quotient_eq_pivot hne
    have hkRoot : Nat.sqrt R < k := by
      simpa only [← hkPivot] using hstate.2
    have hshape := highOwner_orientedState_shape hx hkRoot
    rcases hshape.2 with hcOne | hcData
    · exact (hc hcOne).elim
    have hpData := mem_primesUpTo.mp hpMem
    have hpLtK : p < k := by omega
    have hp4 : 4 ≤ p := by omega
    have hR2p : R < p * 2 :=
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 hhalf
    have hRsq : R ^ 2 < (p * 2) ^ 2 :=
      Nat.pow_lt_pow_left hR2p (by norm_num : 2 ≠ 0)
    have h4p2 : (p * 2) ^ 2 ≤ p ^ 3 := by
      calc
        (p * 2) ^ 2 = 4 * (p * p) := by ring
        _ ≤ p * (p * p) := Nat.mul_le_mul_right (p * p) hp4
        _ = p ^ 3 := by ring
    have hpk : p ≤ k := Nat.le_of_lt hpLtK
    have hpc : p ≤ c := hpk.trans (Nat.le_of_lt hcData.2)
    have hpcProd : p ^ 3 ≤ p * (c * k) := by
      calc
        p ^ 3 = p * (p * p) := by ring
        _ ≤ p * (c * k) :=
          Nat.mul_le_mul_left p (Nat.mul_le_mul hpc hpk)
    have hXltRsq : squareRootEndpoint R < R ^ 2 := by
      unfold squareRootEndpoint
      have hpos : 0 < R ^ 2 := by positivity
      omega
    have hXlt : squareRootEndpoint R < p * (c * k) :=
      hXltRsq.trans (hRsq.trans_le (h4p2.trans hpcProd))
    have hckPos : 0 < c * k := Nat.mul_pos hcData.1.pos hshape.1.pos
    have hdiv : squareRootEndpoint R / (c * k) < p :=
      (Nat.div_lt_iff_lt_mul hckPos).2 hXlt
    have hupper : lowWheelCanonicalDowncrossOwnershipUpper R c k < p := by
      unfold lowWheelCanonicalDowncrossOwnershipUpper
      exact (min_le_right _ _).trans_lt hdiv
    rw [predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_upper_lt hupper]
    simp
  · rfl
  · rfl

/-- **Every actual owner in the upper-half column contributes exactly `-1`.**
The state sign is `μ(1)=1`; all of the sign is the singleton Boolean flip at
`p`. -/
theorem upperHalfFirstJumpOwner_stateSlice_eq_neg_one
    {R p k : ℕ}
    (hR : 3 ≤ R)
    (hpSet : p ∈ signedFirstJumpPostRootPrimeSet R)
    (hhalf : R / 2 < p)
    (hkSet : k ∈ upperHalfFirstJumpOwnerSet R p) :
    signedFirstJumpPrimeStateSlice R p (1, k) = -1 := by
  classical
  have hpData : p.Prime ∧ Nat.sqrt R < p ∧ p ≤ R := by
    simpa [signedFirstJumpPostRootPrimeSet] using
      (mem_frozenPrimeUniverseHighPrimeSet.mp hpSet)
  have hkData : k.Prime ∧ p < k ∧ k ≤ squareRootEndpoint R / p :=
    mem_upperHalfFirstJumpOwnerSet.mp hkSet
  have hx := upperHalfFirstJumpOwner_state_mem hR hpSet hhalf hkSet
  have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
  have hne := hxData.2
  have hkPivot : k = lowWheelCanonicalDowncrossPivot (1, k) :=
    lowWheelCanonicalDowncrossOrientedChargingFaces_quotient_eq_pivot hne
  have hkRoot : Nat.sqrt R < k := hpData.2.1.trans hkData.2.1
  have hactive :
      (lowWheelCanonicalDowncrossOrientedChargingFaces R (1, k)).Nonempty ∧
        Nat.sqrt R < lowWheelCanonicalDowncrossPivot (1, k) := by
    refine ⟨hne, ?_⟩
    simpa only [← hkPivot] using hkRoot
  have hpMem : p ∈ primesUpTo (lowWheelCanonicalDowncrossPivot (1, k) - 1) := by
    apply mem_primesUpTo.mpr
    refine ⟨hpData.1, ?_⟩
    rw [← hkPivot]
    omega
  have hR2p : R < p * 2 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 hhalf
  have hp2k : p * 2 ≤ p * k :=
    Nat.mul_le_mul_left p hkData.1.two_le
  have hRpk : R < p * k := hR2p.trans_le hp2k
  have hA : R / k < p :=
    (Nat.div_lt_iff_lt_mul hkData.1.pos).2 hRpk
  have hraw : lowWheelCanonicalCofactorQuotientPivot (1, k) = k := by
    simpa [lowWheelCanonicalDowncrossPivot] using hkPivot.symm
  have hBform :
      lowWheelCanonicalDowncrossOwnershipUpper R 1 k =
        min R (squareRootEndpoint R / k) := by
    unfold lowWheelCanonicalDowncrossOwnershipUpper
    rw [hraw]
    simp [hkData.1.ne_zero]
  have hkp : k * p ≤ squareRootEndpoint R :=
    (Nat.le_div_iff_mul_le hpData.1.pos).1 hkData.2.2
  have hpXdiv : p ≤ squareRootEndpoint R / k := by
    apply (Nat.le_div_iff_mul_le hkData.1.pos).2
    simpa [Nat.mul_comm] using hkp
  have hpB : p ≤ lowWheelCanonicalDowncrossOwnershipUpper R 1 k := by
    rw [hBform]
    exact le_min hpData.2.2 hpXdiv
  have hBR : lowWheelCanonicalDowncrossOwnershipUpper R 1 k ≤ R := by
    rw [hBform]
    exact min_le_left _ _
  have hpPivot : p < lowWheelCanonicalDowncrossPivot (1, k) := by
    simpa only [← hkPivot] using hkData.2.1
  have hmass :
      predecessorFirstJumpFrozenWindowSliceMass
          3 (Nat.sqrt R)
          (primesUpTo (lowWheelCanonicalDowncrossPivot (1, k) - 1))
          (R / k)
          (lowWheelCanonicalDowncrossOwnershipUpper R 1 k)
          p = -1 :=
    upperHalfFirstJumpFrozenWindowSliceMass_eq_neg_one
      hpData.1 hpData.2.1 hpPivot hA hpB hBR hR2p
  unfold signedFirstJumpPrimeStateSlice
  rw [if_pos hactive, if_pos hpMem, hmass]
  simp [canonicalMoebiusWeight]

end RHLean.Proof
