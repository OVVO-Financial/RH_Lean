import RHLean.Proof.VanishingTransitionRelevanceBase

/-!
# Canonical first-jump prime slices

The first-jump residual of every oriented state is already a disjoint signed
sum over its canonical first failing prime.  This module lifts that exact
partition to the global state carrier without taking norms.  It is the
correct object on which to attempt the next deterministic finite-difference
contraction.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis
open LowWheelCanonicalDowncrossOwnership
open SignedOwnershipInterval

/-- A fixed finite prime universe containing every predecessor prime that can
occur in an oriented state at root `R`. -/
def firstJumpPrimeUniverse (R : ℕ) : Finset ℕ :=
  primesUpTo (squareRootEndpoint R)

/-- Signed contribution of one canonical first-jump prime to one oriented
state.  The state sign is kept outside the predecessor slice. -/
noncomputable def signedFirstJumpPrimeStateSlice
    (R p : ℕ) (x : LowWheelCofactorQuotientState) : ℂ :=
  if h : (lowWheelCanonicalDowncrossOrientedChargingFaces R x).Nonempty ∧
      Nat.sqrt R < lowWheelCanonicalDowncrossPivot x then
    if hp : p ∈ primesUpTo (lowWheelCanonicalDowncrossPivot x - 1) then
      canonicalMoebiusWeight x.1 *
        ((predecessorFirstJumpFrozenWindowSliceMass
          3 (Nat.sqrt R)
          (primesUpTo (lowWheelCanonicalDowncrossPivot x - 1))
          (R / x.2)
          (lowWheelCanonicalDowncrossOwnershipUpper R x.1 x.2)
          p : ℤ) : ℂ)
    else 0
  else 0

/-- Global signed mass owned by one canonical first-jump prime. -/
def signedFirstJumpPrimeSliceAggregate (R p : ℕ) : ℂ :=
  ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
    signedFirstJumpPrimeStateSlice R p x

/-- The local predecessor prime set of every actual oriented state is contained
in the common finite prime universe. -/
theorem predecessorPrimeSet_subset_firstJumpPrimeUniverse
    {R : ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R) :
    primesUpTo (lowWheelCanonicalDowncrossPivot x - 1) ⊆
      firstJumpPrimeUniverse R := by
  classical
  rcases x with ⟨c, k⟩
  have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
  have hne := hxData.2
  have hkPivot : k = lowWheelCanonicalDowncrossPivot (c, k) :=
    lowWheelCanonicalDowncrossOrientedChargingFaces_quotient_eq_pivot hne
  have hkMem := (Finset.mem_product.mp hxData.1).2
  have hkLe : k ≤ squareRootEndpoint R := (Finset.mem_Icc.mp hkMem).2
  intro p hp
  rcases mem_primesUpTo.mp hp with ⟨hpPrime, hpLe⟩
  apply mem_primesUpTo.mpr
  refine ⟨hpPrime, ?_⟩
  omega

/-- For one actual state, the complete first-jump fibre is exactly the signed
sum of its canonical prime slices over the common universe. -/
theorem lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre_eq_sum_primeSlices
    {R : ℕ} {x : LowWheelCofactorQuotientState}
    (hx : x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R) :
    lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x =
      ∑ p ∈ firstJumpPrimeUniverse R,
        signedFirstJumpPrimeStateSlice R p x := by
  classical
  rcases x with ⟨c, k⟩
  have hxData := mem_lowWheelCanonicalDowncrossOrientedStateCarrier.mp hx
  have hne := hxData.2
  by_cases hroot : Nat.sqrt R < lowWheelCanonicalDowncrossPivot (c, k)
  · have hstate :
        (lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty ∧
          Nat.sqrt R < lowWheelCanonicalDowncrossPivot (c, k) :=
      ⟨hne, hroot⟩
    let S := primesUpTo (lowWheelCanonicalDowncrossPivot (c, k) - 1)
    let A := R / k
    let B := lowWheelCanonicalDowncrossOwnershipUpper R c k
    have hmass :=
      predecessorFirstJumpFrozenWindowMass_eq_sum_slices
        3 (Nat.sqrt R) S A B
    have hcast := congrArg (fun z : ℤ => (z : ℂ)) hmass
    push_cast at hcast
    unfold lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre
    rw [if_pos hstate]
    change canonicalMoebiusWeight c *
        ((predecessorFirstJumpFrozenWindowMass
          3 (Nat.sqrt R) S A B : ℤ) : ℂ) = _
    rw [hcast, Finset.mul_sum]
    have hsubset : S ⊆ firstJumpPrimeUniverse R := by
      simpa [S] using
        (predecessorPrimeSet_subset_firstJumpPrimeUniverse (R := R)
          (x := (c, k)) hx)
    calc
      (∑ p ∈ S,
          canonicalMoebiusWeight c *
            ((predecessorFirstJumpFrozenWindowSliceMass
              3 (Nat.sqrt R) S A B p : ℤ) : ℂ)) =
        ∑ p ∈ S, signedFirstJumpPrimeStateSlice R p (c, k) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [signedFirstJumpPrimeStateSlice, hstate, hp, S, A, B]
      _ = ∑ p ∈ firstJumpPrimeUniverse R,
          signedFirstJumpPrimeStateSlice R p (c, k) := by
          apply Finset.sum_subset hsubset
          intro p hpU hpNot
          simp [signedFirstJumpPrimeStateSlice, hstate, hpNot, S]
  · have hstate :
        ¬((lowWheelCanonicalDowncrossOrientedChargingFaces R (c, k)).Nonempty ∧
          Nat.sqrt R < lowWheelCanonicalDowncrossPivot (c, k)) := by
      simp [hne, hroot]
    simp [lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre,
      signedFirstJumpPrimeStateSlice, hstate]

/-- **Exact global prime-slice Fubini.**  The signed live first-jump aggregate is
literally the sum of its canonical first-jump-prime aggregates.  No norm,
probability model, or PNT estimate occurs in this identity. -/
theorem signedLiveFirstJumpAggregate_eq_sum_primeSlices
    (R : ℕ) :
    signedLiveFirstJumpAggregate R =
      ∑ p ∈ firstJumpPrimeUniverse R,
        signedFirstJumpPrimeSliceAggregate R p := by
  classical
  unfold signedLiveFirstJumpAggregate signedFirstJumpPrimeSliceAggregate
  calc
    (∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre R x) =
      ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
        ∑ p ∈ firstJumpPrimeUniverse R,
          signedFirstJumpPrimeStateSlice R p x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact lowWheelCanonicalDowncrossOrientedFirstJumpStateFibre_eq_sum_primeSlices hx
    _ = ∑ p ∈ firstJumpPrimeUniverse R,
        ∑ x ∈ lowWheelCanonicalDowncrossOrientedStateCarrier R,
          signedFirstJumpPrimeStateSlice R p x := by
        rw [Finset.sum_comm]

/-- A canonical first-jump slice below the predecessor threshold is empty. -/
theorem predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_le_threshold
    {d Y : ℕ} {S : Finset ℕ} {A B p : ℕ}
    (hp : p ≤ Y) :
    predecessorFirstJumpFrozenWindowSliceMass d Y S A B p = 0 := by
  unfold predecessorFirstJumpFrozenWindowSliceMass
  apply Finset.sum_eq_zero
  intro t ht
  have hfirst := (mem_predecessorFirstJumpFrozenWindowSlice.mp ht).2
  have hYp : Y < p := hfirst.2.1
  omega

/-- A canonical first-jump slice above the physical window endpoint is empty
when the prime universe is an actual prime prefix. -/
theorem predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_upper_lt
    {d Y K A B p : ℕ}
    (hBp : B < p) :
    predecessorFirstJumpFrozenWindowSliceMass
        d Y (primesUpTo K) A B p = 0 := by
  unfold predecessorFirstJumpFrozenWindowSliceMass
  apply Finset.sum_eq_zero
  intro t ht
  have hslice := mem_predecessorFirstJumpFrozenWindowSlice.mp ht
  have hfirst := hslice.2
  have hwindow := (mem_predecessorFirstJumpFrozenWindowFaces.mp hslice.1).1
  rcases mem_frozenPrimeUniverseWindowFaces.mp hwindow with
    ⟨htPow, _hlo, hup⟩
  have hprodPos : 0 < primeFaceProduct t :=
    primeFaceProduct_pos_of_mem_powerset htPow
  have hpdvd : p ∣ primeFaceProduct t := by
    change p ∣ t.prod id
    exact Finset.dvd_prod_of_mem id hfirst.1
  have hple : p ≤ primeFaceProduct t := Nat.le_of_dvd hprodPos hpdvd
  omega

/-- Consequently a state slice is zero at primes at or below the root wall. -/
theorem signedFirstJumpPrimeStateSlice_eq_zero_of_le_root
    {R p : ℕ} {x : LowWheelCofactorQuotientState}
    (hp : p ≤ Nat.sqrt R) :
    signedFirstJumpPrimeStateSlice R p x = 0 := by
  classical
  unfold signedFirstJumpPrimeStateSlice
  split_ifs with hstate hpMem
  · rw [predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_le_threshold hp]
    simp
  · rfl
  · rfl

/-- A state slice is also zero above the physical root endpoint `R`; the
ownership window itself is already contained in `[1,R]`. -/
theorem signedFirstJumpPrimeStateSlice_eq_zero_of_root_lt
    {R p : ℕ} {x : LowWheelCofactorQuotientState}
    (hRp : R < p) :
    signedFirstJumpPrimeStateSlice R p x = 0 := by
  classical
  rcases x with ⟨c, k⟩
  unfold signedFirstJumpPrimeStateSlice
  split_ifs with hstate hpMem
  · have hupper : lowWheelCanonicalDowncrossOwnershipUpper R c k ≤ R := by
      unfold lowWheelCanonicalDowncrossOwnershipUpper
      exact (min_le_left _ _).trans (Nat.div_le_self _ _)
    have hBp : lowWheelCanonicalDowncrossOwnershipUpper R c k < p :=
      hupper.trans_lt hRp
    rw [predecessorFirstJumpFrozenWindowSliceMass_eq_zero_of_upper_lt hBp]
    simp
  · rfl
  · rfl

/-- The global prime slice vanishes below the root wall. -/
theorem signedFirstJumpPrimeSliceAggregate_eq_zero_of_le_root
    {R p : ℕ} (hp : p ≤ Nat.sqrt R) :
    signedFirstJumpPrimeSliceAggregate R p = 0 := by
  unfold signedFirstJumpPrimeSliceAggregate
  apply Finset.sum_eq_zero
  intro x _hx
  exact signedFirstJumpPrimeStateSlice_eq_zero_of_le_root hp

/-- The global prime slice vanishes above `R`. -/
theorem signedFirstJumpPrimeSliceAggregate_eq_zero_of_root_lt
    {R p : ℕ} (hp : R < p) :
    signedFirstJumpPrimeSliceAggregate R p = 0 := by
  unfold signedFirstJumpPrimeSliceAggregate
  apply Finset.sum_eq_zero
  intro x _hx
  exact signedFirstJumpPrimeStateSlice_eq_zero_of_root_lt hp

/-- The actual first-jump prime carrier is the post-root prime interval. -/
def signedFirstJumpPostRootPrimeSet (R : ℕ) : Finset ℕ :=
  frozenPrimeUniverseHighPrimeSet (Nat.sqrt R) R

/-- Only primes strictly between the square-root wall and `R` survive in the
global signed first-jump decomposition. -/
theorem signedLiveFirstJumpAggregate_eq_sum_postRootPrimeSlices
    (R : ℕ) (hR : 3 ≤ R) :
    signedLiveFirstJumpAggregate R =
      ∑ p ∈ signedFirstJumpPostRootPrimeSet R,
        signedFirstJumpPrimeSliceAggregate R p := by
  classical
  rw [signedLiveFirstJumpAggregate_eq_sum_primeSlices]
  have hRend : R ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    have hsquare : R + 1 ≤ R ^ 2 := by nlinarith
    omega
  have hsubset : signedFirstJumpPostRootPrimeSet R ⊆ firstJumpPrimeUniverse R := by
    intro p hp
    have hpData := mem_frozenPrimeUniverseHighPrimeSet.mp hp
    unfold firstJumpPrimeUniverse
    exact mem_primesUpTo.mpr ⟨hpData.1, hpData.2.2.trans hRend⟩
  symm
  apply Finset.sum_subset hsubset
  intro p hpU hpNot
  have hpPrime : p.Prime := (mem_primesUpTo.mp hpU).1
  by_cases hpLow : p ≤ Nat.sqrt R
  · exact signedFirstJumpPrimeSliceAggregate_eq_zero_of_le_root hpLow
  · have hpHigh : Nat.sqrt R < p := Nat.lt_of_not_ge hpLow
    have hpNotData : ¬(p.Prime ∧ Nat.sqrt R < p ∧ p ≤ R) := by
      simpa [signedFirstJumpPostRootPrimeSet,
        mem_frozenPrimeUniverseHighPrimeSet] using hpNot
    have hRp : R < p := by
      by_contra hnot
      have hpR : p ≤ R := Nat.le_of_not_gt hnot
      exact hpNotData ⟨hpPrime, hpHigh, hpR⟩
    exact signedFirstJumpPrimeSliceAggregate_eq_zero_of_root_lt hRp

/-- The desired signed live-boundary estimate, with the norm taken only after
all state and Möbius signs have been summed. -/
def PNTFiniteDifferenceLiveExposureBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ‖signedLiveFirstJumpAggregate R‖ ≤
        C * (R : ℝ) * (Real.log (R : ℝ) + 1)

/-- The remaining prime-local quantitative seam.  It asks the iterated Euler
finite differences to control one canonical high-prime slice at its natural
`R/p` seat scale, with one logarithmic overlap allowance. -/
def FirstJumpPrimeSliceFiniteDifferenceBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R p : ℕ, 3 ≤ R → p.Prime → Nat.sqrt R < p → p ≤ R →
      ‖signedFirstJumpPrimeSliceAggregate R p‖ ≤
        C * (((R / p : ℕ) : ℝ)) * (Real.log (R : ℝ) + 1)

end RHLean.Proof
