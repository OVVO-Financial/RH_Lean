import Mathlib
import RHLean.Proof.SquareRootLowPrimeFirstOwnerFalloutWidth
import RHLean.Proof.SquareRootLowPrimeDescendingPivotStability
import RHLean.Proof.PrimeCombVisualizationDynamics

/-!
# First-owner wall fallout is terminal and has one fresh owner

The exact fallout-width theorem separates intrinsic missing-child states into a
square-wall part and a response-fibre tail.  This file finishes the purely
combinatorial reduction of the square-wall part before any estimate.

A canonical fallout state already survives its own owner step: its child is
missing, so it is not a lower endpoint, and freshness prevents it from being an
upper endpoint.  On a first-owner square wall the parent canonical owner is at
most the shallow cutoff `K`.  Hence there are no scheduled coordinates before
its first owner.  Every later scheduled prime `r` is at least that first owner,
so `X_R < p*c` implies `X_R < r*c`; the `r`-child is intrinsically absent as
well.  The state therefore survives every later canonical matching step.

There is a second collapse.  Since every scheduled prime is strictly above
`K`, the first scheduled owner above any `L <= K` is simply the first element of
the same fresh-prime list.  Thus all first-owner wall states share one fresh
owner.  The wall is not a sum of independent fresh-prime defects.

The next exact step is the Fubini swap of its already-proved born multiplicity
onto the old partner prime `q <= K`, where the inner cofactor interval is the
frozen-prime window underlying `F_{q^-}`.

No norm, cardinality estimate, PNT input, Mertens bound, or RH-equivalent input
is introduced here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Intrinsic canonical fallout automatically survives the matching step at its
own owner. -/
theorem squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_mem_frontierStep
    {S : Finset SquareRootLowPrimeProcessedState} {p : ℕ}
    {x : SquareRootLowPrimeProcessedState}
    (hfall : x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p) :
    x ∈ squareRootLowPrimeProcessedSeatCanonicalFrontierStep S p := by
  rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
    ⟨hxS, _hxHead, hpFresh, hchildMissing, _hrough⟩
  unfold squareRootLowPrimeProcessedSeatCanonicalFrontierStep
  apply Finset.mem_sdiff.mpr
  refine ⟨hxS, ?_⟩
  intro hpaired
  rcases Finset.mem_union.mp hpaired with hlower | hupper
  · have hlower' :=
      squareRootLowPrimeProcessedSeatCanonicalPairLower_subset S p hlower
    exact hchildMissing
      (mem_squareRootLowPrimeProcessedSeatPairLower.mp hlower').2.2.2
  · have hupper' :=
      squareRootLowPrimeProcessedSeatCanonicalPairUpper_subset S p hupper
    exact
      (squareRootLowPrimeProcessedSeat_not_mem_pairUpper_of_fresh hpFresh)
        hupper'

/-- A square-wall `p`-child remains beyond the wall after replacing `p` by any
larger coordinate `r`. -/
theorem squareRootLowPrimeWall_mono
    {R p r c : ℕ} (hpr : p ≤ r)
    (hwall : squareRootEndpoint R < p * c) :
    squareRootEndpoint R < r * c := by
  have hmul : p * c ≤ r * c := Nat.mul_le_mul_right c hpr
  exact hwall.trans_le hmul

/-- Once `r*c` is beyond the square endpoint, no processed seat with that
cofactor can belong to the original carrier. -/
theorem squareRootLowPrimeWall_child_not_mem_processedCarrier
    {R K j U r c s : ℕ}
    (hwall : squareRootEndpoint R < r * c) :
    some (r * c, s) ∉ squareRootLowPrimeProcessedSeatCarrier R K j U := by
  intro hchild
  have hchildAtom :
      (r * c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hchild
  have hrcSigned :=
    (mem_squareRootLowPrimeProcessedSeatAtoms.mp hchildAtom).1
  have hrcRange := (Finset.mem_filter.mp hrcSigned).1
  have hrcUpper := (Finset.mem_Icc.mp hrcRange).2
  omega

/-- If the first-owner cutoff `L` is already at most `K`, its split has an empty
prefix because every scheduled coordinate lies in `(K,U]`. -/
theorem squareRootLowPrimeFirstOwnerAbove_split_of_le_shallowCutoff
    {K U L p : ℕ} (hLK : L ≤ K)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U) L = some p) :
    ∃ post,
      squareRootLowPrimeFreshPrimeList K U = p :: post := by
  rcases squareRootLowPrimeFirstOwnerAbove_some_split hfirst with
    ⟨pre, post, hsplit, hpre, _hLp⟩
  have hpreNil : pre = [] := by
    cases pre with
    | nil => rfl
    | cons q qs =>
        have hqPre : q ∈ q :: qs := by simp
        have hqLeL := hpre q hqPre
        have hqList : q ∈ squareRootLowPrimeFreshPrimeList K U := by
          rw [hsplit]
          simp
        have hqSet : q ∈ squareRootLowPrimeFreshPrimeSet K U := by
          simpa [squareRootLowPrimeFreshPrimeList] using hqList
        have hKq := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hqSet).1).1
        omega
  subst pre
  refine ⟨post, ?_⟩
  simpa using hsplit

/-- Therefore first owners above any two cutoffs already below `K` coincide.
This is the precise single-fresh-owner statement used for the wall population. -/
theorem squareRootLowPrimeFirstOwnerAbove_unique_below_shallowCutoff
    {K U L₁ L₂ p q : ℕ}
    (hL₁K : L₁ ≤ K) (hL₂K : L₂ ≤ K)
    (hp : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U) L₁ = some p)
    (hq : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U) L₂ = some q) :
    p = q := by
  rcases squareRootLowPrimeFirstOwnerAbove_split_of_le_shallowCutoff hL₁K hp with
    ⟨ps, hps⟩
  rcases squareRootLowPrimeFirstOwnerAbove_split_of_le_shallowCutoff hL₂K hq with
    ⟨qs, hqs⟩
  have hhead : p :: ps = q :: qs := hps.symm.trans hqs
  exact List.cons.inj hhead |>.1

/-- A later fresh coordinate sees a first-owner wall state as intrinsic fallout
again.  The current row may have shrunk, but it remains a subset of the original
carrier, and the later child is beyond the same square wall. -/
theorem squareRootLowPrimeFirstOwnerWall_mem_laterFalloff
    {R K j U p r c s : ℕ}
    {S : Finset SquareRootLowPrimeProcessedState}
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hlow : canonicalLargestPrimeFactor c ≤ K)
    (hwall : squareRootEndpoint R < p * c)
    (hrList : r ∈ squareRootLowPrimeFreshPrimeList K U)
    (hS : S ⊆ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hxS : some (c, s) ∈ S)
    (hcPos : 0 < c) :
    some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S r := by
  have hrSet : r ∈ squareRootLowPrimeFreshPrimeSet K U := by
    simpa [squareRootLowPrimeFreshPrimeList] using hrList
  have hrData := Finset.mem_filter.mp hrSet
  have hrPrime : r.Prime := hrData.2
  have hKr : K < r := (Finset.mem_Ioc.mp hrData.1).1
  have hrough : canonicalLargestPrimeFactor c < r := hlow.trans_lt hKr
  have hpr : p ≤ r :=
    squareRootLowPrimeFirstOwnerAbove_le_of_mem hfirst hrList hrough
  have hrFresh : ¬ r ∣ c :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hcPos hrPrime hrough
  have hchildMissing :
      squareRootLowPrimeProcessedSeatExtend r (some (c, s)) ∉ S := by
    intro hchildS
    have hchildCarrier := hS hchildS
    have hwallR : squareRootEndpoint R < r * c :=
      squareRootLowPrimeWall_mono hpr hwall
    apply squareRootLowPrimeWall_child_not_mem_processedCarrier hwallR
    simpa [squareRootLowPrimeProcessedSeatExtend] using hchildCarrier
  exact mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
    ⟨hxS, by simp,
      by simpa [squareRootLowPrimeProcessedStateCofactor] using hrFresh,
      hchildMissing,
      by simpa [squareRootLowPrimeProcessedStateCofactor] using hrough⟩

/-- Once the first wall owner has been processed, the wall state survives every
remaining canonical Euler coordinate. -/
theorem squareRootLowPrimeFirstOwnerWall_survives_tail
    {R K j U p c s : ℕ}
    (post : List ℕ)
    (hpost : ∀ r ∈ post, r ∈ squareRootLowPrimeFreshPrimeList K U)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hlow : canonicalLargestPrimeFactor c ≤ K)
    (hwall : squareRootEndpoint R < p * c)
    (hcPos : 0 < c)
    (S : Finset SquareRootLowPrimeProcessedState)
    (hS : S ⊆ squareRootLowPrimeProcessedSeatCarrier R K j U)
    (hxS : some (c, s) ∈ S) :
    some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier post S := by
  induction post generalizing S with
  | nil =>
      simpa [squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier] using hxS
  | cons r rs ih =>
      have hrList : r ∈ squareRootLowPrimeFreshPrimeList K U :=
        hpost r (by simp)
      have hfallR := squareRootLowPrimeFirstOwnerWall_mem_laterFalloff
        hfirst hlow hwall hrList hS hxS hcPos
      have hxStep :=
        squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_mem_frontierStep
          hfallR
      have hstepSubset :
          squareRootLowPrimeProcessedSeatCanonicalFrontierStep S r ⊆
            squareRootLowPrimeProcessedSeatCarrier R K j U :=
        (squareRootLowPrimeProcessedSeatCanonicalFrontierStep_subset S r).trans hS
      have hrest :
          ∀ q ∈ rs, q ∈ squareRootLowPrimeFreshPrimeList K U := by
        intro q hq
        exact hpost q (by simp [hq])
      exact ih hrest
        (S := squareRootLowPrimeProcessedSeatCanonicalFrontierStep S r)
        hstepSubset hxStep

/-- **First-owner square-wall fallout is already terminal.**

This removes the last subset loss on the wall component: a state assigned to
its first intrinsic owner and lost because `p*c` crosses the square endpoint
survives the complete canonical Euler schedule. -/
theorem squareRootLowPrimeFirstOwnerWall_mem_canonicalTerminal
    {R K j U p c s : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hfall :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hwall : squareRootEndpoint R < p * c) :
    some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U := by
  have hlow := squareRootLowPrimeFirstOwnerFalloff_productWall_forces_lowOwner
    (R := R) (K := K) (j := j) (U := U) (p := p) (c := c) (s := s)
    (by omega) hUR hfirst hfall hwall
  rcases squareRootLowPrimeFirstOwnerAbove_split_of_le_shallowCutoff hlow hfirst with
    ⟨post, hsplit⟩
  rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
    ⟨hxCarrier, hxHead, _hpFresh, _hchildMissing, _hrough⟩
  have hxAtom :
      (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hxCarrier
  have hcSigned := (mem_squareRootLowPrimeProcessedSeatAtoms.mp hxAtom).1
  have hcRange := (Finset.mem_filter.mp hcSigned).1
  have hcOne := (Finset.mem_Icc.mp hcRange).1
  have hcPos : 0 < c := by omega
  have hxStep :=
    squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_mem_frontierStep hfall
  have hstepSubset :
      squareRootLowPrimeProcessedSeatCanonicalFrontierStep
          (squareRootLowPrimeProcessedSeatCarrier R K j U) p ⊆
        squareRootLowPrimeProcessedSeatCarrier R K j U :=
    squareRootLowPrimeProcessedSeatCanonicalFrontierStep_subset _ p
  have hpost :
      ∀ r ∈ post, r ∈ squareRootLowPrimeFreshPrimeList K U := by
    intro r hr
    rw [hsplit]
    simp [hr]
  have htail := squareRootLowPrimeFirstOwnerWall_survives_tail
    (R := R) (K := K) (j := j) (U := U) (p := p) (c := c) (s := s)
    post hpost hfirst hlow hwall hcPos
    (squareRootLowPrimeProcessedSeatCanonicalFrontierStep
      (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    hstepSubset hxStep
  unfold squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier
  rw [hsplit]
  simpa [squareRootLowPrimeProcessedSeatCanonicalMatchingFrontier] using htail

/-- A first-owner wall state is not one of the explicit terminal heads. -/
theorem squareRootLowPrimeFirstOwnerWall_mem_assignedTerminal
    {R K j U p c s : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hfall :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hwall : squareRootEndpoint R < p * c) :
    some (c, s) ∈
      squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U := by
  have hterminal := squareRootLowPrimeFirstOwnerWall_mem_canonicalTerminal
    hR hUR hfirst hfall hwall
  unfold squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal
  apply Finset.mem_sdiff.mpr
  refine ⟨hterminal, ?_⟩
  intro hhead
  have hheadData := Finset.mem_filter.mp hhead
  rcases hheadData.2 with hnone | hnoOwner
  · simp at hnone
  · simp [squareRootLowPrimeProcessedStateCofactor, hfirst] at hnoOwner

/-- **Wall first-owner state lies in the actual terminal first-owner fibre.** -/
theorem squareRootLowPrimeFirstOwnerWall_mem_intrinsicFirstOwnerSlice
    {R K j U p c s : ℕ}
    (hR : 2 ≤ R) (hUR : U < R)
    (hfirst : squareRootLowPrimeFirstOwnerAbove
      (squareRootLowPrimeFreshPrimeList K U)
      (canonicalLargestPrimeFactor c) = some p)
    (hfall :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p)
    (hwall : squareRootEndpoint R < p * c) :
    some (c, s) ∈
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice
        (squareRootLowPrimeFreshPrimeList K U)
        (squareRootLowPrimeProcessedSeatCarrier R K j U)
        (squareRootLowPrimeProcessedSeatCanonicalAssignedTerminal R K j U) p := by
  have hlow := squareRootLowPrimeFirstOwnerFalloff_productWall_forces_lowOwner
    (R := R) (K := K) (j := j) (U := U) (p := p) (c := c) (s := s)
    (by omega) hUR hfirst hfall hwall
  rcases squareRootLowPrimeFirstOwnerAbove_split_of_le_shallowCutoff hlow hfirst with
    ⟨post, hsplit⟩
  have hassigned := squareRootLowPrimeFirstOwnerWall_mem_assignedTerminal
    hR hUR hfirst hfall hwall
  apply mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mpr
  refine ⟨hassigned, ?_⟩
  rw [hsplit]
  simp only [squareRootLowPrimeProcessedSeatIntrinsicFirstOwner]
  simp [hfall]

end RHLean.Proof
