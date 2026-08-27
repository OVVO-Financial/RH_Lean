import Mathlib
import RHLean.Proof.SquareRootLowPrimeHorizontalOwnerFallout

/-!
# Terminal coverage by intrinsic first missing-child owners

The horizontal owner slices of `SquareRootLowPrimeHorizontalOwnerFallout` are
already disjoint, but there are two different notions of a missing child.

* **Stage fallout:** the child is absent from the mutable row entering owner
  `p`.  This is enough to say that a terminal survivor is not paired at that
  stage, but it is not yet an intrinsic boundary: the child may have belonged
  to the original carrier and been consumed by an earlier owner.
* **Intrinsic fallout:** the child is absent from the original carrier itself.
  This is the genuine fixed-owner boundary.  A displaced child is not silently
  inserted into this set.

The first part below retains the stage-fallout lemmas as diagnostics.  They do
not collapse the terminal residual.

The second part defines the actual horizontal cut used for terminal accounting.
For a fixed original carrier `S`, each state has a finite set of intrinsic owner
coordinates.  If that set is nonempty, its least prime is the canonical first
owner.  The fibres of this function are pairwise disjoint by construction and
the target splits exactly into those fibres plus the states with no intrinsic
owner.

For a terminal state in that residual, any later canonical coordinate whose
child belonged to the original carrier is an actual **skip**: the child was
removed by an earlier matching stage.  The existing displacement theorem then
produces the earlier blocker.  Thus displacement is exposed in the residual;
it is never smuggled into `U_p`.

No estimate, chain-parity bound, PNT input, Mertens bound, or RH-equivalent
statement is used here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Mutable-row stage fallout: diagnostic only -/

/-- A terminal survivor with an eligible coordinate `p` is necessarily a
canonical missing-child state in the mutable row entering the `p` stage.

This is a stage statement only.  It does **not** say that the child was absent
from the original carrier. -/
theorem squareRootLowPrimeProcessedSeatTerminal_mem_canonicalOwnerFalloff
    (pre post : List ℕ)
    (S : Finset SquareRootLowPrimeProcessedState)
    {p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
      (pre ++ p :: post) S)
    (hxHead : x ≠ none)
    (hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hlpf : canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p) :
    x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p := by
  have hxRewritten :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier post
        (squareRootLowPrimeProcessedSeatFrontierStep
          (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p) := by
    rw [squareRootLowPrimeProcessedSeatMatchingFrontier_append] at hx
    simpa [squareRootLowPrimeProcessedSeatMatchingFrontier] using hx
  have hxStep :
      x ∈ squareRootLowPrimeProcessedSeatFrontierStep
        (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p :=
    squareRootLowPrimeProcessedSeatMatchingFrontier_subset' post _ hxRewritten
  have hxPre :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre S :=
    (Finset.mem_sdiff.mp hxStep).1
  have hmissing :
      squareRootLowPrimeProcessedSeatExtend p x ∉
        squareRootLowPrimeProcessedSeatMatchingFrontier pre S := by
    intro hchild
    have hxLower :
        x ∈ squareRootLowPrimeProcessedSeatPairLower
          (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p :=
      mem_squareRootLowPrimeProcessedSeatPairLower.mpr
        ⟨hxPre, hxHead, hpFresh, hchild⟩
    exact (Finset.mem_sdiff.mp hxStep).2
      (Finset.mem_union.mpr (Or.inl hxLower))
  exact mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
    ⟨hxPre, hxHead, hpFresh, hmissing, hlpf⟩

/-- If a target state meets mutable-row fallout at a stated stage, the recursive
stage-fallout construction assigns it no later than that stage.  This remains a
bookkeeping fact, not the intrinsic terminal coverage theorem. -/
theorem squareRootLowPrimeProcessedSeatFirstFalloffSupport_of_stageFalloff
    (pre post : List ℕ)
    (S T : Finset SquareRootLowPrimeProcessedState)
    {p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxT : x ∈ T)
    (hfall : x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
      (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p) :
    x ∈ squareRootLowPrimeProcessedSeatFirstFalloffSupport
      (pre ++ p :: post) S T := by
  induction pre generalizing S T with
  | nil =>
      simp only [List.nil_append,
        squareRootLowPrimeProcessedSeatFirstFalloffSupport]
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_inter.mpr
      exact ⟨hxT, by
        simpa [squareRootLowPrimeProcessedSeatMatchingFrontier] using hfall⟩
  | cons q qs ih =>
      simp only [List.cons_append,
        squareRootLowPrimeProcessedSeatFirstFalloffSupport]
      by_cases hxSlice :
          x ∈ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S q
      · exact Finset.mem_union.mpr (Or.inl hxSlice)
      · apply Finset.mem_union.mpr
        right
        exact ih
          (S := squareRootLowPrimeProcessedSeatFrontierStep S q)
          (T := T \ squareRootLowPrimeProcessedSeatFirstFalloffSlice T S q)
          (Finset.mem_sdiff.mpr ⟨hxT, hxSlice⟩)
          (by
            simpa [squareRootLowPrimeProcessedSeatMatchingFrontier] using hfall)

/-- A terminal target state with one eligible chronological coordinate belongs
to the mutable-row first-fallout support.  This theorem is intentionally not
used below to erase the intrinsic residual. -/
theorem squareRootLowPrimeProcessedSeatTerminal_mem_firstFalloffSupport_of_stage
    (pre post : List ℕ)
    (S T : Finset SquareRootLowPrimeProcessedState)
    {p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
      (pre ++ p :: post) S)
    (hxT : x ∈ T)
    (hxHead : x ≠ none)
    (hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hlpf : canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p) :
    x ∈ squareRootLowPrimeProcessedSeatFirstFalloffSupport
      (pre ++ p :: post) S T := by
  apply squareRootLowPrimeProcessedSeatFirstFalloffSupport_of_stageFalloff
    pre post S T hxT
  exact squareRootLowPrimeProcessedSeatTerminal_mem_canonicalOwnerFalloff
    pre post S hx hxHead hpFresh hlpf

/-- Non-head part of an arbitrary processed terminal frontier. -/
def squareRootLowPrimeProcessedSeatNonHeadTerminalTarget
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    Finset SquareRootLowPrimeProcessedState :=
  (squareRootLowPrimeProcessedSeatMatchingFrontier ps S).erase none

/-! ## Intrinsic owner assignment -/

/-- Intrinsic owners of `x`: listed coordinates at which `x` is canonically
fresh and its child is absent from the **original** carrier `S`.

This set is static.  A child removed by an earlier matching stage is not an
intrinsic owner. -/
def squareRootLowPrimeProcessedSeatIntrinsicOwnerSet
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (x : SquareRootLowPrimeProcessedState) : Finset ℕ :=
  ps.toFinset.filter fun p =>
    x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p

@[simp] theorem mem_squareRootLowPrimeProcessedSeatIntrinsicOwnerSet
    {ps : List ℕ} {S : Finset SquareRootLowPrimeProcessedState}
    {x : SquareRootLowPrimeProcessedState} {p : ℕ} :
    p ∈ squareRootLowPrimeProcessedSeatIntrinsicOwnerSet ps S x ↔
      p ∈ ps ∧
        x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p := by
  simp [squareRootLowPrimeProcessedSeatIntrinsicOwnerSet]

/-- Least intrinsic owner, if one exists.  On the increasing fresh-prime list
this is exactly the first chronological intrinsic owner. -/
def squareRootLowPrimeProcessedSeatIntrinsicFirstOwner
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (x : SquareRootLowPrimeProcessedState) : Option ℕ :=
  if h : (squareRootLowPrimeProcessedSeatIntrinsicOwnerSet ps S x).Nonempty then
    some ((squareRootLowPrimeProcessedSeatIntrinsicOwnerSet ps S x).min' h)
  else
    none

/-- A returned first owner is an actual listed intrinsic owner. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_some_mem
    {ps : List ℕ} {S : Finset SquareRootLowPrimeProcessedState}
    {x : SquareRootLowPrimeProcessedState} {p : ℕ}
    (hp : squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = some p) :
    p ∈ squareRootLowPrimeProcessedSeatIntrinsicOwnerSet ps S x := by
  unfold squareRootLowPrimeProcessedSeatIntrinsicFirstOwner at hp
  by_cases h :
      (squareRootLowPrimeProcessedSeatIntrinsicOwnerSet ps S x).Nonempty
  · have hmin :
        (squareRootLowPrimeProcessedSeatIntrinsicOwnerSet ps S x).min' h = p := by
      simpa [h] using hp
    rw [← hmin]
    exact Finset.min'_mem _ h
  · simp [h] at hp

/-- If an intrinsic owner exists, the first-owner option is not empty. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_ne_none_of_mem
    {ps : List ℕ} {S : Finset SquareRootLowPrimeProcessedState}
    {x : SquareRootLowPrimeProcessedState} {p : ℕ}
    (hp : p ∈ squareRootLowPrimeProcessedSeatIntrinsicOwnerSet ps S x) :
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x ≠ none := by
  have hnon :
      (squareRootLowPrimeProcessedSeatIntrinsicOwnerSet ps S x).Nonempty :=
    ⟨p, hp⟩
  unfold squareRootLowPrimeProcessedSeatIntrinsicFirstOwner
  simp [hnon]

/-- Fibre of the canonical first-owner map inside a target population. -/
def squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    (p : ℕ) : Finset SquareRootLowPrimeProcessedState :=
  T.filter fun x =>
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = some p

@[simp] theorem mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice
    {ps : List ℕ} {S T : Finset SquareRootLowPrimeProcessedState}
    {p : ℕ} {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p ↔
      x ∈ T ∧
        squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = some p := by
  simp [squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice]

/-- Intrinsically assigned part of `T`. -/
def squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    Finset SquareRootLowPrimeProcessedState :=
  ps.toFinset.biUnion fun p =>
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p

/-- Honest residual: target states with no intrinsic owner in the original
carrier.  Mutable-row skips remain here. -/
def squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    Finset SquareRootLowPrimeProcessedState :=
  T.filter fun x =>
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = none

@[simp] theorem mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual
    {ps : List ℕ} {S T : Finset SquareRootLowPrimeProcessedState}
    {x : SquareRootLowPrimeProcessedState} :
    x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T ↔
      x ∈ T ∧
        squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x = none := by
  simp [squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual]

/-- Different intrinsic first owners have disjoint fibres. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice_disjoint
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    {p q : ℕ} (hpq : p ≠ q) :
    Disjoint
      (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p)
      (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T q) := by
  rw [Finset.disjoint_left]
  intro x hxp hxq
  have hp :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hxp).2
  have hq :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hxq).2
  apply hpq
  exact Option.some.inj (hp.symm.trans hq)

/-- Every intrinsically assigned state has a unique owner prime. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_existsUnique
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    {x : SquareRootLowPrimeProcessedState}
    (hx : x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T) :
    ∃! p : ℕ,
      p ∈ ps ∧
        x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p := by
  rcases Finset.mem_biUnion.mp hx with ⟨p, hpList, hxp⟩
  refine ⟨p, ⟨by simpa using hpList, hxp⟩, ?_⟩
  intro q hq
  have hpEq :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hxp).2
  have hqEq :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hq.2).2
  exact Option.some.inj (hpEq.symm.trans hqEq)

/-- Assigned intrinsic fibres and honest residual partition the target exactly. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_union_residual
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T ∪
        squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T = T := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hxSupport | hxResidual
    · rcases Finset.mem_biUnion.mp hxSupport with ⟨p, _hp, hxp⟩
      exact
        (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hxp).1
    · exact
        (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mp
          hxResidual).1
  · intro hxT
    cases howner : squareRootLowPrimeProcessedSeatIntrinsicFirstOwner ps S x with
    | none =>
        exact Finset.mem_union.mpr <| Or.inr <|
          mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mpr
            ⟨hxT, howner⟩
    | some p =>
        have hpOwner :=
          squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_some_mem howner
        have hpList : p ∈ ps.toFinset := by
          exact (Finset.mem_filter.mp hpOwner).1
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_biUnion.mpr
        refine ⟨p, hpList, ?_⟩
        exact mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mpr
          ⟨hxT, howner⟩

/-- Assigned intrinsic support is disjoint from the honest residual. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_disjoint_residual
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    Disjoint
      (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T)
      (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T) := by
  rw [Finset.disjoint_left]
  intro x hxSupport hxResidual
  rcases Finset.mem_biUnion.mp hxSupport with ⟨p, _hp, hxp⟩
  have hpSome :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice.mp hxp).2
  have hnone :=
    (mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mp
      hxResidual).2
  rw [hnone] at hpSome
  simp at hpSome

/-- Pairwise disjointness of the owner fibres in the owner index set. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice_pairwise
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    Set.PairwiseDisjoint (↑ps.toFinset)
      (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T) := by
  intro p _hp q _hq hpq
  exact squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice_disjoint
    ps S T hpq

/-- Signed mass of all intrinsic first-owner fibres.  No fibre is asserted to
have zero mass. -/
def squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) : ℝ :=
  ∑ p ∈ ps.toFinset,
    ∑ x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p,
      squareRootLowPrimeProcessedSeatWeightReal x

/-- The intrinsic support mass is exactly the sum of its disjoint owner-fibre
masses. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_weight_sum
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass ps S T := by
  unfold squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass
  rw [Finset.sum_biUnion
    (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice_pairwise ps S T)]

/-- **Intrinsic horizontal mass decomposition.**  The target mass is the sum of
its unique intrinsic first-owner fibres plus the honest skip/head residual. -/
theorem squareRootLowPrimeProcessedSeatTarget_weight_sum_eq_intrinsicFirstOwner_add_residual
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState) :
    (∑ x ∈ T, squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass ps S T +
        ∑ x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T,
          squareRootLowPrimeProcessedSeatWeightReal x := by
  have hdisj :=
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_disjoint_residual
      ps S T
  have hunion :=
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_union_residual
      ps S T
  calc
    (∑ x ∈ T, squareRootLowPrimeProcessedSeatWeightReal x) =
        ∑ x ∈
          (squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T ∪
            squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T),
          squareRootLowPrimeProcessedSeatWeightReal x := by
            rw [hunion]
    _ =
        (∑ x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T,
          squareRootLowPrimeProcessedSeatWeightReal x) +
        ∑ x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T,
          squareRootLowPrimeProcessedSeatWeightReal x :=
      Finset.sum_union hdisj
    _ = squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass ps S T +
        ∑ x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T,
          squareRootLowPrimeProcessedSeatWeightReal x := by
      rw [squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_weight_sum]

/-- Exact intrinsic coverage empties the residual.  Unlike the old stage gate,
this hypothesis requires actual membership in `U_p` relative to the original
carrier. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual_eq_empty_of_covered
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    (hcover : ∀ x ∈ T,
      ∃ p ∈ ps,
        x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p) :
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hxResidual
  have hxData :=
    mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mp hxResidual
  rcases hcover x hxData.1 with ⟨p, hpList, hfall⟩
  have hpOwner :
      p ∈ squareRootLowPrimeProcessedSeatIntrinsicOwnerSet ps S x :=
    mem_squareRootLowPrimeProcessedSeatIntrinsicOwnerSet.mpr
      ⟨hpList, hfall⟩
  exact
    (squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_ne_none_of_mem hpOwner)
      hxData.2

/-- Under true intrinsic coverage, every target state has exactly one first
owner. -/
theorem squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_unique_of_covered
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    (hcover : ∀ x ∈ T,
      ∃ p ∈ ps,
        x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p) :
    ∀ x ∈ T,
      ∃! p : ℕ,
        p ∈ ps ∧
          x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSlice ps S T p := by
  intro x hxT
  have hresEmpty :=
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual_eq_empty_of_covered
      ps S T hcover
  have hpart :=
    squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport_union_residual
      ps S T
  have hxSupport :
      x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T := by
    have hxUnion :
        x ∈ squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerSupport ps S T ∪
          squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S T := by
      rw [hpart]
      exact hxT
    rcases Finset.mem_union.mp hxUnion with hx | hx
    · exact hx
    · rw [hresEmpty] at hx
      simp at hx
  exact squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_existsUnique
    ps S T hxSupport

/-- Under true intrinsic coverage, the target mass is exactly the sum over the
unique owner fibres. -/
theorem squareRootLowPrimeProcessedSeatTarget_weight_sum_eq_intrinsicFirstOwnerMass_of_covered
    (ps : List ℕ) (S T : Finset SquareRootLowPrimeProcessedState)
    (hcover : ∀ x ∈ T,
      ∃ p ∈ ps,
        x ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p) :
    (∑ x ∈ T, squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerMass ps S T := by
  rw [squareRootLowPrimeProcessedSeatTarget_weight_sum_eq_intrinsicFirstOwner_add_residual]
  rw [squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual_eq_empty_of_covered
    ps S T hcover]
  simp

/-! ## Honest terminal residual = skips or unscheduled heads -/

/-- Intrinsic residual of the actual non-head terminal target. -/
def squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState) :
    Finset SquareRootLowPrimeProcessedState :=
  squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual ps S
    (squareRootLowPrimeProcessedSeatNonHeadTerminalTarget ps S)

/-- If a non-head terminal residual state has an eligible listed coordinate
`p`, then its `p`-child was present in the original carrier.  Hence its failure
at the `p` row is a genuine displacement skip, and the existing theorem
produces a strictly earlier blocker.

This is the exact distinction required for the final coverage proof: such a
state is **not** counted in `U_p`. -/
theorem squareRootLowPrimeProcessedSeatTerminalIntrinsicResidual_has_earlier_blocker
    (ps pre post : List ℕ)
    (S : Finset SquareRootLowPrimeProcessedState)
    {p : ℕ} {x : SquareRootLowPrimeProcessedState}
    (hxResidual :
      x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalIntrinsicResidual ps S)
    (hps : ps = pre ++ p :: post)
    (hpFresh : ¬ p ∣ squareRootLowPrimeProcessedStateCofactor x)
    (hlpf : canonicalLargestPrimeFactor
      (squareRootLowPrimeProcessedStateCofactor x) < p)
    (hpre : ∀ q ∈ pre, q < p) :
    ∃ pre' q post' z,
      pre = pre' ++ q :: post' ∧ q < p ∧
        z ∈ squareRootLowPrimeProcessedSeatMatchingFrontier pre' S ∧
        ((squareRootLowPrimeProcessedSeatExtend p x ∈
              squareRootLowPrimeProcessedSeatPairLower
                (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            z = squareRootLowPrimeProcessedSeatExtend q
              (squareRootLowPrimeProcessedSeatExtend p x)) ∨
          (z ∈ squareRootLowPrimeProcessedSeatPairLower
              (squareRootLowPrimeProcessedSeatMatchingFrontier pre' S) q ∧
            squareRootLowPrimeProcessedSeatExtend p x =
              squareRootLowPrimeProcessedSeatExtend q z)) := by
  have hxResidualData :=
    mem_squareRootLowPrimeProcessedSeatIntrinsicFirstOwnerResidual.mp hxResidual
  have hxTarget := hxResidualData.1
  have hxTargetData := Finset.mem_erase.mp hxTarget
  have hxHead : x ≠ none := hxTargetData.1
  have hxTerminal :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps S :=
    hxTargetData.2
  have hxS : x ∈ S :=
    squareRootLowPrimeProcessedSeatMatchingFrontier_subset' ps S hxTerminal
  have hpList : p ∈ ps := by
    rw [hps]
    simp
  have hnotIntrinsic :
      x ∉ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff S p := by
    intro hfall
    have hpOwner :
        p ∈ squareRootLowPrimeProcessedSeatIntrinsicOwnerSet ps S x :=
      mem_squareRootLowPrimeProcessedSeatIntrinsicOwnerSet.mpr
        ⟨hpList, hfall⟩
    exact
      (squareRootLowPrimeProcessedSeatIntrinsicFirstOwner_ne_none_of_mem hpOwner)
        hxResidualData.2
  have hneighbor : squareRootLowPrimeProcessedSeatExtend p x ∈ S := by
    by_contra hmissing
    apply hnotIntrinsic
    exact mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mpr
      ⟨hxS, hxHead, hpFresh, hmissing, hlpf⟩
  have hxStage :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
        (pre ++ p :: post) S := by
    rw [← hps]
    exact hxTerminal
  exact squareRootLowPrimeProcessedSeatTerminal_neighbor_has_earlier_blocker
    pre post S hxStage hxHead hpFresh hneighbor hpre

end RHLean.Proof
