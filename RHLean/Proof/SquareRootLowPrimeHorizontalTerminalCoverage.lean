import Mathlib
import RHLean.Proof.SquareRootLowPrimeHorizontalOwnerFallout

/-!
# Terminal coverage by first missing-child owners

The horizontal owner slices of `SquareRootLowPrimeHorizontalOwnerFallout` are
already disjoint.  This file identifies the remaining coverage gate for the
actual terminal matching frontier.

If a terminal survivor has a chronological coordinate `p` for which

* `p` is fresh for its cofactor, and
* `P+(cofactor) < p`,

then its `p`-child cannot still be present in the row entering the `p` stage.
Otherwise the survivor would be a lower endpoint of an available `p` pair and
would be removed at that stage.  Hence the survivor is literal canonical
missing-child fallout at `p`.

An induction over the prefix shows that the first-owner construction assigns the
survivor either to an earlier fallout owner or to `p` itself.  Thus no ancestry
or chain parity is needed.  The only remaining coverage obligation is the
arithmetic existence of one eligible chronological owner for every non-head
terminal survivor.

Under that one hypothesis the non-head terminal frontier is exactly the
disjoint union of its first-fallout owner slices, and its signed mass is exactly
the sum of those slice masses.  No fallout slice is declared zero.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- A terminal survivor with an eligible coordinate `p` is necessarily a
canonical missing-child fallout state in the row entering the `p` stage. -/
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

/-- If a target state meets canonical fallout at a stated stage, the recursive
first-owner construction assigns it no later than that stage.  Earlier owners
may already have taken it; otherwise it remains unassigned until `p`. -/
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

/-- A terminal target state with one eligible chronological owner belongs to the
disjoint first-fallout support. -/
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

/-- If every non-head terminal survivor has an eligible chronological fresh
coordinate, the disjoint first-fallout slices cover the whole non-head terminal
target.  This is the remaining arithmetic existence gate. -/
theorem squareRootLowPrimeProcessedSeatNonHeadTerminal_firstFalloff_cover
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (howner : ∀ x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalTarget ps S,
      ∃ pre p post,
        ps = pre ++ p :: post ∧
          (¬ p ∣ squareRootLowPrimeProcessedStateCofactor x) ∧
          canonicalLargestPrimeFactor
            (squareRootLowPrimeProcessedStateCofactor x) < p) :
    ∀ x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalTarget ps S,
      x ∈ squareRootLowPrimeProcessedSeatFirstFalloffSupport ps S
        (squareRootLowPrimeProcessedSeatNonHeadTerminalTarget ps S) := by
  intro x hxT
  have hxErase := Finset.mem_erase.mp hxT
  rcases howner x hxT with
    ⟨pre, p, post, hps, hpFresh, hlpf⟩
  have hxTerminal :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier
        (pre ++ p :: post) S := by
    rw [← hps]
    exact hxErase.2
  rw [hps]
  exact squareRootLowPrimeProcessedSeatTerminal_mem_firstFalloffSupport_of_stage
    pre post S
      (squareRootLowPrimeProcessedSeatNonHeadTerminalTarget
        (pre ++ p :: post) S)
      hxTerminal (by simpa [hps] using hxT) hxErase.1 hpFresh hlpf

/-- Under the explicit owner-existence gate, the non-head terminal frontier has
exact signed mass equal to the sum of its disjoint first-fallout slice masses. -/
theorem squareRootLowPrimeProcessedSeatNonHeadTerminal_weight_sum_eq_firstFalloffMass
    (ps : List ℕ) (S : Finset SquareRootLowPrimeProcessedState)
    (howner : ∀ x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalTarget ps S,
      ∃ pre p post,
        ps = pre ++ p :: post ∧
          (¬ p ∣ squareRootLowPrimeProcessedStateCofactor x) ∧
          canonicalLargestPrimeFactor
            (squareRootLowPrimeProcessedStateCofactor x) < p) :
    (∑ x ∈ squareRootLowPrimeProcessedSeatNonHeadTerminalTarget ps S,
      squareRootLowPrimeProcessedSeatWeightReal x) =
      squareRootLowPrimeProcessedSeatFirstFalloffMass ps S
        (squareRootLowPrimeProcessedSeatNonHeadTerminalTarget ps S) := by
  apply squareRootLowPrimeProcessedSeatTarget_weight_sum_eq_firstFalloffMass_of_covered
  exact squareRootLowPrimeProcessedSeatNonHeadTerminal_firstFalloff_cover
    ps S howner

end RHLean.Proof