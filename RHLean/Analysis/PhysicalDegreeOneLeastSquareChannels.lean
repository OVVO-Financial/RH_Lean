import Mathlib
import RHLean.Analysis.PhysicalDegreeOneTransitionEstimate

/-!
# Physical degree-one least-square channels

This is a proof-side decomposition of the structured physical transition defect.
Each adjacent three-slot edge has six active sites

`4k+1, 4k+2, 4k+3, 4k+5, 4k+6, 4k+7`.

If one of those sites has a square prime divisor, `physicalLeastOddSquarePrime`
records the least such prime.  It is an `Option` because an all-squarefree edge
has no square channel.  The active geometry excludes the prime `2`, so every
returned prime is automatically odd.

The defect is then partitioned exactly into the disjoint least-square channels.
The first channel, `p = 3`, is identified with the six residue classes
`k mod 9 = 1,...,6` and its exact nine-edge recurrence is pushed back to a
short Mertens increment.  No estimate or cancellation hypothesis is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- The six active sites on the physical edge from cell `k` to cell `k+1`. -/
def physicalTransitionActiveOffsets : Finset ℕ :=
  {1, 2, 3, 5, 6, 7}

/-- A prime whose square divides at least one of the six active sites of edge `k`. -/
def physicalSquarePrimeAtEdge (k p : ℕ) : Prop :=
  Nat.Prime p ∧
    ∃ a ∈ physicalTransitionActiveOffsets, p * p ∣ 4 * k + a

/-- The least square-prime channel of edge `k`, or `none` when all six active
sites are squarefree.  The least witness is taken over actual prime-square hits;
the physical parity geometry later proves that the witness is always odd. -/
noncomputable def physicalLeastOddSquarePrime (k : ℕ) : Option ℕ :=
  if h : ∃ p, physicalSquarePrimeAtEdge k p then
    some (Nat.find h)
  else
    none

/-- The degree-one observable on the destination cell of edge `k`. -/
def physicalDefectEdgeValue (k : ℕ) : ℤ :=
  threeSlotDegreeOneValue (threeSlotState (k + 1))

/-- The signed least-square channel `D_{p^2}(K)`. -/
def physicalLeastSquareChannel (K p : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K with physicalLeastOddSquarePrime k = some p,
    physicalDefectEdgeValue k

/-- The finite set of least square primes that actually occur among the first
`K` physical edges. -/
def physicalLeastSquarePrimes (K : ℕ) : Finset ℕ :=
  ((Finset.range K).filter fun k => physicalLeastOddSquarePrime k ≠ none).image
    (fun k => (physicalLeastOddSquarePrime k).getD 0)

/-- The `3^2` least-square channel. -/
def physicalD9 (K : ℕ) : ℤ :=
  physicalLeastSquareChannel K 3

/-- The six edge residues carrying a forced `3^2` hit. -/
def physicalNineChannelResidues : Finset ℕ :=
  {1, 2, 3, 4, 5, 6}

private theorem physicalActiveOffset_not_four_dvd
    (k a : ℕ) (ha : a ∈ physicalTransitionActiveOffsets) :
    ¬ 4 ∣ 4 * k + a := by
  intro h
  rw [Nat.dvd_iff_mod_eq_zero] at h
  simp [physicalTransitionActiveOffsets] at ha
  omega

/-- Every prime-square hit in the six active sites is odd. -/
theorem physicalSquarePrimeAtEdge_odd
    {k p : ℕ} (h : physicalSquarePrimeAtEdge k p) : p % 2 = 1 := by
  rcases h with ⟨hp, a, ha, hsq⟩
  have hpne : p ≠ 2 := by
    intro htwo
    subst p
    norm_num at hsq
    exact physicalActiveOffset_not_four_dvd k a ha hsq
  exact hp.mod_two_eq_one_iff_ne_two.mpr hpne

private theorem physicalSquarePrimeAtEdge_three_le
    {k p : ℕ} (h : physicalSquarePrimeAtEdge k p) : 3 ≤ p := by
  have hp := h.1
  have hodd := physicalSquarePrimeAtEdge_odd h
  have hp2 := hp.two_le
  omega

/-- A returned least channel is an actual square-prime hit. -/
theorem physicalLeastOddSquarePrime_some_spec
    {k p : ℕ} (h : physicalLeastOddSquarePrime k = some p) :
    physicalSquarePrimeAtEdge k p := by
  classical
  unfold physicalLeastOddSquarePrime at h
  split at h with
  | isTrue hex =>
      have hp : Nat.find hex = p := by simpa using h
      rw [← hp]
      exact Nat.find_spec hex
  | isFalse _ => simp at h

/-- A returned least channel is no larger than any other square-prime hit. -/
theorem physicalLeastOddSquarePrime_le
    {k p q : ℕ}
    (hp : physicalLeastOddSquarePrime k = some p)
    (hq : physicalSquarePrimeAtEdge k q) : p ≤ q := by
  classical
  unfold physicalLeastOddSquarePrime at hp
  split at hp with
  | isTrue hex =>
      have hfind : Nat.find hex = p := by simpa using hp
      rw [← hfind]
      exact Nat.find_min' hex hq
  | isFalse _ => simp at hp

@[simp] theorem physicalLeastOddSquarePrime_eq_none_iff (k : ℕ) :
    physicalLeastOddSquarePrime k = none ↔
      ¬ ∃ p, physicalSquarePrimeAtEdge k p := by
  classical
  simp [physicalLeastOddSquarePrime]

private theorem no_physicalSquarePrimeAtEdge_iff_squarefree
    (k : ℕ) :
    (¬ ∃ p, physicalSquarePrimeAtEdge k p) ↔
      ∀ a ∈ physicalTransitionActiveOffsets, Squarefree (4 * k + a) := by
  constructor
  · intro h a ha
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hsq
    exact h ⟨p, hp, a, ha, hsq⟩
  · intro h hex
    rcases hex with ⟨p, hp, a, ha, hsq⟩
    exact (Nat.squarefree_iff_prime_squarefree.mp (h a ha) p hp) hsq

/-- The explicit eight physical sign states are exactly the states with no zero
coordinate. -/
@[simp] theorem mem_physicalThreeSlotNonzeroStates_iff
    (i : Fin 27) :
    i ∈ physicalThreeSlotNonzeroStates ↔ IsThreeSlotNonzeroState i := by
  fin_cases i <;>
    norm_num [physicalThreeSlotNonzeroStates, IsThreeSlotNonzeroState,
      chiA, chiB, chiC]

private theorem physicalNonzeroEdge_iff_activeSquarefree
    (k : ℕ) :
    (threeSlotState k ∈ physicalThreeSlotNonzeroStates ∧
        threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates) ↔
      ∀ a ∈ physicalTransitionActiveOffsets, Squarefree (4 * k + a) := by
  rw [mem_physicalThreeSlotNonzeroStates_iff,
    mem_physicalThreeSlotNonzeroStates_iff]
  simp only [IsThreeSlotNonzeroState, chiA_threeSlotState,
    chiB_threeSlotState, chiC_threeSlotState]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, ⟨h5, h6, h7⟩⟩
    have hs1 : Squarefree (4 * k + 1) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h1
    have hs2 : Squarefree (4 * k + 2) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h2
    have hs3 : Squarefree (4 * k + 3) :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h3
    have hs5 : Squarefree (4 * k + 5) := by
      apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
      convert h5 using 1 <;> omega
    have hs6 : Squarefree (4 * k + 6) := by
      apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
      convert h6 using 1 <;> omega
    have hs7 : Squarefree (4 * k + 7) := by
      apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
      convert h7 using 1 <;> omega
    intro a ha
    simp [physicalTransitionActiveOffsets] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs1
    · exact hs2
    · exact hs3
    · exact hs5
    · exact hs6
    · exact hs7
  · intro h
    have hs1 := h 1 (by simp [physicalTransitionActiveOffsets])
    have hs2 := h 2 (by simp [physicalTransitionActiveOffsets])
    have hs3 := h 3 (by simp [physicalTransitionActiveOffsets])
    have hs5 := h 5 (by simp [physicalTransitionActiveOffsets])
    have hs6 := h 6 (by simp [physicalTransitionActiveOffsets])
    have hs7 := h 7 (by simp [physicalTransitionActiveOffsets])
    have h1 : μ (4 * k + 1) ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs1
    have h2 : μ (4 * k + 2) ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs2
    have h3 : μ (4 * k + 3) ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs3
    have h5 : μ (4 * (k + 1) + 1) ≠ 0 := by
      apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
      convert hs5 using 1 <;> omega
    have h6 : μ (4 * (k + 1) + 2) ≠ 0 := by
      apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
      convert hs6 using 1 <;> omega
    have h7 : μ (4 * (k + 1) + 3) ≠ 0 := by
      apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
      convert hs7 using 1 <;> omega
    exact ⟨⟨h1, h2, h3⟩, ⟨h5, h6, h7⟩⟩

/-- `none` is exactly the all-squarefree physical edge, i.e. both endpoints
lie in the eight-state sign sector. -/
theorem physicalLeastOddSquarePrime_eq_none_iff_nonzeroEdge
    (k : ℕ) :
    physicalLeastOddSquarePrime k = none ↔
      threeSlotState k ∈ physicalThreeSlotNonzeroStates ∧
        threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates := by
  rw [physicalLeastOddSquarePrime_eq_none_iff]
  exact (no_physicalSquarePrimeAtEdge_iff_squarefree k).trans
    (physicalNonzeroEdge_iff_activeSquarefree k).symm

private theorem threeSlotTransitionMomentOn_eq_nonzeroDestinationSum
    (F : Finset ℕ) (s : Fin 27) (χ : Fin 27 → ℤ) :
    threeSlotTransitionMomentOn F s χ =
      ∑ k ∈ F with
        threeSlotState k = s ∧
          threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates,
        χ (threeSlotState (k + 1)) := by
  classical
  let E : Finset ℕ := F.filter fun k =>
    threeSlotState k = s ∧
      threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates
  have hmaps : ∀ k ∈ E,
      threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2.2
  have hfiber := Finset.sum_fiberwise_of_maps_to'
    (s := E)
    (t := physicalThreeSlotNonzeroStates)
    (g := fun k => threeSlotState (k + 1))
    hmaps χ
  have hcount : ∀ t ∈ physicalThreeSlotNonzeroStates,
      (∑ k ∈ E with threeSlotState (k + 1) = t, χ t) =
        (threeSlotTransitionCountOn F s t : ℤ) * χ t := by
    intro t ht
    simp [E, threeSlotTransitionCountOn, ht, Finset.filter_filter,
      and_assoc, and_left_comm, and_comm]
  calc
    threeSlotTransitionMomentOn F s χ =
        ∑ t ∈ physicalThreeSlotNonzeroStates,
          (threeSlotTransitionCountOn F s t : ℤ) * χ t := by
            norm_num [threeSlotTransitionMomentOn,
              physicalThreeSlotNonzeroStates]
    _ = ∑ t ∈ physicalThreeSlotNonzeroStates,
          ∑ k ∈ E with threeSlotState (k + 1) = t, χ t := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [hcount t ht]
    _ = ∑ k ∈ E, χ (threeSlotState (k + 1)) := hfiber
    _ = ∑ k ∈ F with
        threeSlotState k = s ∧
          threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates,
        χ (threeSlotState (k + 1)) := by rfl

/-- The conditioned transition mass is literally the destination degree-one sum
on edges whose two endpoints are both in the nonzero sign sector. -/
theorem physicalDegreeOneT_eq_nonzeroEdgeSum (K : ℕ) :
    physicalDegreeOneT K =
      ∑ k ∈ Finset.range K with
        threeSlotState k ∈ physicalThreeSlotNonzeroStates ∧
          threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates,
        physicalDefectEdgeValue k := by
  classical
  let E : Finset ℕ := (Finset.range K).filter fun k =>
    threeSlotState k ∈ physicalThreeSlotNonzeroStates ∧
      threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates
  have hmaps : ∀ k ∈ E, threeSlotState k ∈ physicalThreeSlotNonzeroStates := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2.1
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := E)
    (t := physicalThreeSlotNonzeroStates)
    (g := threeSlotState)
    hmaps physicalDefectEdgeValue
  have hrow : ∀ s ∈ physicalThreeSlotNonzeroStates,
      (∑ k ∈ E with threeSlotState k = s, physicalDefectEdgeValue k) =
        threeSlotTransitionMomentOn
          (Finset.range K) s threeSlotDegreeOneValue := by
    intro s hs
    rw [threeSlotTransitionMomentOn_eq_nonzeroDestinationSum]
    apply Finset.sum_congr
    · ext k
      simp [E, hs, and_assoc, and_left_comm, and_comm]
    · intro k hk
      rfl
  calc
    physicalDegreeOneT K =
        ∑ s ∈ physicalThreeSlotNonzeroStates,
          threeSlotTransitionMomentOn
            (Finset.range K) s threeSlotDegreeOneValue := by
              norm_num [physicalDegreeOneT, threeSlotTransitionDegreeOneMass,
                physicalThreeSlotNonzeroStates]
    _ = ∑ s ∈ physicalThreeSlotNonzeroStates,
          ∑ k ∈ E with threeSlotState k = s, physicalDefectEdgeValue k := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [hrow s hs]
    _ = ∑ k ∈ E, physicalDefectEdgeValue k := hfiber
    _ = ∑ k ∈ Finset.range K with
        threeSlotState k ∈ physicalThreeSlotNonzeroStates ∧
          threeSlotState (k + 1) ∈ physicalThreeSlotNonzeroStates,
        physicalDefectEdgeValue k := by rfl

/-- The conditioned transition mass is the sum over precisely the edges with no
least square-prime channel. -/
theorem physicalDegreeOneT_eq_leastSquareNoneSum (K : ℕ) :
    physicalDegreeOneT K =
      ∑ k ∈ Finset.range K with physicalLeastOddSquarePrime k = none,
        physicalDefectEdgeValue k := by
  rw [physicalDegreeOneT_eq_nonzeroEdgeSum]
  apply Finset.sum_congr
  · ext k
    simp [physicalLeastOddSquarePrime_eq_none_iff_nonzeroEdge]
  · intro k hk
    rfl

/-- The defect is literally the signed destination sum on the square-supported
edges.  No absolute-value splitting has occurred. -/
theorem physicalTransitionD_eq_leastSquareSupportedSum (K : ℕ) :
    physicalTransitionD K =
      ∑ k ∈ Finset.range K with physicalLeastOddSquarePrime k ≠ none,
        physicalDefectEdgeValue k := by
  change
    (∑ k ∈ Finset.range K, physicalDefectEdgeValue k) -
        physicalDegreeOneT K = _
  rw [physicalDegreeOneT_eq_leastSquareNoneSum]
  have hpart := Finset.sum_filter_add_sum_filter_not
    (Finset.range K)
    (fun k => physicalLeastOddSquarePrime k = none)
    physicalDefectEdgeValue
  rw [← hpart]
  ring

/-- Every index appearing in the finite channel set is an odd prime. -/
theorem physicalLeastSquarePrime_mem_spec
    {K p : ℕ} (hp : p ∈ physicalLeastSquarePrimes K) :
    Nat.Prime p ∧ p % 2 = 1 := by
  classical
  rw [physicalLeastSquarePrimes, Finset.mem_image] at hp
  rcases hp with ⟨k, hk, hkp⟩
  have hsome : physicalLeastOddSquarePrime k ≠ none :=
    (Finset.mem_filter.mp hk).2
  cases hleast : physicalLeastOddSquarePrime k with
  | none => exact (hsome hleast).elim
  | some q =>
      have hq : q = p := by simpa [hleast] using hkp
      subst p
      have hspec := physicalLeastOddSquarePrime_some_spec hleast
      exact ⟨hspec.1, physicalSquarePrimeAtEdge_odd hspec⟩

/-- **Exact disjoint channel decomposition.**  The finite index set consists
only of odd primes and each defect-supported edge enters exactly one least
square-prime channel. -/
theorem physicalTransitionD_eq_sum_leastSquareChannels (K : ℕ) :
    physicalTransitionD K =
      ∑ p ∈ physicalLeastSquarePrimes K, physicalLeastSquareChannel K p := by
  classical
  let E : Finset ℕ :=
    (Finset.range K).filter fun k => physicalLeastOddSquarePrime k ≠ none
  let q : ℕ → ℕ := fun k => (physicalLeastOddSquarePrime k).getD 0
  have hmaps : ∀ k ∈ E, q k ∈ physicalLeastSquarePrimes K := by
    intro k hk
    rw [physicalLeastSquarePrimes, Finset.mem_image]
    exact ⟨k, hk, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := E)
    (t := physicalLeastSquarePrimes K)
    (g := q)
    hmaps physicalDefectEdgeValue
  have hchannel : ∀ p ∈ physicalLeastSquarePrimes K,
      (∑ k ∈ E with q k = p, physicalDefectEdgeValue k) =
        physicalLeastSquareChannel K p := by
    intro p hp
    unfold physicalLeastSquareChannel
    apply Finset.sum_congr
    · ext k
      cases hleast : physicalLeastOddSquarePrime k <;>
        simp [E, q, hleast]
    · intro k hk
      rfl
  rw [physicalTransitionD_eq_leastSquareSupportedSum]
  change (∑ k ∈ E, physicalDefectEdgeValue k) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro p hp
  exact hchannel p hp

/-- A `3^2` hit occurs exactly on the six forced residues modulo `9`. -/
theorem physicalSquarePrimeAtEdge_three_iff (k : ℕ) :
    physicalSquarePrimeAtEdge k 3 ↔
      k % 9 ∈ physicalNineChannelResidues := by
  simp [physicalSquarePrimeAtEdge, physicalTransitionActiveOffsets,
    physicalNineChannelResidues, Nat.dvd_iff_mod_eq_zero]
  omega

/-- Because every square-prime channel is at least `3`, a `3^2` hit is
automatically the least channel. -/
theorem physicalLeastOddSquarePrime_eq_three_iff (k : ℕ) :
    physicalLeastOddSquarePrime k = some 3 ↔
      physicalSquarePrimeAtEdge k 3 := by
  constructor
  · exact physicalLeastOddSquarePrime_some_spec
  · intro h3
    classical
    unfold physicalLeastOddSquarePrime
    split with
    | isTrue hex =>
        simp only [Option.some.injEq]
        apply le_antisymm
        · exact Nat.find_min' hex h3
        · exact physicalSquarePrimeAtEdge_three_le (Nat.find_spec hex)
    | isFalse hno => exact (hno ⟨3, h3⟩).elim

@[simp] theorem physicalLeastOddSquarePrime_eq_three_iff_mod (k : ℕ) :
    physicalLeastOddSquarePrime k = some 3 ↔
      k % 9 ∈ physicalNineChannelResidues := by
  rw [physicalLeastOddSquarePrime_eq_three_iff,
    physicalSquarePrimeAtEdge_three_iff]

/-- Exact residue-class form of the `3^2` channel. -/
theorem physicalD9_eq_residueSum (K : ℕ) :
    physicalD9 K =
      ∑ k ∈ Finset.range K with k % 9 ∈ physicalNineChannelResidues,
        physicalDefectEdgeValue k := by
  unfold physicalD9 physicalLeastSquareChannel
  apply Finset.sum_congr
  · ext k
    simp [physicalLeastOddSquarePrime_eq_three_iff_mod]
  · intro k hk
    rfl

/-- The destination degree-one cell observable is the ordinary four-slot cell
sum, since the fourth site is killed by `2^2`. -/
theorem physicalDefectEdgeValue_eq_fourSlotCellSum (k : ℕ) :
    physicalDefectEdgeValue k = fourSlotCellSum (k + 1) := by
  simp [physicalDefectEdgeValue, threeSlotDegreeOneValue_threeSlotState,
    fourSlotCellSum, moebius_four_mul_add_four]
  ring

/-- **Exact `3^2` recurrence.**  One complete nine-edge period of the least
`3^2` channel is exactly the Mertens increment over the corresponding six
four-cells. -/
theorem physicalD9_nine_step_recurrence (L : ℕ) :
    physicalD9 (9 * (L + 1)) - physicalD9 (9 * L) =
      moebiusPositivePrefix (36 * L + 32) -
        moebiusPositivePrefix (36 * L + 8) := by
  rw [physicalD9_eq_residueSum, physicalD9_eq_residueSum]
  simp_rw [physicalDefectEdgeValue_eq_fourSlotCellSum]
  have hleft :
      (∑ k ∈ Finset.range (9 * (L + 1)) with
          k % 9 ∈ physicalNineChannelResidues,
          fourSlotCellSum (k + 1)) -
        (∑ k ∈ Finset.range (9 * L) with
          k % 9 ∈ physicalNineChannelResidues,
          fourSlotCellSum (k + 1)) =
      fourSlotCellSum (9 * L + 2) +
        fourSlotCellSum (9 * L + 3) +
        fourSlotCellSum (9 * L + 4) +
        fourSlotCellSum (9 * L + 5) +
        fourSlotCellSum (9 * L + 6) +
        fourSlotCellSum (9 * L + 7) := by
    have hrange := Finset.sum_range_sub_sum_range
      (f := fun k =>
        if k % 9 ∈ physicalNineChannelResidues then
          fourSlotCellSum (k + 1)
        else 0)
      (show 9 * L ≤ 9 * (L + 1) by omega)
    simpa [Finset.sum_filter, physicalNineChannelResidues,
      Nat.add_mod, Nat.mul_mod] using hrange
  rw [hleft]
  rw [show 36 * L + 32 = 4 * (9 * L + 8) by ring,
    show 36 * L + 8 = 4 * (9 * L + 2) by ring]
  rw [moebiusPositivePrefix_four_mul_eq_fourSlotCellSum,
    moebiusPositivePrefix_four_mul_eq_fourSlotCellSum]
  have hrange := Finset.sum_range_sub_sum_range
    (f := fourSlotCellSum)
    (show 9 * L + 2 ≤ 9 * L + 8 by omega)
  simpa using hrange

end RHLean.Analysis
