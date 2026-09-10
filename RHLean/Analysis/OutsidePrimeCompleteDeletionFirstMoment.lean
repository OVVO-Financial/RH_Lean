import Mathlib.Data.Int.CardIntervalMod
import RHLean.Analysis.OutsidePrimeLeastSquareEndpoint

/-!
# Complete q-owner deletion first-moment bound

This file attacks the arithmetic obstruction left by the selected-prime
`T`-sector contraction directly.  It does not introduce another coordinate
rewrite.

For a fixed least square-prime owner `q`, every deleted physical transition cell
has one of the six active affine forms divisible by `q^2`.  Because `q` is odd,
`4` is invertible modulo `q^2`, so for each active offset there is at most one
cell residue modulo `q^2`.  On a prefix containing a complete number of `q^2`
periods, each offset therefore contributes at most `K / q^2` cells.

The selected degree-one observable has pointwise magnitude at most three.  Thus
the actual signed least-owner deletion first moment satisfies

`|chi^T m_q| <= 18 * K / q^2`

on every complete `q^2` prefix.  The absolute value is taken only after the
signed q-owner channel has been formed.

This is a genuine summable q-owner bound.  It does not yet identify the complete
least-square super-orbit Schur block with the Go `q^2` daughter block; that is
the next intertwining theorem.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Cells below `K` on which one fixed physical active offset is hit by `q^2`. -/
def physicalOffsetSquareHitCells (K q a : ℕ) : Finset ℕ :=
  (Finset.range K).filter fun k => q ^ 2 ∣ 4 * k + a

/-- All cells below `K` on which `q^2` hits at least one of the six physical
transition offsets. -/
def physicalSquareHitCells (K q : ℕ) : Finset ℕ :=
  physicalTransitionActiveOffsets.biUnion fun a =>
    physicalOffsetSquareHitCells K q a

/-- Literal carrier of one least-square deletion channel. -/
def outsidePrimeLeastDeletionChannelCells
    (P O : Finset ℕ) (q : ℕ) : Finset ℕ :=
  (outsidePrimeDeletionCells P O).filter fun k =>
    (physicalLeastOddSquarePrime k).getD 0 = q

/-- Two hits of the same active offset by the square of an odd prime lie in the
same cell residue class modulo `q^2`. -/
theorem physicalOffsetSquareHit_modeq
    {q a k r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hk : q ^ 2 ∣ 4 * k + a) (hr : q ^ 2 ∣ 4 * r + a) :
    k ≡ r [MOD q ^ 2] := by
  have hkm : 4 * k + a ≡ 0 [MOD q ^ 2] :=
    Nat.modEq_zero_iff_dvd.mpr hk
  have hrm : 4 * r + a ≡ 0 [MOD q ^ 2] :=
    Nat.modEq_zero_iff_dvd.mpr hr
  have hsamed : 4 * k + a ≡ 4 * r + a [MOD q ^ 2] :=
    hkm.trans hrm.symm
  have hfour : 4 * k ≡ 4 * r [MOD q ^ 2] :=
    Nat.ModEq.add_right_cancel' a hsamed
  have hcop : Nat.Coprime (q ^ 2) 4 := by
    simpa using
      (Nat.coprime_pow_primes (p := q) (q := 2) 2 2
        hq Nat.prime_two hq2)
  exact Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one hfour

/-- One fixed active offset occupies at most one residue per complete `q^2`
period. -/
theorem physicalOffsetSquareHitCells_card_le_completePeriods
    {K q a : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hcomplete : q ^ 2 ∣ K) :
    (physicalOffsetSquareHitCells K q a).card ≤ K / q ^ 2 := by
  classical
  by_cases hne : (physicalOffsetSquareHitCells K q a).Nonempty
  · rcases hne with ⟨r, hrS⟩
    have hr := (Finset.mem_filter.mp hrS).2
    have hsub :
        physicalOffsetSquareHitCells K q a ⊆
          (Finset.range K).filter (fun k => k ≡ r [MOD q ^ 2]) := by
      intro k hkS
      rcases Finset.mem_filter.mp hkS with ⟨hkK, hkdiv⟩
      exact Finset.mem_filter.mpr
        ⟨hkK, physicalOffsetSquareHit_modeq hq hq2 hkdiv hr⟩
    have hqpow : 0 < q ^ 2 := pow_pos hq.pos 2
    calc
      (physicalOffsetSquareHitCells K q a).card ≤
          ((Finset.range K).filter (fun k => k ≡ r [MOD q ^ 2])).card :=
        Finset.card_le_card hsub
      _ = K.count (fun k => k ≡ r [MOD q ^ 2]) := by
        rw [Nat.count_eq_card_filter_range]
      _ = K / q ^ 2 := by
        rw [Nat.count_modEq_card K hqpow r,
          Nat.mod_eq_zero_of_dvd hcomplete]
        simp
  · have hempty : physicalOffsetSquareHitCells K q a = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

/-- A q-square hit is covered by the union of the six fixed-offset hit sets. -/
theorem mem_physicalSquareHitCells_of_squarePrimeAtEdge
    {K q k : ℕ} (hkK : k < K)
    (hqhit : physicalSquarePrimeAtEdge k q) :
    k ∈ physicalSquareHitCells K q := by
  rcases hqhit with ⟨_hqPrime, a, ha, hdiv⟩
  unfold physicalSquareHitCells
  apply Finset.mem_biUnion.mpr
  refine ⟨a, ha, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr hkK, by simpa [pow_two] using hdiv⟩

/-- Across all six active offsets, a complete `q^2` prefix contains at most
`6 * (K/q^2)` q-square-hit cells. -/
theorem physicalSquareHitCells_card_le_six_completePeriods
    {K q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hcomplete : q ^ 2 ∣ K) :
    (physicalSquareHitCells K q).card ≤ 6 * (K / q ^ 2) := by
  unfold physicalSquareHitCells
  have h_each : ∀ a ∈ physicalTransitionActiveOffsets,
      (physicalOffsetSquareHitCells K q a).card ≤ K / q ^ 2 := by
    intro a _ha
    exact physicalOffsetSquareHitCells_card_le_completePeriods hq hq2 hcomplete
  calc
    (physicalTransitionActiveOffsets.biUnion fun a =>
        physicalOffsetSquareHitCells K q a).card ≤
        physicalTransitionActiveOffsets.card * (K / q ^ 2) := by
      exact Finset.card_biUnion_le_card_mul _ _ _ h_each
    _ = 6 * (K / q ^ 2) := by
      norm_num [physicalTransitionActiveOffsets]

/-- A cell in the q-owned deletion channel is genuinely a q-square-hit cell. -/
theorem outsidePrimeLeastDeletionChannelCells_subset_squareHit
    {P : Finset ℕ} {K q : ℕ} :
    outsidePrimeLeastDeletionChannelCells P (Finset.range K) q ⊆
      physicalSquareHitCells K q := by
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨hkdel, hkowner⟩
  have hkK : k < K :=
    Finset.mem_range.mp (mem_outsidePrimeDeletionCells_iff.mp hkdel).1
  have hne := outsidePrimeDeletion_leastSquare_ne_none hkdel
  cases hleast : physicalLeastOddSquarePrime k with
  | none => exact (hne hleast).elim
  | some p =>
      have hpq : p = q := by
        simpa [hleast] using hkowner
      subst p
      have hhit : physicalSquarePrimeAtEdge k q :=
        physicalLeastOddSquarePrime_some_spec hleast
      exact mem_physicalSquareHitCells_of_squarePrimeAtEdge hkK hhit

/-- The literal q-owned deletion carrier inherits the complete-period
`6 K/q^2` bound. -/
theorem outsidePrimeLeastDeletionChannelCells_card_le_six_completePeriods
    {P : Finset ℕ} {K q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hcomplete : q ^ 2 ∣ K) :
    (outsidePrimeLeastDeletionChannelCells P (Finset.range K) q).card ≤
      6 * (K / q ^ 2) := by
  calc
    (outsidePrimeLeastDeletionChannelCells P (Finset.range K) q).card ≤
        (physicalSquareHitCells K q).card :=
      Finset.card_le_card
        (outsidePrimeLeastDeletionChannelCells_subset_squareHit
          (P := P) (K := K) (q := q))
    _ ≤ 6 * (K / q ^ 2) :=
      physicalSquareHitCells_card_le_six_completePeriods hq hq2 hcomplete

/-- The channel definition is exactly the signed sum on its literal carrier. -/
theorem outsidePrimeLeastDeletionChannel_eq_cells_sum
    (P O : Finset ℕ) (q : ℕ) :
    outsidePrimeLeastDeletionChannel P O q =
      ∑ k ∈ outsidePrimeLeastDeletionChannelCells P O q,
        selectedDegreeOneProjection P k := by
  rfl

/-- **Decisive q-owner first-moment bound.**

For every odd prime owner `q` and every complete `q^2` prefix, the actual signed
deletion first moment has summable `q^{-2}` size:

`|chi^T m_q| <= 18 * K/q^2`.

No norm is taken before the q-owner channel is assembled. -/
theorem abs_outsidePrimeLeastDeletionChannel_le_eighteen_completePeriods
    (P : Finset ℕ) {K q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hcomplete : q ^ 2 ∣ K) :
    |outsidePrimeLeastDeletionChannel P (Finset.range K) q| ≤
      18 * ((K / q ^ 2 : ℕ) : ℝ) := by
  rw [outsidePrimeLeastDeletionChannel_eq_cells_sum]
  let C := outsidePrimeLeastDeletionChannelCells P (Finset.range K) q
  have hcardNat : C.card ≤ 6 * (K / q ^ 2) := by
    simpa [C] using
      outsidePrimeLeastDeletionChannelCells_card_le_six_completePeriods
        (P := P) hq hq2 hcomplete
  have hcardReal : (C.card : ℝ) ≤ 6 * ((K / q ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  calc
    |∑ k ∈ C, selectedDegreeOneProjection P k| ≤
        ∑ k ∈ C, |selectedDegreeOneProjection P k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ C, (3 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact abs_selectedDegreeOneProjection_le_three P k
    _ = 3 * (C.card : ℝ) := by
      simp
      ring
    _ ≤ 3 * (6 * ((K / q ^ 2 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hcardReal (by norm_num)
    _ = 18 * ((K / q ^ 2 : ℕ) : ℝ) := by ring

end RHLean.Analysis
