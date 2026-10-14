import Mathlib
import «research.VF_MID_DYADIC_OWNER_PARITY_TWO»

/-!
# Modulus-30 capacity for genuine late square-band owner fibres

The existing strict subdoubling owner theorem identifies each late composite
as p*q, where p and q are genuine primes and q lies in four consecutive
quotient slots. Since q>5, only slots coprime to 30 are admissible.

This is a sharper UNSIGNED occurrence bound than the existing parity-two
inequality. It DOES NOT prove the original historical signed VF payment,
dyadic centered late correction, canonical von-Koch bound, or RH.

Research claim IDs: 20261014-wheel-1 and 20261014-wheel-2.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Four consecutive quotient slots surviving divisibility by 2, 3 and 5.
This is the exact gcd-30 wheel used by the finite census. -/
def vfMidFourSlotWheelThirtyCapacity (t : ℕ) : ℕ :=
  ((Finset.Ioc t (t + 4)).filter (fun m => Nat.Coprime m 30)).card

/-- A prime exceeding five survives the 30-wheel. -/
private theorem prime_gt_five_coprime_thirty
    {q : ℕ} (hq : q.Prime) (hq5 : 5 < q) :
    Nat.Coprime q 30 := by
  apply hq.coprime_iff_not_dvd.mpr
  intro hd
  change q ∣ (2 * 3) * 5 at hd
  rcases hq.dvd_mul.mp hd with h23 | h5
  · rcases hq.dvd_mul.mp h23 with h2 | h3
    · have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      omega
    · have hle : q ≤ 3 := Nat.le_of_dvd (by norm_num) h3
      omega
  · have hle : q ≤ 5 := Nat.le_of_dvd (by norm_num) h5
    omega

/-- Literal quotient-child inclusion in the four-slot 30-wheel. -/
theorem vfMidSquareBandLateOwner_roughChildren_subset_wheelThirty
    {A R p : ℕ} (hA : 5 ≤ A) (_hAR : A ≤ R)
    (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    vfMidSquareBandOwnerRoughChildren R p ⊆
      (Finset.Ioc (R ^ 2 / p) (R ^ 2 / p + 4)).filter
        (fun m => Nat.Coprime m 30) := by
  have hpGtA : A < p :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).2
  intro m hm
  have hmSlots :=
    vfMidSquareBandLateOwner_roughChildren_subset_four_slots
      hRlt hp hm
  have hmPrime : m.Prime :=
    vfMidSquareBandLateOwnerRoughChild_prime_of_subdoubling
      (by omega : 3 ≤ A) hRlt hp hm
  have hmIcc := (Finset.mem_filter.mp hm).1
  have hpm : p ≤ m := (Finset.mem_Icc.mp hmIcc).1
  have hmGt5 : 5 < m := by omega
  exact Finset.mem_filter.mpr
    ⟨hmSlots, prime_gt_five_coprime_thirty hmPrime hmGt5⟩

/-- Exact genuine-owner fibre cap by 30-wheel survivors, not by a
probabilistic residue average. The old two-slot cap follows because every
four consecutive integers include at most two 30-wheel survivors. -/
theorem vfMidSquareBandLateOwner_card_le_wheelThirty
    {A R p : ℕ} (hA : 5 ≤ A) (hAR : A ≤ R)
    (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    (vfMidSquareBandCompositeOwner R p).card ≤
      vfMidFourSlotWheelThirtyCapacity (R ^ 2 / p) := by
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).1
  have hroughEq :
      vfMidSquareBandCompositeOwnerChildren R p =
        vfMidSquareBandOwnerRoughChildren R p :=
    vfMidSquareBandCompositeOwnerChildren_eq_rough
      (by omega : 3 ≤ R) hpOwner
  have hsub :=
    vfMidSquareBandLateOwner_roughChildren_subset_wheelThirty
      hA hAR hRlt hp
  calc
    (vfMidSquareBandCompositeOwner R p).card =
        (vfMidSquareBandCompositeOwnerChildren R p).card := by
          symm
          exact vfMidSquareBandCompositeOwnerChildren_card R p
    _ = (vfMidSquareBandOwnerRoughChildren R p).card := by
          exact congrArg Finset.card hroughEq
    _ ≤ vfMidFourSlotWheelThirtyCapacity (R ^ 2 / p) := by
          exact Finset.card_le_card hsub

/-- The adaptive 30-wheel capacity, summed over distinct least-prime
owner occurrences and over an entire strict subdoubling run. -/
def vfMidDyadicWheelThirtyLateBudget (A B : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico A B,
    ∑ p ∈ vfMidSquareBandLateOwnerPrimes A r,
      (vfMidFourSlotWheelThirtyCapacity (r ^ 2 / p) : ℝ)

/-- Every genuine late composite occurs in exactly one owner fibre, so
the wheel bound can be summed without duplicating physical occurrences. -/
theorem vfMidDyadicLateRemoval_start_le_wheelThirtyBudget
    {A B : ℕ} (hA : 5 ≤ A) (hAB : A ≤ B)
    (hBA : B ≤ 2 * A) :
    vfMidDyadicLateRemoval A A B ≤
      vfMidDyadicWheelThirtyLateBudget A B := by
  rw [vfMidDyadicLateRemoval_eq_ownerCensus A A B
    (by omega) le_rfl hAB]
  unfold vfMidDyadicOwnerLateRemoval
    vfMidDyadicWheelThirtyLateBudget
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro p hp
  have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
  have hr2A : r < 2 * A :=
    (Finset.mem_Ico.mp hr).2.trans_le hBA
  exact_mod_cast
    (vfMidSquareBandLateOwner_card_le_wheelThirty
      hA hAr hr2A hp)

/-- Correctly directed lower bound for actual prime supply. This counts
positive unit-weight removals; it is not historical signed NNS payment. -/
theorem vfMidDyadicPrimeSupply_ge_startPrefix_sub_wheelThirtyBudget
    {A B : ℕ} (hA : 5 ≤ A) (hAB : A ≤ B)
    (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSupply A A B -
      vfMidDyadicWheelThirtyLateBudget A B ≤
        vfMidDyadicPrimeSupply A B := by
  have hlate :=
    vfMidDyadicLateRemoval_start_le_wheelThirtyBudget
      hA hAB hBA
  unfold vfMidDyadicLateRemoval at hlate
  linarith

#print axioms vfMidSquareBandLateOwner_roughChildren_subset_wheelThirty
#print axioms vfMidSquareBandLateOwner_card_le_wheelThirty
#print axioms vfMidDyadicLateRemoval_start_le_wheelThirtyBudget
#print axioms vfMidDyadicPrimeSupply_ge_startPrefix_sub_wheelThirtyBudget

end RHLean.Analysis
