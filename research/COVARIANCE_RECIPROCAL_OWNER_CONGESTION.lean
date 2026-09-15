import Mathlib
import RHLean.Proof.EndpointCubeAnalyticClosure
import RHLean.Proof.SquareRootLowPrimeSharpFrameBudget

/-!
# Strict reciprocal-square congestion for the covariance owner map

Raw child multiplicity in the post-root covariance owner descent is not
uniformly bounded by one. The correct quantity suggested by the critical
Perron/q² coordinate is the owner-weighted congestion

  sum_p childMultiplicity(parent,p) / p².

This file proves two elementary facts on the literal covariance owner map.

1. For a fixed ordered parent and fixed owner prime `p`, there are at most two
   recursive children: insert `p` into the first parent coordinate or into the
   second, then re-orient as a positive-lag pair.

2. The reciprocal-square mass of all prime owners has uniform slack below the
   coarse `1/2` telescope. The old odd-integer envelope counts the composite
   site `9`; deleting that impossible prime site yields

     sum_{p prime <= N} 1/p² <= 1/2 - 1/81 = 79/162.

Therefore the exact fixed-parent reciprocal-square congestion is at most

  2 * 79/162 = 79/81 < 1.

This is a strict contraction coefficient only after the natural q²/Perron
weighting. It does not bound raw multiplicity and is not inverted below.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Canonical positive-lag orientation of an unordered natural pair. -/
def covarianceOrderedPair (a b : ℕ) : ℕ × ℕ :=
  if a < b then (a, b) else (b, a)

@[simp] theorem covarianceOrderedPair_eq_of_lt
    {a b : ℕ} (hab : a < b) :
    covarianceOrderedPair a b = (a, b) := by
  simp [covarianceOrderedPair, hab]

theorem covarianceOrderedPair_comm (a b : ℕ) :
    covarianceOrderedPair a b = covarianceOrderedPair b a := by
  unfold covarianceOrderedPair
  by_cases hab : a < b
  · have hba : ¬ b < a := by omega
    simp [hab, hba]
  · by_cases hba : b < a
    · simp [hab, hba]
    · have habEq : a = b := by omega
      simp [habEq]

/-- The only two possible ordered children obtained from a fixed ordered parent
and one fresh owner `p`. -/
def covarianceOwnerChildCandidates
    (p : ℕ) (parent : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  {covarianceOrderedPair (p * parent.1) parent.2,
    covarianceOrderedPair parent.1 (p * parent.2)}

private theorem covariance_mixed_child_mem_candidates
    {p um un m n : ℕ} {parent : ℕ × ℕ}
    (hmn : m < n)
    (hparent : covarianceOrderedPair um un = parent)
    (hmix : (m = p * um ∧ n = un) ∨ (m = um ∧ n = p * un)) :
    (m, n) ∈ covarianceOwnerChildCandidates p parent := by
  rw [← hparent]
  rcases hmix with hmix | hmix
  · rcases hmix with ⟨hm, hn⟩
    have hmn' : p * um < un := by simpa [hm, hn] using hmn
    rw [hm, hn]
    by_cases hum : um < un
    · simp [covarianceOwnerChildCandidates, covarianceOrderedPair, hum, hmn']
    · have hnot : ¬ un < p * um := by omega
      simp [covarianceOwnerChildCandidates, covarianceOrderedPair, hum, hnot]
  · rcases hmix with ⟨hm, hn⟩
    have hmn' : um < p * un := by simpa [hm, hn] using hmn
    rw [hm, hn]
    by_cases hum : um < un
    · simp [covarianceOwnerChildCandidates, covarianceOrderedPair, hum, hmn']
    · have hnot : ¬ p * un < um := by omega
      simp [covarianceOwnerChildCandidates, covarianceOrderedPair, hum, hnot]

/-- Nonzero recursive children with both chronological owner and stripped
ordered parent fixed. -/
def postRootCovarianceFixedOwnerChildFiber
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) : Finset (ℕ × ℕ) :=
  ((((postRootCovarianceRemainderRecursivePairCarrier W).filter
      (fun mn => realMoebiusStep mn.1 * realMoebiusStep mn.2 ≠ 0)).filter
    (fun mn => squarefreePairFreshPrimeOwner mn.1 mn.2 = p)).filter
    (fun mn => squarefreePairFreshPrimeOrderedParent mn.1 mn.2 = parent))

/-- Every fixed-owner child lies in the two literal mixed-corner candidates. -/
theorem postRootCovarianceFixedOwnerChildFiber_subset_candidates
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    postRootCovarianceFixedOwnerChildFiber W parent p ⊆
      covarianceOwnerChildCandidates p parent := by
  intro mn hmn
  rcases mn with ⟨m, n⟩
  rcases Finset.mem_filter.mp hmn with ⟨hownerFilter, hparent⟩
  rcases Finset.mem_filter.mp hownerFilter with ⟨hweightFilter, howner⟩
  rcases Finset.mem_filter.mp hweightFilter with ⟨hrec, hweight⟩
  rcases Finset.mem_filter.mp hrec with ⟨hremainder, _hparentNeProp⟩
  have hphysical :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hremainder).1
  rcases mem_mertensPositivePhysicalPairCarrier.mp hphysical with
    ⟨hm1, _hmW, hn1, _hnW, hmnlt⟩
  have hmstep : realMoebiusStep m ≠ 0 := by
    intro hmzero
    exact hweight (by rw [hmzero, zero_mul])
  have hnstep : realMoebiusStep n ≠ 0 := by
    intro hnzero
    exact hweight (by rw [hnzero, mul_zero])
  have hmsq : Squarefree m := squarefree_of_realMoebiusStep_ne_zero hmstep
  have hnsq : Squarefree n := squarefree_of_realMoebiusStep_ne_zero hnstep
  have hcube := squarefreePairFreshPrimeOwner_parentCube
    hmsq hnsq (ne_of_lt hmnlt) (by omega) (by omega)
  dsimp only at hcube
  have hparent' :
      covarianceOrderedPair
          (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) m)
          (squarefreePrimeFamilyParent (squarefreePairFreshPrimeOwner m n) n) =
        parent := by
    unfold squarefreePairFreshPrimeOrderedParent at hparent
    simpa [covarianceOrderedPair] using hparent
  have hcand := covariance_mixed_child_mem_candidates
    hmnlt hparent' hcube.2.2
  rw [howner] at hcand
  exact hcand

/-- A two-element insertion/singleton finset has cardinality at most two. -/
theorem covarianceOwnerChildCandidates_card_le_two
    (p : ℕ) (parent : ℕ × ℕ) :
    (covarianceOwnerChildCandidates p parent).card ≤ 2 := by
  unfold covarianceOwnerChildCandidates
  have h := Finset.card_insert_le
    (covarianceOrderedPair (p * parent.1) parent.2)
    ({covarianceOrderedPair parent.1 (p * parent.2)} : Finset (ℕ × ℕ))
  simpa using h

/-- At most two children for one fixed parent/owner pair. -/
theorem postRootCovarianceFixedOwnerChildFiber_card_le_two
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    (postRootCovarianceFixedOwnerChildFiber W parent p).card ≤ 2 := by
  exact (Finset.card_le_card
    (postRootCovarianceFixedOwnerChildFiber_subset_candidates W parent p)).trans
      (covarianceOwnerChildCandidates_card_le_two p parent)

/-- Fixed-owner child multiplicity. -/
def postRootCovarianceFixedOwnerChildMultiplicity
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) : ℕ :=
  (postRootCovarianceFixedOwnerChildFiber W parent p).card

@[simp] theorem postRootCovarianceFixedOwnerChildMultiplicity_le_two
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    postRootCovarianceFixedOwnerChildMultiplicity W parent p ≤ 2 :=
  postRootCovarianceFixedOwnerChildFiber_card_le_two W parent p

/-! ## Sharpen the global prime reciprocal-square budget -/

private def covarianceOddIntegerEnvelope (N : ℕ) : Finset ℕ :=
  (Finset.range N).image (fun k : ℕ => 2 * k + 3)

private theorem covarianceOddPrimes_subset_envelope_erase_nine (N : ℕ) :
    (primesUpTo N).erase 2 ⊆ (covarianceOddIntegerEnvelope N).erase 9 := by
  intro q hq
  have hqData := mem_primesUpTo.mp (Finset.mem_erase.mp hq).2
  have hqPrime := hqData.1
  have hqN := hqData.2
  have hq2 := hqPrime.two_le
  have hqNe2 := (Finset.mem_erase.mp hq).1
  have hqNe9 : q ≠ 9 := by
    intro hq9
    subst q
    norm_num at hqPrime
  obtain ⟨k, hk⟩ := hqPrime.odd_of_ne_two hqNe2
  have hk1 : 1 ≤ k := by omega
  apply Finset.mem_erase.mpr
  refine ⟨hqNe9, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
  omega

private theorem nine_mem_covarianceOddIntegerEnvelope
    {N : ℕ} (hN : 9 ≤ N) :
    9 ∈ covarianceOddIntegerEnvelope N := by
  unfold covarianceOddIntegerEnvelope
  apply Finset.mem_image.mpr
  refine ⟨3, Finset.mem_range.mpr (by omega), by norm_num⟩

private theorem covarianceOddIntegerEnvelope_reciprocalSquareSum_le_quarter
    (N : ℕ) :
    (∑ q ∈ covarianceOddIntegerEnvelope N,
      (1 : ℚ) / (q : ℚ) ^ 2) ≤ 1 / 4 := by
  unfold covarianceOddIntegerEnvelope
  rw [Finset.sum_image]
  · have h := sum_oddReciprocalSquares_le_quarter_sub N
    have htail : (0 : ℚ) ≤ 1 / (4 * ((N : ℚ) + 1)) := by positivity
    linarith
  · intro a _ha b _hb hab
    have hmul : 2 * a = 2 * b := Nat.add_right_cancel hab
    omega

/-- The odd-prime envelope has uniform slack because the odd integer `9` is
never prime but is always present once `N >= 9`. -/
theorem oddPrimeOwnerReciprocalSquareBudget_le_quarter_sub_one_over_81
    {N : ℕ} (hN : 9 ≤ N) :
    (∑ q ∈ (primesUpTo N).erase 2,
      (1 : ℚ) / (q : ℚ) ^ 2) ≤ 1 / 4 - 1 / 81 := by
  have hsubset := covarianceOddPrimes_subset_envelope_erase_nine N
  have hsum :
      (∑ q ∈ (primesUpTo N).erase 2,
        (1 : ℚ) / (q : ℚ) ^ 2) ≤
      ∑ q ∈ (covarianceOddIntegerEnvelope N).erase 9,
        (1 : ℚ) / (q : ℚ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro q _hqNew _hqOld
    positivity
  have h9 := nine_mem_covarianceOddIntegerEnvelope hN
  have herase := Finset.sum_erase_add
    (s := covarianceOddIntegerEnvelope N)
    (f := fun q => (1 : ℚ) / (q : ℚ) ^ 2) h9
  have herase' :
      (∑ q ∈ (covarianceOddIntegerEnvelope N).erase 9,
        (1 : ℚ) / (q : ℚ) ^ 2) + 1 / 81 =
      ∑ q ∈ covarianceOddIntegerEnvelope N,
        (1 : ℚ) / (q : ℚ) ^ 2 := by
    norm_num at herase
    simpa [one_div] using herase
  have hall := covarianceOddIntegerEnvelope_reciprocalSquareSum_le_quarter N
  rw [← herase'] at hall
  linarith

private theorem small_prime_reciprocalSquareBudget_le_79_over_162
    {N : ℕ} (hN : N < 9) :
    primeOwnerReciprocalSquareBudget N ≤ 79 / 162 := by
  have hsubset : primesUpTo N ⊆ ({2, 3, 5, 7} : Finset ℕ) := by
    intro q hq
    have hdata := mem_primesUpTo.mp hq
    have hp := hdata.1
    have hqN := hdata.2
    have hqLt : q < 9 := lt_of_le_of_lt hqN hN
    have hq2 := hp.two_le
    interval_cases q <;> norm_num at hp
    all_goals norm_num
  unfold primeOwnerReciprocalSquareBudget
  calc
    (∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2) ≤
        ∑ q ∈ ({2, 3, 5, 7} : Finset ℕ),
          (1 : ℚ) / (q : ℚ) ^ 2 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
            intro q _hqNew _hqOld
            positivity
    _ ≤ 79 / 162 := by norm_num

/-- Uniform strict prime reciprocal-square budget. -/
theorem primeOwnerReciprocalSquareBudget_le_79_over_162 (N : ℕ) :
    primeOwnerReciprocalSquareBudget N ≤ 79 / 162 := by
  by_cases hN : N < 9
  · exact small_prime_reciprocalSquareBudget_le_79_over_162 hN
  · have hN9 : 9 ≤ N := by omega
    have hodd :=
      oddPrimeOwnerReciprocalSquareBudget_le_quarter_sub_one_over_81 hN9
    have htwo : 2 ∈ primesUpTo N :=
      mem_primesUpTo.mpr ⟨Nat.prime_two, by omega⟩
    have hsplit := Finset.sum_erase_add
      (s := primesUpTo N)
      (f := fun q => (1 : ℚ) / (q : ℚ) ^ 2) htwo
    have hsplit' :
        (∑ q ∈ (primesUpTo N).erase 2,
          (1 : ℚ) / (q : ℚ) ^ 2) + 1 / 4 =
        ∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2 := by
      norm_num at hsplit
      simpa [one_div] using hsplit
    unfold primeOwnerReciprocalSquareBudget
    calc
      (∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2) =
          (∑ q ∈ (primesUpTo N).erase 2,
            (1 : ℚ) / (q : ℚ) ^ 2) + 1 / 4 := hsplit'.symm
      _ ≤ (1 / 4 - 1 / 81) + 1 / 4 := add_le_add_right hodd _
      _ = 79 / 162 := by norm_num

/-! ## Strict fixed-parent reciprocal-square congestion -/

/-- Reciprocal-square owner congestion seen by one ordered covariance parent. -/
def postRootCovarianceReciprocalOwnerCongestion
    (W : ℕ) (parent : ℕ × ℕ) : ℚ :=
  ∑ p ∈ primesUpTo W,
    (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℚ) /
      (p : ℚ) ^ 2

/-- Fixed-parent congestion is bounded by twice the prime reciprocal-square
budget because each owner has at most two mixed-corner children. -/
theorem postRootCovarianceReciprocalOwnerCongestion_le_two_mul_budget
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootCovarianceReciprocalOwnerCongestion W parent ≤
      2 * primeOwnerReciprocalSquareBudget W := by
  unfold postRootCovarianceReciprocalOwnerCongestion primeOwnerReciprocalSquareBudget
  calc
    (∑ p ∈ primesUpTo W,
        (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℚ) /
          (p : ℚ) ^ 2) ≤
      ∑ p ∈ primesUpTo W, 2 * ((1 : ℚ) / (p : ℚ) ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpPrime := (mem_primesUpTo.mp hp).1
        have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hpPrime.pos
        have hpSq : (0 : ℚ) < (p : ℚ) ^ 2 := sq_pos_of_pos hpQ
        have hmultNat :=
          postRootCovarianceFixedOwnerChildMultiplicity_le_two W parent p
        have hmult :
            (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℚ) ≤ 2 := by
          exact_mod_cast hmultNat
        calc
          (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℚ) /
              (p : ℚ) ^ 2 ≤ 2 / (p : ℚ) ^ 2 :=
            (div_le_div_iff_of_pos_right hpSq).2 hmult
          _ = 2 * ((1 : ℚ) / (p : ℚ) ^ 2) := by ring
    _ = 2 * ∑ p ∈ primesUpTo W, (1 : ℚ) / (p : ℚ) ^ 2 := by
      rw [Finset.mul_sum]

/-- Strict reciprocal-square congestion contraction. -/
theorem postRootCovarianceReciprocalOwnerCongestion_le_79_over_81
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootCovarianceReciprocalOwnerCongestion W parent ≤ 79 / 81 := by
  have hcong :=
    postRootCovarianceReciprocalOwnerCongestion_le_two_mul_budget W parent
  have hbudget := primeOwnerReciprocalSquareBudget_le_79_over_162 W
  nlinarith

/-- The contraction coefficient has genuine uniform slack below one. -/
theorem postRootCovarianceReciprocalOwnerCongestion_lt_one
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootCovarianceReciprocalOwnerCongestion W parent < 1 := by
  have h := postRootCovarianceReciprocalOwnerCongestion_le_79_over_81 W parent
  norm_num at h ⊢
  linarith

end RHLean.Proof