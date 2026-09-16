import Mathlib
import «research.GLOBAL_RETURNED_CORE_GREATEST_OWNER_CONTINUATION»
import «research.COVARIANCE_RECIPROCAL_OWNER_CONGESTION»

/-!
# Reciprocal-square congestion on the reversed greatest-owner graph

Fix a stripped ordered parent and an owner `p` in the greatest-fresh-prime
filtration.  A positive-lag child can only be one of the same two mixed
insertions as in the least-owner graph:

  ordered(p*a,b), ordered(a,p*b).

Hence fixed-owner multiplicity is at most two.  Under the companion-clipped
condition `X_R < p * parent.2`, only the first candidate can remain physical,
so multiplicity is at most one.

Every greatest-owner child carries exactly `1/p^2` of the reciprocal pair
energy of its stripped parent, by the arbitrary-fresh-prime descent theorem.
Thus the old prime reciprocal-square budget applies verbatim:

  outgoing energy <= 79/81 * parent energy,
  clipped energy  <= 79/162 * parent energy.

This is a contraction only in reciprocal pair currency.  No claim is made here
that the raw AMP weighted Gram has already been converted to that currency.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Positive-lag greatest-owner children with stripped ordered parent fixed. -/
def lowOwnerGreatestOwnerFixedParentChildFiber
    (R : ℕ) (parent : ℕ × ℕ) (p : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p).filter
    (fun mn => mn.1 < mn.2)).filter
    (fun mn => squarefreePairPrimeOrderedParent p mn.1 mn.2 = parent)

/-- Generic mixed child lies in the two canonical candidates. -/
theorem arbitrary_mixed_child_mem_covarianceOwnerChildCandidates
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

/-- A cross pair is obtained from its specified-prime parents by one mixed
p-insertion.  Primality is not needed for this carrier fact; the stored xor is
enough. -/
theorem revealedCrossPair_parentCube
    {R p m n : ℕ}
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    (m = p * um ∧ n = un) ∨ (m = um ∧ n = p * un) := by
  have hxor := (Finset.mem_filter.mp hcross).2.2
  dsimp only
  rcases hxor with h | h
  · left
    unfold squarefreePrimeFamilyParent
    rw [if_pos h.1, if_neg h.2]
    exact ⟨(Nat.mul_div_cancel' h.1).symm, rfl⟩
  · right
    unfold squarefreePrimeFamilyParent
    rw [if_neg h.2, if_pos h.1]
    exact ⟨rfl, (Nat.mul_div_cancel' h.1).symm⟩

/-- Every fixed-parent greatest-owner child lies in the two mixed candidates. -/
theorem lowOwnerGreatestOwnerFixedParentChildFiber_subset_candidates
    (R : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    lowOwnerGreatestOwnerFixedParentChildFiber R parent p ⊆
      covarianceOwnerChildCandidates p parent := by
  intro mn hmn
  rcases mn with ⟨m, n⟩
  rcases Finset.mem_filter.mp hmn with ⟨hltFilter, hparent⟩
  rcases Finset.mem_filter.mp hltFilter with ⟨hcross, hmnlt⟩
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  have hparent' : covarianceOrderedPair um un = parent := by
    simpa [squarefreePairPrimeOrderedParent, covarianceOrderedPair, um, un]
      using hparent
  have hmix := revealedCrossPair_parentCube hcross
  dsimp only at hmix
  exact arbitrary_mixed_child_mem_covarianceOwnerChildCandidates
    hmnlt hparent' hmix

/-- Fixed-parent multiplicity is at most two. -/
theorem lowOwnerGreatestOwnerFixedParentChildFiber_card_le_two
    (R : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    (lowOwnerGreatestOwnerFixedParentChildFiber R parent p).card ≤ 2 := by
  exact (Finset.card_le_card
    (lowOwnerGreatestOwnerFixedParentChildFiber_subset_candidates R parent p)).trans
      (covarianceOwnerChildCandidates_card_le_two p parent)

/-- Fixed-parent greatest-owner multiplicity. -/
def lowOwnerGreatestOwnerFixedParentChildMultiplicity
    (R : ℕ) (parent : ℕ × ℕ) (p : ℕ) : ℕ :=
  (lowOwnerGreatestOwnerFixedParentChildFiber R parent p).card

@[simp] theorem lowOwnerGreatestOwnerFixedParentChildMultiplicity_le_two
    (R : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent p ≤ 2 := by
  exact lowOwnerGreatestOwnerFixedParentChildFiber_card_le_two R parent p

/-- One greatest-owner child carries exactly `1/p^2` of its fixed stripped
parent's reciprocal energy. -/
theorem lowOwnerGreatestOwnerFixedParentChild_energy_eq
    {R p : ℕ} {parent mn : ℕ × ℕ}
    (hp : p.Prime)
    (hmn : mn ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p) :
    postRootCovarianceReciprocalPairEnergy mn =
      (1 / (p : ℝ) ^ 2) *
        postRootCovarianceReciprocalPairEnergy parent := by
  rcases mn with ⟨m, n⟩
  rcases Finset.mem_filter.mp hmn with ⟨hltFilter, hparent⟩
  rcases Finset.mem_filter.mp hltFilter with ⟨hcross, _hmnlt⟩
  have hdesc := descendingGreatestOwner_reciprocal_descent hp hcross
  dsimp only at hdesc
  calc
    postRootCovarianceReciprocalPairEnergy (m, n) =
        (1 / (p : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy
            (squarefreePrimeFamilyParent p m,
              squarefreePrimeFamilyParent p n) := hdesc.2.2
    _ = (1 / (p : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy
            (squarefreePairPrimeOrderedParent p m n) := by
      rw [postRootCovarianceReciprocalPairEnergy_primeOrderedParent]
    _ = (1 / (p : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy parent := by rw [hparent]

/-- Exact fixed-owner reciprocal energy. -/
theorem sum_lowOwnerGreatestOwnerFixedParentChild_energy_eq
    {R p : ℕ} (hp : p.Prime) (parent : ℕ × ℕ) :
    (∑ mn ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
        postRootCovarianceReciprocalPairEnergy mn) =
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent p : ℝ) /
          (p : ℝ) ^ 2 *
        postRootCovarianceReciprocalPairEnergy parent := by
  calc
    (∑ mn ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
        postRootCovarianceReciprocalPairEnergy mn) =
      ∑ _mn ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
        (1 / (p : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy parent := by
        apply Finset.sum_congr rfl
        intro mn hmn
        exact lowOwnerGreatestOwnerFixedParentChild_energy_eq hp hmn
    _ = (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent p : ℝ) /
          (p : ℝ) ^ 2 *
        postRootCovarianceReciprocalPairEnergy parent := by
      unfold lowOwnerGreatestOwnerFixedParentChildMultiplicity
      simp [div_eq_mul_inv]
      ring

/-- Total reciprocal child energy in the greatest-owner graph. -/
def lowOwnerGreatestOwnerReciprocalOutgoingEnergy
    (R : ℕ) (parent : ℕ × ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ mn ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
      postRootCovarianceReciprocalPairEnergy mn

/-- Elementary multiplicity reduction before applying the global prime budget. -/
theorem lowOwnerGreatestOwnerReciprocalOutgoingEnergy_le_twoPrimeBudget
    (R : ℕ) (parent : ℕ × ℕ) :
    lowOwnerGreatestOwnerReciprocalOutgoingEnergy R parent ≤
      2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
        (1 : ℝ) / (p : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy parent := by
  unfold lowOwnerGreatestOwnerReciprocalOutgoingEnergy
  calc
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ mn ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
        postRootCovarianceReciprocalPairEnergy mn) =
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent p : ℝ) /
          (p : ℝ) ^ 2 * postRootCovarianceReciprocalPairEnergy parent := by
          apply Finset.sum_congr rfl
          intro p hpMem
          exact sum_lowOwnerGreatestOwnerFixedParentChild_energy_eq
            (mem_primesUpTo.mp hpMem).1 parent
    _ ≤ ∑ p ∈ primesUpTo (squareRootEndpoint R),
        (2 : ℝ) / (p : ℝ) ^ 2 *
          postRootCovarianceReciprocalPairEnergy parent := by
      apply Finset.sum_le_sum
      intro p _hp
      have hmultNat :=
        lowOwnerGreatestOwnerFixedParentChildMultiplicity_le_two R parent p
      have hmult :
          (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent p : ℝ) ≤ 2 := by
        exact_mod_cast hmultNat
      have hscale :
          (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent p : ℝ) /
              (p : ℝ) ^ 2 ≤
            (2 : ℝ) / (p : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right hmult (by positivity)
      exact mul_le_mul_of_nonneg_right hscale
        (postRootCovarianceReciprocalPairEnergy_nonneg parent)
    _ = 2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
        (1 : ℝ) / (p : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy parent := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring

/-- **79/81 contraction on the reversed owner graph.** -/
theorem lowOwnerGreatestOwnerReciprocalOutgoingEnergy_le_79_over_81
    (R : ℕ) (parent : ℕ × ℕ) :
    lowOwnerGreatestOwnerReciprocalOutgoingEnergy R parent ≤
      (79 / 81 : ℝ) * postRootCovarianceReciprocalPairEnergy parent := by
  have hout := lowOwnerGreatestOwnerReciprocalOutgoingEnergy_le_twoPrimeBudget
    R parent
  have hbudgetQ := primeOwnerReciprocalSquareBudget_le_79_over_162
    (squareRootEndpoint R)
  have hbudgetCast :
      (((∑ p ∈ primesUpTo (squareRootEndpoint R),
          (1 : ℚ) / (p : ℚ) ^ 2 : ℚ)) : ℝ) ≤
        (((79 / 162 : ℚ)) : ℝ) := by
    unfold primeOwnerReciprocalSquareBudget at hbudgetQ
    exact_mod_cast hbudgetQ
  push_cast at hbudgetCast
  norm_num at hbudgetCast ⊢
  have hbudgetR :
      (∑ p ∈ primesUpTo (squareRootEndpoint R),
        (1 : ℝ) / (p : ℝ) ^ 2) ≤ 79 / 162 := by
    simpa [Nat.cast_pow] using hbudgetCast
  have hE := postRootCovarianceReciprocalPairEnergy_nonneg parent
  nlinarith

/-- Under clipping only the candidate multiplying the smaller parent coordinate
can remain physical. -/
theorem lowOwnerGreatestOwnerFixedParentChildFiber_subset_singleton_of_clipped
    {R p : ℕ} {parent : ℕ × ℕ}
    (hclip : squareRootEndpoint R < p * parent.2) :
    lowOwnerGreatestOwnerFixedParentChildFiber R parent p ⊆
      {covarianceOrderedPair (p * parent.1) parent.2} := by
  intro mn hmn
  have hcand :=
    lowOwnerGreatestOwnerFixedParentChildFiber_subset_candidates R parent p hmn
  rcases Finset.mem_filter.mp hmn with ⟨hltFilter, _hparent⟩
  rcases Finset.mem_filter.mp hltFilter with ⟨hcross, _hlt⟩
  have hprod := (Finset.mem_filter.mp hcross).1
  rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
  have hmX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmCar).1).2
  have hnX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnCar).1).2
  have hmaxX : max mn.1 mn.2 ≤ squareRootEndpoint R := max_le hmX hnX
  unfold covarianceOwnerChildCandidates at hcand
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcand
  rcases hcand with hfirst | hsecond
  · exact Finset.mem_singleton.mpr hfirst
  · exfalso
    have hmaxEq :
        max (covarianceOrderedPair parent.1 (p * parent.2)).1
            (covarianceOrderedPair parent.1 (p * parent.2)).2 =
          max parent.1 (p * parent.2) := by
      unfold covarianceOrderedPair
      split <;> simp [Nat.max_comm]
    have hp2X : p * parent.2 ≤ squareRootEndpoint R := by
      calc
        p * parent.2 ≤ max parent.1 (p * parent.2) := Nat.le_max_right _ _
        _ = max (covarianceOrderedPair parent.1 (p * parent.2)).1
            (covarianceOrderedPair parent.1 (p * parent.2)).2 := hmaxEq.symm
        _ = max mn.1 mn.2 := by rw [hsecond]
        _ ≤ squareRootEndpoint R := hmaxX
    exact (Nat.not_lt_of_ge hp2X) hclip

/-- Clipped greatest-owner multiplicity is at most one. -/
theorem lowOwnerGreatestOwnerFixedParentChildFiber_card_le_one_of_clipped
    {R p : ℕ} {parent : ℕ × ℕ}
    (hclip : squareRootEndpoint R < p * parent.2) :
    (lowOwnerGreatestOwnerFixedParentChildFiber R parent p).card ≤ 1 := by
  have hcard := Finset.card_le_card
    (lowOwnerGreatestOwnerFixedParentChildFiber_subset_singleton_of_clipped hclip)
  simpa using hcard

/-- Reciprocal energy on the clipped portion of the greatest-owner graph. -/
def lowOwnerGreatestOwnerClippedOutgoingEnergy
    (R : ℕ) (parent : ℕ × ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    if squareRootEndpoint R < p * parent.2 then
      ∑ mn ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
        postRootCovarianceReciprocalPairEnergy mn
    else 0

/-- **79/162 contraction on the clipped reversed-owner graph.** -/
theorem lowOwnerGreatestOwnerClippedOutgoingEnergy_le_79_over_162
    (R : ℕ) (parent : ℕ × ℕ) :
    lowOwnerGreatestOwnerClippedOutgoingEnergy R parent ≤
      (79 / 162 : ℝ) * postRootCovarianceReciprocalPairEnergy parent := by
  unfold lowOwnerGreatestOwnerClippedOutgoingEnergy
  calc
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      if squareRootEndpoint R < p * parent.2 then
        ∑ mn ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent p,
          postRootCovarianceReciprocalPairEnergy mn
      else 0) ≤
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        (1 / (p : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy parent := by
      apply Finset.sum_le_sum
      intro p hpMem
      by_cases hclip : squareRootEndpoint R < p * parent.2
      · simp only [hclip, if_true]
        rw [sum_lowOwnerGreatestOwnerFixedParentChild_energy_eq
          (mem_primesUpTo.mp hpMem).1]
        have hmultNat :=
          lowOwnerGreatestOwnerFixedParentChildFiber_card_le_one_of_clipped hclip
        have hmult :
            (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent p : ℝ) ≤ 1 := by
          unfold lowOwnerGreatestOwnerFixedParentChildMultiplicity
          exact_mod_cast hmultNat
        have hscale :
            (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent p : ℝ) /
                (p : ℝ) ^ 2 ≤
              (1 : ℝ) / (p : ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_right hmult (by positivity)
        exact mul_le_mul_of_nonneg_right hscale
          (postRootCovarianceReciprocalPairEnergy_nonneg parent)
      · simp only [hclip, if_false]
        positivity
    _ = (∑ p ∈ primesUpTo (squareRootEndpoint R),
        (1 : ℝ) / (p : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy parent := by
      rw [Finset.sum_mul]
    _ ≤ (79 / 162 : ℝ) * postRootCovarianceReciprocalPairEnergy parent := by
      have hbudgetQ := primeOwnerReciprocalSquareBudget_le_79_over_162
        (squareRootEndpoint R)
      have hbudgetCast :
          (((∑ p ∈ primesUpTo (squareRootEndpoint R),
              (1 : ℚ) / (p : ℚ) ^ 2 : ℚ)) : ℝ) ≤
            (((79 / 162 : ℚ)) : ℝ) := by
        unfold primeOwnerReciprocalSquareBudget at hbudgetQ
        exact_mod_cast hbudgetQ
      push_cast at hbudgetCast
      norm_num at hbudgetCast ⊢
      have hbudgetR :
          (∑ p ∈ primesUpTo (squareRootEndpoint R),
            (1 : ℝ) / (p : ℝ) ^ 2) ≤ 79 / 162 := by
        simpa [Nat.cast_pow] using hbudgetCast
      exact mul_le_mul_of_nonneg_right hbudgetR
        (postRootCovarianceReciprocalPairEnergy_nonneg parent)

end RHLean.Proof
