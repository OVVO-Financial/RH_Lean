import Mathlib
import «research.COVARIANCE_RECIPROCAL_OWNER_CONGESTION»

/-!
# Reciprocal covariance pair amplitude contracts on the literal owner graph

PR #714 proves that, for one stripped covariance parent, the owner-weighted
child congestion satisfies

  sum_p multiplicity(parent,p) / p^2 <= 79/81.

Here the reciprocal-square weight is derived from an actual amplitude rather
than inserted externally.  Put

  A(m,n) = mu(m) mu(n) / (m n).

The first-separation owner theorem says that a recursive child differs from its
stripped parent by inserting its fresh owner `p` in exactly one coordinate and
reversing the Mobius pair sign.  Therefore

  A(child) = -(1/p) A(parent)

and hence

  E(child) = (1/p^2) E(parent).

Summing the literal fixed-owner fibres then turns #714's `79/81` congestion
bound into a genuine strict energy contraction on this reciprocal pair
amplitude.  No statistical independence, norm inversion, or RH estimate is
used.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Reciprocal amplitude of one ordered/unordered covariance pair. -/
def postRootCovarianceReciprocalPairAmplitude (mn : ℕ × ℕ) : ℝ :=
  (realMoebiusStep mn.1 * realMoebiusStep mn.2) /
    ((mn.1 : ℝ) * (mn.2 : ℝ))

/-- Positive energy carried by the reciprocal pair amplitude. -/
def postRootCovarianceReciprocalPairEnergy (mn : ℕ × ℕ) : ℝ :=
  postRootCovarianceReciprocalPairAmplitude mn ^ 2

/-- Reordering the two coordinates changes neither reciprocal amplitude nor
energy. -/
theorem postRootCovarianceReciprocalPairAmplitude_ordered
    (a b : ℕ) :
    postRootCovarianceReciprocalPairAmplitude (covarianceOrderedPair a b) =
      postRootCovarianceReciprocalPairAmplitude (a, b) := by
  unfold covarianceOrderedPair postRootCovarianceReciprocalPairAmplitude
  by_cases hab : a < b
  · simp [hab]
  · simp [hab, mul_comm]

@[simp] theorem postRootCovarianceReciprocalPairEnergy_nonneg
    (mn : ℕ × ℕ) :
    0 ≤ postRootCovarianceReciprocalPairEnergy mn := by
  unfold postRootCovarianceReciprocalPairEnergy
  positivity

/-- **Exact reciprocal amplitude descent.**  Stripping the first separating
prime from a nonzero squarefree pair removes one factor `p` from the physical
product and flips the Mobius pair sign. -/
theorem postRootCovarianceReciprocalPairAmplitude_owner_descent
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n)
    (hmn : m ≠ n) (hmpos : 0 < m) (hnpos : 0 < n) :
    let p := squarefreePairFreshPrimeOwner m n
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    postRootCovarianceReciprocalPairAmplitude (m, n) =
      -(1 / (p : ℝ)) *
        postRootCovarianceReciprocalPairAmplitude
          (covarianceOrderedPair um un) := by
  dsimp
  let p := squarefreePairFreshPrimeOwner m n
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  have hp : p.Prime := squarefreePairFreshPrimeOwner_prime hm hn hmn
  have hcube := squarefreePairFreshPrimeOwner_parentCube
    hm hn hmn hmpos hnpos
  change (¬ p ∣ um) ∧ (¬ p ∣ un) ∧
      ((m = p * um ∧ n = un) ∨ (m = um ∧ n = p * un)) at hcube
  have hum0 : (um : ℝ) ≠ 0 := by
    exact_mod_cast (by
      intro hum
      apply hcube.1
      subst um
      exact dvd_zero p)
  have hun0 : (un : ℝ) ≠ 0 := by
    exact_mod_cast (by
      intro hun
      apply hcube.2.1
      subst un
      exact dvd_zero p)
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hweight :=
    squarefreePairFreshPrimeOwner_pairWeight_eq_neg_parentPairWeight
      hm hn hmn hmpos hnpos
  change realMoebiusStep m * realMoebiusStep n =
      -(realMoebiusStep um * realMoebiusStep un) at hweight
  have hprod : (m : ℝ) * (n : ℝ) =
      (p : ℝ) * ((um : ℝ) * (un : ℝ)) := by
    rcases hcube.2.2 with h | h
    · rw [h.1, h.2]
      push_cast
      ring
    · rw [h.1, h.2]
      push_cast
      ring
  rw [postRootCovarianceReciprocalPairAmplitude_ordered]
  unfold postRootCovarianceReciprocalPairAmplitude
  simp only [Prod.fst, Prod.snd]
  rw [hweight, hprod]
  field_simp [hp0, hum0, hun0]
  ring

/-- Squaring the preceding amplitude law gives the literal reciprocal-square
owner factor. -/
theorem postRootCovarianceReciprocalPairEnergy_owner_descent
    {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n)
    (hmn : m ≠ n) (hmpos : 0 < m) (hnpos : 0 < n) :
    let p := squarefreePairFreshPrimeOwner m n
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    postRootCovarianceReciprocalPairEnergy (m, n) =
      (1 / (p : ℝ) ^ 2) *
        postRootCovarianceReciprocalPairEnergy
          (covarianceOrderedPair um un) := by
  dsimp
  unfold postRootCovarianceReciprocalPairEnergy
  rw [postRootCovarianceReciprocalPairAmplitude_owner_descent
    hm hn hmn hmpos hnpos]
  ring

/-- Every actual child in one fixed owner/parent fibre carries exactly the same
`1/p^2` fraction of its ordered parent's reciprocal energy. -/
theorem postRootCovarianceFixedOwnerChild_energy_eq
    {W p : ℕ} {parent mn : ℕ × ℕ}
    (hmnMem : mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p) :
    postRootCovarianceReciprocalPairEnergy mn =
      (1 / (p : ℝ) ^ 2) * postRootCovarianceReciprocalPairEnergy parent := by
  rcases mn with ⟨m, n⟩
  rcases Finset.mem_filter.mp hmnMem with ⟨hownerFilter, hparent⟩
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
  have henergy := postRootCovarianceReciprocalPairEnergy_owner_descent
    hmsq hnsq (ne_of_lt hmnlt) (by omega) (by omega)
  dsimp only at henergy
  rw [howner] at henergy
  have hparent' :
      covarianceOrderedPair
          (squarefreePrimeFamilyParent p m)
          (squarefreePrimeFamilyParent p n) = parent := by
    unfold squarefreePairFreshPrimeOrderedParent at hparent
    simpa [howner] using hparent
  rw [hparent'] at henergy
  exact henergy

/-- Exact energy of one fixed owner fibre: multiplicity times the reciprocal
square of the owner, times the parent energy. -/
theorem sum_postRootCovarianceFixedOwnerChild_energy_eq
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        postRootCovarianceReciprocalPairEnergy mn) =
      (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) /
          (p : ℝ) ^ 2 *
        postRootCovarianceReciprocalPairEnergy parent := by
  calc
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        postRootCovarianceReciprocalPairEnergy mn) =
      ∑ _mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        (1 / (p : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy parent := by
        apply Finset.sum_congr rfl
        intro mn hmn
        exact postRootCovarianceFixedOwnerChild_energy_eq hmn
    _ = (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) /
          (p : ℝ) ^ 2 *
        postRootCovarianceReciprocalPairEnergy parent := by
      unfold postRootCovarianceFixedOwnerChildMultiplicity
      simp [div_eq_mul_inv]
      ring

/-- Total reciprocal child energy leaving one physical covariance parent. -/
def postRootCovarianceReciprocalOutgoingEnergy
    (W : ℕ) (parent : ℕ × ℕ) : ℝ :=
  ∑ p ∈ primesUpTo W,
    ∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
      postRootCovarianceReciprocalPairEnergy mn

/-- **Literal 79/81 reciprocal-amplitude energy contraction.**  The abstract
congestion coefficient of #714 is exactly the outgoing energy ratio of the
physical reciprocal pair amplitude. -/
theorem postRootCovarianceReciprocalOutgoingEnergy_le_79_over_81
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootCovarianceReciprocalOutgoingEnergy W parent ≤
      (79 / 81 : ℝ) * postRootCovarianceReciprocalPairEnergy parent := by
  unfold postRootCovarianceReciprocalOutgoingEnergy
  rw [show
    (∑ p ∈ primesUpTo W,
      ∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        postRootCovarianceReciprocalPairEnergy mn) =
      ∑ p ∈ primesUpTo W,
        (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) /
          (p : ℝ) ^ 2 * postRootCovarianceReciprocalPairEnergy parent by
      apply Finset.sum_congr rfl
      intro p _hp
      exact sum_postRootCovarianceFixedOwnerChild_energy_eq W parent p]
  rw [← Finset.sum_mul]
  have hcongQ :=
    postRootCovarianceReciprocalOwnerCongestion_le_79_over_81 W parent
  have hcongR :
      (∑ p ∈ primesUpTo W,
        (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) /
          (p : ℝ) ^ 2) ≤ 79 / 81 := by
    unfold postRootCovarianceReciprocalOwnerCongestion at hcongQ
    exact_mod_cast hcongQ
  exact mul_le_mul_of_nonneg_right hcongR
    (postRootCovarianceReciprocalPairEnergy_nonneg parent)

end RHLean.Proof
