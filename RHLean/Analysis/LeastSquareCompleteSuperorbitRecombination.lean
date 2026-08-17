import Mathlib
import RHLean.Analysis.OutsidePrimeLeastSquareEndpoint
import RHLean.Analysis.SelectedCRTBaseline

/-!
# Complete least-owner super-orbit recombination

The least-square endpoint layer assigns each outside-prime deletion to its least
square-prime owner `q`.  On a complete owner-`q` super-orbit, the condition that
no smaller square prime has already deleted the cell is itself finite CRT data.
It can therefore be absorbed into the field on the stage modulus containing the
selected primes and every prime below `q`.

Since `q^2` is coprime to that stage modulus, stepping by `q^2` still permutes
the complete stage orbit exactly.  Thus every fixed owner-`q` deletion residue
samples the *earlier-prime-conditioned* selected degree-one field exactly once.
No new independence or analytic estimate is used.

The residual stage baseline is deliberately kept explicit.  The preceding
`SelectedCRTBaseline` module shows that the raw selected degree-one baseline is
not zero in general, so a zero-baseline theorem would be false.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Every element of the least-owner stage prime set is prime when the selected
set itself consists of primes. -/
theorem outsidePrimeLeastStagePrimes_prime
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (q : ℕ) :
    ∀ r ∈ outsidePrimeLeastStagePrimes P q, r.Prime := by
  intro r hr
  rcases Finset.mem_union.mp hr with hrP | hrEarlier
  · exact hP r hrP
  · exact (Finset.mem_filter.mp hrEarlier).2

/-- The owner prime does not occur among the strictly earlier primes. -/
theorem outsidePrime_owner_not_mem_earlierPrimes (q : ℕ) :
    q ∉ outsidePrimeEarlierPrimes q := by
  intro hq
  have hmemRange : q ∈ Finset.range q := (Finset.mem_filter.mp hq).1
  have hlt : q < q := Finset.mem_range.mp hmemRange
  omega

/-- An outside owner prime is absent from the complete least-owner stage set. -/
theorem outsidePrime_owner_not_mem_leastStage
    (P : Finset ℕ) {q : ℕ} (hqP : q ∉ P) :
    q ∉ outsidePrimeLeastStagePrimes P q := by
  intro hqStage
  rcases Finset.mem_union.mp hqStage with hqInP | hqEarlier
  · exact hqP hqInP
  · exact outsidePrime_owner_not_mem_earlierPrimes q hqEarlier

/-- For any finite set of genuine primes, the totalized CRT period is exactly
the product of their square moduli. -/
theorem finitePrimeCRTPeriod_eq_primeSquareProduct_of_primeSet
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    finitePrimeCRTPeriod S = ∏ p ∈ S, p ^ 2 := by
  unfold finitePrimeCRTPeriod
  apply max_eq_right
  have hpos : 0 < ∏ p ∈ S, p ^ 2 := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (hS p hp).pos 2
  omega

/-- A least owner square is coprime to the complete stage modulus containing
all selected primes and all smaller prime-square channels. -/
theorem outsidePrime_ownerSquare_coprime_leastStagePeriod
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) :
    (q ^ 2).Coprime
      (finitePrimeCRTPeriod (outsidePrimeLeastStagePrimes P q)) := by
  let S := outsidePrimeLeastStagePrimes P q
  have hS : ∀ p ∈ S, p.Prime := by
    simpa [S] using outsidePrimeLeastStagePrimes_prime P hP q
  rw [finitePrimeCRTPeriod_eq_primeSquareProduct_of_primeSet hS]
  apply Nat.Coprime.prod_right
  intro p hpS
  have hpPrime : p.Prime := hS p hpS
  have hne : q ≠ p := by
    intro hqp
    subst p
    exact outsidePrime_owner_not_mem_leastStage P hqP hpS
  exact Nat.coprime_pow_primes 2 2 hq hpPrime hne

/-- The stage modulus before processing owner `q`. -/
def outsidePrimeLeastStagePeriod (P : Finset ℕ) (q : ℕ) : ℕ :=
  finitePrimeCRTPeriod (outsidePrimeLeastStagePrimes P q)

instance outsidePrimeLeastStagePeriod_neZero (P : Finset ℕ) (q : ℕ) :
    NeZero (outsidePrimeLeastStagePeriod P q) :=
  ⟨Nat.ne_of_gt (by
    unfold outsidePrimeLeastStagePeriod
    exact finitePrimeCRTPeriod_pos _)⟩

/-- Exact selected degree-one field after imposing selected-prime zero-freeness
and exclusion of every square-prime channel strictly below the owner `q`.
This is the finite CRT field relevant to least-owner recombination. -/
def leastOwnerStageDegreeOneField
    (P : Finset ℕ) (q : ℕ)
    (r : ZMod (outsidePrimeLeastStagePeriod P q)) : ℝ :=
  if outsidePrimeSelectedZeroFreeAt
      (outsidePrimeLeastStagePrimes P q) r.val then
    selectedDegreeOneProjection P r.val
  else
    0

/-- Raw complete-stage baseline seen by an owner-`q` channel after every smaller
square-prime deletion has been excluded. -/
def leastOwnerStageBaseline (P : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ r : ZMod (outsidePrimeLeastStagePeriod P q),
    leastOwnerStageDegreeOneField P q r

/-- **Exact conditioned affine CRT sampling.**  For a genuine outside owner
prime `q`, every fixed residue modulo `q^2` samples the entire earlier-prime-
conditioned selected degree-one stage field exactly once. -/
theorem leastOwner_singleDeletionResidue_preserves_stageBaseline
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} (hq : q.Prime) (hqP : q ∉ P)
    (a : ZMod (q ^ 2)) :
    (∑ t : ZMod (outsidePrimeLeastStagePeriod P q),
        leastOwnerStageDegreeOneField P q
          ((a.val : ZMod (outsidePrimeLeastStagePeriod P q)) +
            t * ((q ^ 2 : ℕ) :
              ZMod (outsidePrimeLeastStagePeriod P q)))) =
      leastOwnerStageBaseline P q := by
  have hcop :
      (q ^ 2).Coprime (outsidePrimeLeastStagePeriod P q) := by
    simpa [outsidePrimeLeastStagePeriod] using
      outsidePrime_ownerSquare_coprime_leastStagePeriod P hP hq hqP
  unfold leastOwnerStageBaseline
  exact zmod_sum_affine_coprime_eq_sum hcop
    (a.val : ZMod (outsidePrimeLeastStagePeriod P q))
    (leastOwnerStageDegreeOneField P q)

/-- Centered form: a fixed least-owner deletion residue has exactly zero
deviation from its conditioned complete-stage baseline. -/
theorem leastOwner_singleDeletionResidue_stageDeviationZero
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} (hq : q.Prime) (hqP : q ∉ P)
    (a : ZMod (q ^ 2)) :
    (∑ t : ZMod (outsidePrimeLeastStagePeriod P q),
        leastOwnerStageDegreeOneField P q
          ((a.val : ZMod (outsidePrimeLeastStagePeriod P q)) +
            t * ((q ^ 2 : ℕ) :
              ZMod (outsidePrimeLeastStagePeriod P q)))) -
      leastOwnerStageBaseline P q = 0 := by
  rw [leastOwner_singleDeletionResidue_preserves_stageBaseline
    P hP hq hqP a]
  ring

/-- Residues modulo an owner square on which at least one of the six physical
active forms is square-zero.  Repeated hits are represented only once because
this is a `Finset` of residues. -/
def leastOwnerDeletionResidues (q : ℕ) :
    Finset (ZMod (q ^ 2)) :=
  Finset.univ.filter fun a =>
    ∃ i : Fin 6, q ^ 2 ∣ tTransitionForm i a.val

/-- Exact baseline-consistent mass of all distinct owner-`q` square-deletion
residues across one complete stage cycle each. -/
def leastOwnerCompleteChannelMass (P : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ a ∈ leastOwnerDeletionResidues q,
    ∑ t : ZMod (outsidePrimeLeastStagePeriod P q),
      leastOwnerStageDegreeOneField P q
        ((a.val : ZMod (outsidePrimeLeastStagePeriod P q)) +
          t * ((q ^ 2 : ℕ) : ZMod (outsidePrimeLeastStagePeriod P q)))

/-- **Complete least-owner CRT recombination.**  After conditioning away all
smaller square-prime channels, the complete owner-`q` deletion contribution is
exactly the number of distinct owner-square deletion residues times the single
conditioned stage baseline.  No absolute value or analytic estimate appears. -/
theorem leastOwnerCompleteChannelMass_eq_card_mul_baseline
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) :
    leastOwnerCompleteChannelMass P q =
      ((leastOwnerDeletionResidues q).card : ℝ) *
        leastOwnerStageBaseline P q := by
  classical
  unfold leastOwnerCompleteChannelMass
  calc
    (∑ a ∈ leastOwnerDeletionResidues q,
      ∑ t : ZMod (outsidePrimeLeastStagePeriod P q),
        leastOwnerStageDegreeOneField P q
          ((a.val : ZMod (outsidePrimeLeastStagePeriod P q)) +
            t * ((q ^ 2 : ℕ) :
              ZMod (outsidePrimeLeastStagePeriod P q)))) =
        ∑ a ∈ leastOwnerDeletionResidues q,
          leastOwnerStageBaseline P q := by
      apply Finset.sum_congr rfl
      intro a ha
      exact leastOwner_singleDeletionResidue_preserves_stageBaseline
        P hP hq hqP a
    _ = ((leastOwnerDeletionResidues q).card : ℝ) *
          leastOwnerStageBaseline P q := by
      simp

/-- The centered complete owner channel vanishes identically.  This is the exact
finite CRT cancellation statement that survives the least-owner conditioning;
the only coherent term is the explicit stage baseline above. -/
theorem leastOwnerCompleteChannel_centered_eq_zero
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} (hq : q.Prime) (hqP : q ∉ P) :
    leastOwnerCompleteChannelMass P q -
      ((leastOwnerDeletionResidues q).card : ℝ) *
        leastOwnerStageBaseline P q = 0 := by
  rw [leastOwnerCompleteChannelMass_eq_card_mul_baseline P hP hq hqP]
  ring

end RHLean.Analysis
