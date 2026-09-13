import Mathlib
import RHLean.Analysis.LogWeightedPrimeExtension

/-!
# Log-weighted squarefree child fibers

This module proves the local logarithmic child-fiber identity, extends it to all
children, and performs the exact finite reindex from fresh `(cofactor, prime)`
pairs to `(child product, prime)` pairs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

theorem prod_primeFactors_eq_self_of_squarefree
    {n : ℕ} (hs : Squarefree n) :
    ∏ p ∈ n.primeFactors, p = n := by
  calc
    (∏ p ∈ n.primeFactors, p) =
        ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
          apply Finset.prod_congr rfl
          intro p hp
          have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
          rw [Nat.factorization_eq_one_of_squarefree hs hpPrime hpDvd, pow_one]
    _ = n.factorization.prod (fun p k => p ^ k) := by
          rw [Nat.prod_factorization_eq_prod_primeFactors]
    _ = n := Nat.factorization_prod_pow_eq_self hs.ne_zero

theorem log_nat_finset_prod
    (s : Finset ℕ) (hpos : ∀ x ∈ s, 0 < x) :
    Real.log (((∏ x ∈ s, x : ℕ) : ℝ)) =
      ∑ x ∈ s, Real.log x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haPos : 0 < a := hpos a (Finset.mem_insert_self a s)
      have hsPos : ∀ x ∈ s, 0 < x := by
        intro x hx
        exact hpos x (Finset.mem_insert_of_mem hx)
      have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt haPos)
      have hs0 : (((∏ x ∈ s, x : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun x hx => Nat.ne_of_gt (hsPos x hx))
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Nat.cast_mul,
        Real.log_mul ha0 hs0, ih hsPos]

theorem sum_log_primeFactors_eq_log
    {n : ℕ} (hs : Squarefree n) :
    ∑ p ∈ n.primeFactors, Real.log p = Real.log n := by
  have hpos : ∀ p ∈ n.primeFactors, 0 < p := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos
  rw [← log_nat_finset_prod n.primeFactors hpos]
  rw [prod_primeFactors_eq_self_of_squarefree hs]

theorem prime_not_dvd_div_of_squarefree
    {n p : ℕ} (hs : Squarefree n) (hp : p ∈ n.primeFactors) :
    ¬ p ∣ n / p := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpDvd
  intro hpd
  have hsq : p * p ∣ n := by
    rw [← hmul]
    exact Nat.mul_dvd_mul_left p hpd
  exact hpPrime.not_isUnit (hs p hsq)

theorem moebiusReal_div_prime_eq_neg
    {n p : ℕ} (hs : Squarefree n) (hp : p ∈ n.primeFactors) :
    moebiusReal (n / p) = -moebiusReal n := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hnot := prime_not_dvd_div_of_squarefree hs hp
  have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpDvd
  have hflip := moebiusReal_prime_mul hpPrime hnot
  rw [hmul] at hflip
  linarith

theorem sum_log_p_mu_parent_eq_neg_mu_log
    (n : ℕ) (hs : Squarefree n) :
    (∑ p ∈ n.primeFactors,
      moebiusReal (n / p) * Real.log p) =
      -moebiusReal n * Real.log n := by
  calc
    (∑ p ∈ n.primeFactors,
        moebiusReal (n / p) * Real.log p) =
      ∑ p ∈ n.primeFactors,
        (-moebiusReal n) * Real.log p := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [moebiusReal_div_prime_eq_neg hs hp]
    _ = (-moebiusReal n) *
        (∑ p ∈ n.primeFactors, Real.log p) := by
          rw [Finset.mul_sum]
    _ = -moebiusReal n * Real.log n := by
          rw [sum_log_primeFactors_eq_log hs]

theorem freshPrimeDivisors_eq_primeFactors_of_squarefree
    {n : ℕ} (hs : Squarefree n) :
    freshPrimeDivisors n = n.primeFactors := by
  unfold freshPrimeDivisors
  apply Finset.filter_eq_self.mpr
  intro p hp
  exact prime_not_dvd_div_of_squarefree hs hp

theorem not_squarefree_div_of_fresh_prime
    {n p : ℕ} (hns : ¬Squarefree n)
    (hp : p ∈ freshPrimeDivisors n) :
    ¬Squarefree (n / p) := by
  rw [freshPrimeDivisors, Finset.mem_filter] at hp
  rcases hp with ⟨hpPF, hnot⟩
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpPF
  have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpPF
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpDvd
  intro hco
  have hcop : Nat.Coprime p (n / p) :=
    (hpPrime.coprime_iff_not_dvd).2 hnot
  have hsq : Squarefree (p * (n / p)) :=
    (Nat.squarefree_mul hcop).2 ⟨hpPrime.squarefree, hco⟩
  exact hns (by simpa [hmul] using hsq)

theorem sum_freshPrimeDivisors_mu_parent_log_eq_neg_mu_log (n : ℕ) :
    (∑ p ∈ freshPrimeDivisors n,
      moebiusReal (n / p) * Real.log p) =
      -moebiusReal n * Real.log n := by
  by_cases hs : Squarefree n
  · rw [freshPrimeDivisors_eq_primeFactors_of_squarefree hs]
    exact sum_log_p_mu_parent_eq_neg_mu_log n hs
  · have hmuN : moebiusReal n = 0 := by
      unfold moebiusReal
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      norm_num
    rw [hmuN]
    simp only [neg_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have hnsParent := not_squarefree_div_of_fresh_prime hs hp
    have hmuParent : moebiusReal (n / p) = 0 := by
      unfold moebiusReal
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsParent]
      norm_num
    rw [hmuParent, zero_mul]

/-- Child-first fresh logarithmic mass on the doubling block. -/
def logFreshChildFiberMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2 * N),
    ∑ p ∈ freshPrimeDivisors n,
      moebiusReal (n / p) * Real.log p

theorem logFreshChildFiberMass_eq_neg_logWeightedBlock (N : ℕ) :
    logFreshChildFiberMass N = -logWeightedBlock N := by
  unfold logFreshChildFiberMass logWeightedBlock
  calc
    (∑ n ∈ Finset.Ioc N (2 * N),
        ∑ p ∈ freshPrimeDivisors n,
          moebiusReal (n / p) * Real.log p) =
      ∑ n ∈ Finset.Ioc N (2 * N),
        (-moebiusReal n * Real.log n) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact sum_freshPrimeDivisors_mu_parent_log_eq_neg_mu_log n
    _ = -∑ n ∈ Finset.Ioc N (2 * N),
        moebiusReal n * Real.log n := by
          rw [Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro n hn
          ring

/-! ## Exact rectangular reindex `(c,p) -> (c*p,p)` -/

/-- Active fresh cofactor/prime pairs in the original rectangular definition. -/
def logFreshExtensionPairSet (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (2 * N)).product (Finset.Icc 2 (2 * N))).filter fun cp =>
    cp.2.Prime ∧ N < cp.1 * cp.2 ∧ cp.1 * cp.2 ≤ 2 * N ∧ ¬ cp.2 ∣ cp.1

/-- The same active pairs indexed by their child product. -/
def logFreshChildPairSet (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ioc N (2 * N)).product (Finset.Icc 2 (2 * N))).filter fun np =>
    np.2 ∈ freshPrimeDivisors np.1

theorem logFreshPrimeExtensionMass_eq_sourcePairSum (N : ℕ) :
    logFreshPrimeExtensionMass N =
      ∑ cp ∈ logFreshExtensionPairSet N,
        moebiusReal cp.1 * Real.log cp.2 := by
  unfold logFreshPrimeExtensionMass logFreshExtensionPairSet
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro p hp
  unfold logFreshPrimeExtensionTerm
  by_cases h : p.Prime ∧ N < c * p ∧ c * p ≤ 2 * N ∧ ¬p ∣ c <;>
    simp [h]

private theorem freshPrimeDivisors_subset_blockPrimeRange
    {N n : ℕ} (hn : n ∈ Finset.Ioc N (2 * N)) :
    freshPrimeDivisors n ⊆ Finset.Icc 2 (2 * N) := by
  intro p hp
  rw [freshPrimeDivisors, Finset.mem_filter] at hp
  rcases hp with ⟨hpPF, _hnot⟩
  rcases Nat.mem_primeFactors.mp hpPF with ⟨hpPrime, hpDvd, hn0⟩
  have hpLeN : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpDvd
  exact Finset.mem_Icc.mpr
    ⟨hpPrime.two_le, hpLeN.trans (Finset.mem_Ioc.mp hn).2⟩

theorem childPairSum_eq_logFreshChildFiberMass (N : ℕ) :
    (∑ np ∈ logFreshChildPairSet N,
      moebiusReal (np.1 / np.2) * Real.log np.2) =
      logFreshChildFiberMass N := by
  unfold logFreshChildPairSet logFreshChildFiberMass
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  have hsub := freshPrimeDivisors_subset_blockPrimeRange hn
  have hfilter :
      (Finset.Icc 2 (2 * N)).filter (fun p => p ∈ freshPrimeDivisors n) =
        freshPrimeDivisors n := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_hpRange, hpFresh⟩
      exact hpFresh
    · intro hpFresh
      exact ⟨hsub hpFresh, hpFresh⟩
  rw [← Finset.sum_filter, hfilter]

/-- The multiplication map is a literal finite bijection between the two fresh
pair carriers. -/
theorem logFreshExtensionPairSet_sum_eq_childPairSet_sum (N : ℕ) :
    (∑ cp ∈ logFreshExtensionPairSet N,
      moebiusReal cp.1 * Real.log cp.2) =
    ∑ np ∈ logFreshChildPairSet N,
      moebiusReal (np.1 / np.2) * Real.log np.2 := by
  classical
  refine Finset.sum_bij
    (fun cp _hcp => (cp.1 * cp.2, cp.2)) ?_ ?_ ?_ ?_
  · intro cp hcp
    rw [logFreshExtensionPairSet, Finset.mem_filter,
      Finset.mem_product] at hcp
    rcases hcp with ⟨⟨hcRange, hpRange⟩, hpPrime, hlower, hupper, hfresh⟩
    rw [logFreshChildPairSet, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨Finset.mem_Ioc.mpr ⟨hlower, hupper⟩, hpRange⟩, ?_⟩
    unfold freshPrimeDivisors
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · apply Nat.mem_primeFactors.mpr
      refine ⟨hpPrime, ?_, ?_⟩
      · exact ⟨cp.1, by simp [Nat.mul_comm]⟩
      · omega
    · simpa using hfresh
  · intro a ha b hb hab
    have hpEq : a.2 = b.2 := congrArg Prod.snd hab
    have hprod : a.1 * a.2 = b.1 * b.2 := congrArg Prod.fst hab
    have hcEq : a.1 = b.1 := by
      rw [hpEq] at hprod
      exact Nat.mul_right_cancel hprod
    exact Prod.ext hcEq hpEq
  · intro np hnp
    rw [logFreshChildPairSet, Finset.mem_filter,
      Finset.mem_product] at hnp
    rcases hnp with ⟨⟨hnRange, hpRange⟩, hpFresh⟩
    rw [freshPrimeDivisors, Finset.mem_filter] at hpFresh
    rcases hpFresh with ⟨hpPF, hfresh⟩
    rcases Nat.mem_primeFactors.mp hpPF with ⟨hpPrime, hpDvd, hn0⟩
    let c := np.1 / np.2
    have hmul : c * np.2 = np.1 := by
      simpa [c] using Nat.div_mul_cancel hpDvd
    have hcPos : 0 < c := by
      exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpDvd) hpPrime.pos
    have hcUpper : c ≤ 2 * N := by
      exact (Nat.div_le_self np.1 np.2).trans (Finset.mem_Ioc.mp hnRange).2
    refine ⟨(c, np.2), ?_, ?_⟩
    · rw [logFreshExtensionPairSet, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨Finset.mem_Icc.mpr ⟨hcPos, hcUpper⟩, hpRange⟩,
        hpPrime, ?_, ?_, ?_⟩
      · simpa [hmul] using (Finset.mem_Ioc.mp hnRange).1
      · simpa [hmul] using (Finset.mem_Ioc.mp hnRange).2
      · simpa [c] using hfresh
    · apply Prod.ext
      · exact hmul
      · rfl
  · intro cp hcp
    rw [logFreshExtensionPairSet, Finset.mem_filter,
      Finset.mem_product] at hcp
    rcases hcp with ⟨⟨_hcRange, _hpRange⟩, hpPrime, _hlower, _hupper, _hfresh⟩
    rw [Nat.mul_div_right cp.1 hpPrime.pos]

/-- **Global fresh child-fiber identity.**  This discharges the typed arithmetic
statement left open in `LogWeightedPrimeExtension`: the rectangular fresh-prime
extension mass is exactly the negative logarithmic Möbius block. -/
theorem logWeightedChildFiberIdentity : LogWeightedChildFiberIdentityStatement := by
  intro N
  rw [logFreshPrimeExtensionMass_eq_sourcePairSum,
    logFreshExtensionPairSet_sum_eq_childPairSet_sum,
    childPairSum_eq_logFreshChildFiberMass,
    logFreshChildFiberMass_eq_neg_logWeightedBlock]

end RHLean.Analysis
