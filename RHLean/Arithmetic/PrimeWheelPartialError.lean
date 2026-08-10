import Mathlib
import RHLean.Arithmetic.PrimeWheelMobiusRecovery
import RHLean.Arithmetic.PrimesUpToFrontier

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Arithmetic

/-- The prime-factorization part of `n` supported on primes at most `y`. -/
def primeWheelResolvedFactorization (y n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.filter (fun p : ℕ => p ≤ y) n.factorization

/-- The complementary prime-factorization part, supported on primes above `y`. -/
def primeWheelUnresolvedFactorization (y n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.filter (fun p : ℕ => ¬ p ≤ y) n.factorization

/-- The canonical `y`-resolved factor of `n`, with multiplicities retained. -/
def primeWheelResolvedPart (y n : ℕ) : ℕ :=
  (primeWheelResolvedFactorization y n).prod (fun p e => p ^ e)

/-- The canonical `y`-unresolved factor of `n`, with multiplicities retained. -/
def primeWheelUnresolvedPart (y n : ℕ) : ℕ :=
  (primeWheelUnresolvedFactorization y n).prod (fun p e => p ^ e)

/-- The partially completed corrected wheel through prime cutoff `y`. -/
def partialPrimeWheelSite (y upper n : ℕ) : ℤ :=
  correctedPrimeWheelSite (primesUpTo y) upper n

lemma primeWheelResolvedFactorization_le (y n : ℕ) :
    primeWheelResolvedFactorization y n ≤ n.factorization := by
  intro p
  simp [primeWheelResolvedFactorization]

lemma primeWheelUnresolvedFactorization_le (y n : ℕ) :
    primeWheelUnresolvedFactorization y n ≤ n.factorization := by
  intro p
  simp [primeWheelUnresolvedFactorization]

@[simp] theorem primeWheelResolvedPart_factorization (y n : ℕ) :
    (primeWheelResolvedPart y n).factorization =
      primeWheelResolvedFactorization y n := by
  unfold primeWheelResolvedPart
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (primeWheelResolvedFactorization_le y n)

@[simp] theorem primeWheelUnresolvedPart_factorization (y n : ℕ) :
    (primeWheelUnresolvedPart y n).factorization =
      primeWheelUnresolvedFactorization y n := by
  unfold primeWheelUnresolvedPart
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (primeWheelUnresolvedFactorization_le y n)

lemma primeWheelResolvedPart_ne_zero (y n : ℕ) :
    primeWheelResolvedPart y n ≠ 0 := by
  unfold primeWheelResolvedPart
  rw [Finsupp.prod_ne_zero_iff]
  intro p hp
  apply pow_ne_zero
  have hpN : p ∈ n.factorization.support := by
    have hp' := hp
    rw [primeWheelResolvedFactorization, Finsupp.support_filter] at hp'
    exact (Finset.mem_filter.mp hp').1
  exact (Nat.prime_of_mem_factorization hpN).ne_zero

lemma primeWheelUnresolvedPart_ne_zero (y n : ℕ) :
    primeWheelUnresolvedPart y n ≠ 0 := by
  unfold primeWheelUnresolvedPart
  rw [Finsupp.prod_ne_zero_iff]
  intro p hp
  apply pow_ne_zero
  have hpN : p ∈ n.factorization.support := by
    have hp' := hp
    rw [primeWheelUnresolvedFactorization, Finsupp.support_filter] at hp'
    exact (Finset.mem_filter.mp hp').1
  exact (Nat.prime_of_mem_factorization hpN).ne_zero

/-- The resolved and unresolved factors multiply back to `n`. -/
theorem primeWheelResolvedPart_mul_unresolvedPart
    (y : ℕ) {n : ℕ} (hn : n ≠ 0) :
    primeWheelResolvedPart y n * primeWheelUnresolvedPart y n = n := by
  unfold primeWheelResolvedPart primeWheelUnresolvedPart
    primeWheelResolvedFactorization primeWheelUnresolvedFactorization
  calc
    (Finsupp.filter (fun p : ℕ => p ≤ y) n.factorization).prod
          (fun p e => p ^ e) *
        (Finsupp.filter (fun p : ℕ => ¬ p ≤ y) n.factorization).prod
          (fun p e => p ^ e) =
      n.factorization.prod (fun p e => p ^ e) := by
        exact Finsupp.prod_filter_mul_prod_filter_not
          (fun p : ℕ => p ≤ y) n.factorization (fun p e => p ^ e)
    _ = n := Nat.prod_factorization_pow_eq_self hn

lemma primeWheelResolvedPart_primeFactor_le
    {y n p : ℕ} (hp : p ∈ (primeWheelResolvedPart y n).primeFactors) :
    p ≤ y := by
  have hp' : p ∈ (primeWheelResolvedPart y n).factorization.support := by
    simpa [Nat.support_factorization] using hp
  rw [primeWheelResolvedPart_factorization,
    primeWheelResolvedFactorization, Finsupp.support_filter] at hp'
  exact (Finset.mem_filter.mp hp').2

lemma primeWheelUnresolvedPart_primeFactor_gt
    {y n p : ℕ} (hp : p ∈ (primeWheelUnresolvedPart y n).primeFactors) :
    y < p := by
  have hp' : p ∈ (primeWheelUnresolvedPart y n).factorization.support := by
    simpa [Nat.support_factorization] using hp
  rw [primeWheelUnresolvedPart_factorization,
    primeWheelUnresolvedFactorization, Finsupp.support_filter] at hp'
  exact Nat.lt_of_not_ge (Finset.mem_filter.mp hp').2

/-- The canonical cutoff factors are coprime because their prime supports are disjoint. -/
theorem primeWheelResolvedPart_coprime_unresolvedPart (y n : ℕ) :
    (primeWheelResolvedPart y n).Coprime (primeWheelUnresolvedPart y n) := by
  rw [← Nat.disjoint_primeFactors
    (primeWheelResolvedPart_ne_zero y n)
    (primeWheelUnresolvedPart_ne_zero y n)]
  rw [Finset.disjoint_left]
  intro p hpA hpB
  exact (Nat.not_lt_of_ge (primeWheelResolvedPart_primeFactor_le hpA))
    (primeWheelUnresolvedPart_primeFactor_gt hpB)

lemma primeWheelResolvedPart_isSmooth (y n : ℕ) :
    IsPrimeWheelSmooth (primesUpTo y) (primeWheelResolvedPart y n) ↔
      Squarefree (primeWheelResolvedPart y n) := by
  constructor
  · exact fun h => h.1
  · intro hsq
    refine ⟨hsq, ?_⟩
    intro p hp
    exact mem_primesUpTo.mpr
      ⟨Nat.prime_of_mem_primeFactors hp, primeWheelResolvedPart_primeFactor_le hp⟩

lemma localPrimeComb_resolvedPart
    {y n p : ℕ} (hn : n ≠ 0) (hp : p ∈ primesUpTo y) :
    localPrimeComb p n = localPrimeComb p (primeWheelResolvedPart y n) := by
  have hpPrime : Nat.Prime p := prime_of_mem_primesUpTo hp
  have hpLe : p ≤ y := (mem_primesUpTo.mp hp).2
  have hfac :
      (primeWheelResolvedPart y n).factorization p = n.factorization p := by
    rw [primeWheelResolvedPart_factorization, primeWheelResolvedFactorization,
      Finsupp.filter_apply, if_pos hpLe]
  have ha0 := primeWheelResolvedPart_ne_zero y n
  have hsq : p ^ 2 ∣ n ↔ p ^ 2 ∣ primeWheelResolvedPart y n := by
    rw [hpPrime.pow_dvd_iff_le_factorization hn,
      hpPrime.pow_dvd_iff_le_factorization ha0, hfac]
  have hdvd : p ∣ n ↔ p ∣ primeWheelResolvedPart y n := by
    rw [hpPrime.dvd_iff_one_le_factorization hn,
      hpPrime.dvd_iff_one_le_factorization ha0, hfac]
  unfold localPrimeComb
  by_cases h2 : p ^ 2 ∣ n
  · have h2a := hsq.mp h2
    simp [h2, h2a]
  · have h2a : ¬ p ^ 2 ∣ primeWheelResolvedPart y n := by
      exact fun h => h2 (hsq.mpr h)
    by_cases h1 : p ∣ n
    · have h1a := hdvd.mp h1
      simp [h2, h2a, h1, h1a]
    · have h1a : ¬ p ∣ primeWheelResolvedPart y n := by
        exact fun h => h1 (hdvd.mpr h)
      simp [h2, h2a, h1, h1a]

/-- The partial raw comb sees exactly the resolved factor of `n`. -/
theorem seededPrimeComb_primesUpTo_eq_neg_moebius_resolvedPart
    (y : ℕ) {n : ℕ} (hn : n ≠ 0) :
    seededPrimeComb (primesUpTo y) n = -μ (primeWheelResolvedPart y n) := by
  have hraw :
      seededPrimeComb (primesUpTo y) n =
        seededPrimeComb (primesUpTo y) (primeWheelResolvedPart y n) := by
    unfold seededPrimeComb
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    exact localPrimeComb_resolvedPart hn hp
  rw [hraw]
  by_cases hsq : Squarefree (primeWheelResolvedPart y n)
  · exact seededPrimeComb_eq_neg_moebius_of_smooth
      (primesUpTo y)
      (fun p hp => prime_of_mem_primesUpTo hp)
      ((primeWheelResolvedPart_isSmooth y n).2 hsq)
  · have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    have hraw0 : seededPrimeComb (primesUpTo y) (primeWheelResolvedPart y n) = 0 := by
      rw [seededPrimeComb_eq_zero_of_not_squarefree]
      · rfl
      · intro p hpPrime hpLe
        exact mem_primesUpTo_of_prime_le hpPrime hpLe
      · exact Nat.pos_of_ne_zero (primeWheelResolvedPart_ne_zero y n)
      · exact Nat.le_refl _
      · exact hsq
    simp [hraw0, hmu]

lemma unresolvedPart_eq_one_iff_all_primeFactors_le
    (y : ℕ) {n : ℕ} (hn : n ≠ 0) :
    primeWheelUnresolvedPart y n = 1 ↔
      ∀ p ∈ n.primeFactors, p ≤ y := by
  constructor
  · intro hb p hp
    by_contra hpy
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hpos : 0 < n.factorization p := hpPrime.factorization_pos_of_dvd hn hpDvd
    have hfac : (primeWheelUnresolvedPart y n).factorization p = n.factorization p := by
      rw [primeWheelUnresolvedPart_factorization, primeWheelUnresolvedFactorization,
        Finsupp.filter_apply, if_pos hpy]
    rw [hb] at hfac
    simp at hfac
    omega
  · intro hall
    apply Nat.eq_one_of_dvd_one
    rw [← Nat.factorization_le_iff_dvd
      (primeWheelUnresolvedPart_ne_zero y n) one_ne_zero]
    intro p
    rw [primeWheelUnresolvedPart_factorization, primeWheelUnresolvedFactorization,
      Finsupp.filter_apply]
    by_cases hpy : p ≤ y
    · simp [hpy]
    · have hzero : n.factorization p = 0 := by
        by_contra hp0
        have hpSupport : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hp0
        have hpPrime : Nat.Prime p := Nat.prime_of_mem_factorization hpSupport
        have hpDvd : p ∣ n := Nat.dvd_of_factorization_pos hp0
        have hpPF : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hpPrime, hpDvd, hn⟩
        exact hpy (hall p hpPF)
      simp [hpy, hzero]

lemma not_smooth_of_unresolvedPart_ne_one
    (y : ℕ) {n : ℕ} (hn : n ≠ 0)
    (hb : primeWheelUnresolvedPart y n ≠ 1) :
    ¬ IsPrimeWheelSmooth (primesUpTo y) n := by
  intro hsmooth
  apply hb
  exact (unresolvedPart_eq_one_iff_all_primeFactors_le y hn).2 fun p hp =>
    (mem_primesUpTo.mp (hsmooth.2 p hp)).2

/-- Exact pointwise error formula for a partial prime wheel.

Writing `n = a_y(n) b_y(n)` with `a_y` carrying all prime powers at most `y`
and `b_y` all prime powers above `y`, the partial corrected field is already
exact when `b_y = 1`.  Otherwise the smooth correction is absent, the raw field
is `-μ(a_y)`, and the error is `μ(a_y) (1 + μ(b_y))`. -/
theorem partialPrimeWheel_error_eq
    (y upper : ℕ) {n : ℕ}
    (hnpos : 0 < n) (hnupper : n ≤ upper) :
    μ n - partialPrimeWheelSite y upper n =
      if primeWheelUnresolvedPart y n = 1 then 0
      else μ (primeWheelResolvedPart y n) *
        (1 + μ (primeWheelUnresolvedPart y n)) := by
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  let a := primeWheelResolvedPart y n
  let b := primeWheelUnresolvedPart y n
  have hab : a * b = n := by
    simpa [a, b] using primeWheelResolvedPart_mul_unresolvedPart y hn
  have hcop : a.Coprime b := by
    simpa [a, b] using primeWheelResolvedPart_coprime_unresolvedPart y n
  have hmu : μ n = μ a * μ b := by
    calc
      μ n = μ (a * b) := by rw [hab]
      _ = μ a * μ b :=
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  by_cases hb : b = 1
  · have hnSmooth : ∀ p ∈ n.primeFactors, p ≤ y := by
      exact (unresolvedPart_eq_one_iff_all_primeFactors_le y hn).1 (by simpa [b] using hb)
    have hcorrect : partialPrimeWheelSite y upper n = μ n := by
      unfold partialPrimeWheelSite
      by_cases hsq : Squarefree n
      · have hsmooth : IsPrimeWheelSmooth (primesUpTo y) n := by
          refine ⟨hsq, ?_⟩
          intro p hp
          exact mem_primesUpTo.mpr ⟨Nat.prime_of_mem_primeFactors hp, hnSmooth p hp⟩
        have hraw := seededPrimeComb_eq_neg_moebius_of_smooth
          (primesUpTo y) (fun p hp => prime_of_mem_primesUpTo hp) hsmooth
        simp [correctedPrimeWheelSite, primeWheelSmoothCoreSite,
          hnupper, hsmooth, hraw]
        ring
      · have hmu0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
        have hraw0 : seededPrimeComb (primesUpTo y) n = 0 := by
          rw [seededPrimeComb_eq_zero_of_not_squarefree]
          · rfl
          · intro p hpPrime hpLe
            exact mem_primesUpTo_of_prime_le hpPrime hpLe
          · exact hnpos
          · exact hnupper
          · exact hsq
        simp [correctedPrimeWheelSite, primeWheelSmoothCoreSite, hraw0, hmu0]
    simp [hb, b, hcorrect]
  · have hnonsmooth : ¬ IsPrimeWheelSmooth (primesUpTo y) n :=
      not_smooth_of_unresolvedPart_ne_one y hn (by simpa [b] using hb)
    have hraw := seededPrimeComb_primesUpTo_eq_neg_moebius_resolvedPart y hn
    have hpartial : partialPrimeWheelSite y upper n = -μ a := by
      unfold partialPrimeWheelSite correctedPrimeWheelSite primeWheelSmoothCoreSite
      simp [hnupper, hnonsmooth, a, hraw]
    rw [hmu, hpartial]
    simp [hb]
    ring

end RHLean.Arithmetic
