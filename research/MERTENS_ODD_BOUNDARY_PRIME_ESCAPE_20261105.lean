import RHLean.Proof.AdaptivePrimeMatching
import «research.MERTENS_HEATH_BROWN_SIGNED»

/-!
# Finite prime/semiprime cancellation on the genuine odd boundary

This is the finite signed-residual consequence of 20261105-wheel-3/PE1,
independently accepted in 20261105-referee-11. The existing factor-two
cancellation is reused. The new endpoints are genuine unused integers,
with their original Mobius signs, and every partner has a unique factorization.

The result chooses equal-sized endpoint subsets; it does not implement the
paper's increasing-list involution or its raw binomial-occurrence lift.
The signed lift bridge below is at coefficient level with the strict cutoff.
No PNT asymptotic, small residual bound, recurrence, or exponent gain is claimed.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

def oddSquarefreeUpper (X : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 X).filter fun n => n % 2 = 1 ∧ X < 2 * n ∧ μ n ≠ 0

/-- The literal factor-two escape set, before zero coefficients are removed. -/
theorem primeEscapePart_two_Ioc (X : ℕ) :
    primeEscapePart 2 (Finset.Ioc 0 X) =
      (Finset.Ioc 0 X).filter (fun n => n % 2 = 1 ∧ X < 2 * n) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hnI, hescape⟩ := mem_primeEscapePart.mp hn
    obtain ⟨hn0, hnX⟩ := Finset.mem_Ioc.mp hnI
    have hnd : ¬ 2 ∣ n := by
      intro hd
      by_cases hs : 2 ^ 2 ∣ n
      · exact hescape (by rw [primeCarrierToggle_of_sq_dvd hs]; exact hnI)
      · apply hescape
        rw [primeCarrierToggle_of_dvd hd hs]
        exact Finset.mem_Ioc.mpr
          ⟨Nat.div_pos (Nat.le_of_dvd hn0 hd) (by decide),
            le_trans (Nat.div_le_self n 2) hnX⟩
    have hm : n % 2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hnd
    have hhalf : X < 2 * n := by
      rw [primeCarrierToggle_of_not_dvd hnd] at hescape
      simp only [Finset.mem_Ioc] at hescape
      omega
    exact Finset.mem_filter.mpr ⟨hnI, by omega, hhalf⟩
  · intro hn
    obtain ⟨hnI, hm, hhalf⟩ := Finset.mem_filter.mp hn
    have hnd : ¬ 2 ∣ n := by
      intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      omega
    refine mem_primeEscapePart.mpr ⟨hnI, ?_⟩
    rw [primeCarrierToggle_of_not_dvd hnd]
    simp only [Finset.mem_Ioc]
    omega

/-- The original prefix sum, not a model sum, is supported on this boundary. -/
theorem sum_moebius_eq_oddSquarefreeUpper (X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X, μ n) = ∑ n ∈ oddSquarefreeUpper X, μ n := by
  rw [sum_moebius_eq_sum_primeEscapePart Nat.prime_two]
  have heq : oddSquarefreeUpper X =
      (primeEscapePart 2 (Finset.Ioc 0 X)).filter (fun n => μ n ≠ 0) := by
    rw [primeEscapePart_two_Ioc]
    ext n
    simp [oddSquarefreeUpper, and_assoc]
  rw [heq]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  by_contra hmu
  exact hnot (Finset.mem_filter.mpr ⟨hn, hmu⟩)

/-- Actual upper-half semiprimes; the large factor exceeds every member of P. -/
def semiprimeEscapePartners (X : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (Finset.Ioc 0 X).filter fun n => X < 2 * n ∧
    ∃ s ∈ P, ∃ q : ℕ, q.Prime ∧ (∀ t ∈ P, t < q) ∧ n = s * q

theorem semiprimeEscapePartners_moebius
    {X n : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hn : n ∈ semiprimeEscapePartners X P) : μ n = 1 := by
  obtain ⟨_, _, s, hs, q, hq, hlarge, rfl⟩ := Finset.mem_filter.mp hn
  have hcop : Nat.Coprime s q := (Nat.Prime.coprime_iff_not_dvd (hP s hs)).mpr (by
    intro hd
    have heq := (Nat.prime_dvd_prime_iff_eq (hP s hs) hq).mp hd
    have hlt := hlarge s hs
    omega)
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime (hP s hs),
    ArithmeticFunction.moebius_apply_prime hq]
  norm_num

/-- A physical partner is counted only once across all small-prime channels. -/
theorem semiprimeEscape_factor_unique
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {s t q r : ℕ} (hs : s ∈ P) (ht : t ∈ P)
    (hr : r.Prime) (hrP : ∀ p ∈ P, p < r)
    (heq : s * q = t * r) : s = t ∧ q = r := by
  have hd : s ∣ t * r := by rw [← heq]; exact dvd_mul_right s q
  have hst : s = t := by
    rcases (hP s hs).dvd_mul.mp hd with h | h
    · exact (Nat.prime_dvd_prime_iff_eq (hP s hs) (hP t ht)).mp h
    · have hsr := (Nat.prime_dvd_prime_iff_eq (hP s hs) hr).mp h
      have hlt := hrP s hs
      omega
  refine ⟨hst, ?_⟩
  subst t
  exact Nat.eq_of_mul_eq_mul_left (hP s hs).pos heq

theorem semiprimeEscapePartners_subset_upper
    {X : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p % 2 = 1) :
    semiprimeEscapePartners X P ⊆ oddSquarefreeUpper X := by
  intro n hn
  have hmu := semiprimeEscapePartners_moebius (fun p hp => (hP p hp).1) hn
  obtain ⟨hnI, hhalf, s, hs, q, hq, hlarge, rfl⟩ := Finset.mem_filter.mp hn
  have hqodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with htwo | hodd
    · have hlt := hlarge s hs
      have htwole := (hP s hs).1.two_le
      omega
    · exact hodd
  refine Finset.mem_filter.mpr ⟨hnI, ?_, hhalf, ?_⟩
  · simp [Nat.mul_mod, (hP s hs).2, hqodd]
  · rw [hmu]; norm_num

theorem topHalfPrimes_subset_upper {X : ℕ} (hX : 4 ≤ X) :
    topHalfPrimes X ⊆ oddSquarefreeUpper X := by
  intro p hp
  obtain ⟨hpI, hprime, hhalf⟩ := mem_topHalfPrimes.mp hp
  have hodd : p % 2 = 1 := by
    rcases hprime.eq_two_or_odd with htwo | hodd
    · omega
    · exact hodd
  refine Finset.mem_filter.mpr ⟨hpI, hodd, hhalf, ?_⟩
  rw [ArithmeticFunction.moebius_apply_prime hprime]
  norm_num

/-- Equal-cardinality endpoint subsets remove exactly twice the available
capacity. No already-cancelled factor-two endpoint is reused. -/
theorem exists_prime_semiprime_residual
    {X : ℕ} (hX : 4 ≤ X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p % 2 = 1) :
    ∃ A C : Finset ℕ,
      A ⊆ topHalfPrimes X ∧ C ⊆ semiprimeEscapePartners X P ∧
      A.card = min (topHalfPrimes X).card (semiprimeEscapePartners X P).card ∧
      C.card = A.card ∧ Disjoint A C ∧
      (oddSquarefreeUpper X \ (A ∪ C)).card + 2 * A.card =
        (oddSquarefreeUpper X).card ∧
      (∑ n ∈ Finset.Ioc 0 X, μ n) =
        ∑ n ∈ oddSquarefreeUpper X \ (A ∪ C), μ n := by
  let t := min (topHalfPrimes X).card (semiprimeEscapePartners X P).card
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq
    (show t ≤ (topHalfPrimes X).card from Nat.min_le_left _ _)
  obtain ⟨C, hC, hCc⟩ := Finset.exists_subset_card_eq
    (show t ≤ (semiprimeEscapePartners X P).card from Nat.min_le_right _ _)
  have ha : ∀ n ∈ A, μ n = -1 := by
    intro n hn
    exact ArithmeticFunction.moebius_apply_prime (mem_topHalfPrimes.mp (hA hn)).2.1
  have hc : ∀ n ∈ C, μ n = 1 := by
    intro n hn
    exact semiprimeEscapePartners_moebius (fun p hp => (hP p hp).1) (hC hn)
  have hd : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro n hnA hnC
    have hna := ha n hnA
    have hnc := hc n hnC
    omega
  have hsub : A ∪ C ⊆ oddSquarefreeUpper X := by
    intro n hn
    rcases Finset.mem_union.mp hn with h | h
    · exact topHalfPrimes_subset_upper hX (hA h)
    · exact semiprimeEscapePartners_subset_upper hP (hC h)
  have hsumA : (∑ n ∈ A, μ n) = -(A.card : ℤ) := by
    calc
      _ = ∑ _n ∈ A, (-1 : ℤ) := Finset.sum_congr rfl ha
      _ = _ := by simp
  have hsumC : (∑ n ∈ C, μ n) = (C.card : ℤ) := by
    calc
      _ = ∑ _n ∈ C, (1 : ℤ) := Finset.sum_congr rfl hc
      _ = _ := by simp
  have hzero : (∑ n ∈ A ∪ C, μ n) = 0 := by
    rw [Finset.sum_union hd, hsumA, hsumC, hAc, hCc]
    omega
  refine ⟨A, C, hA, hC, hAc, hCc.trans hAc.symm, hd, ?_, ?_⟩
  · have hcard := Finset.card_sdiff_add_card_eq_card hsub
    rw [Finset.card_union_of_disjoint hd] at hcard
    omega
  · rw [sum_moebius_eq_oddSquarefreeUpper]
    have hsplit : (∑ n ∈ oddSquarefreeUpper X \ (A ∪ C), μ n) +
        (∑ n ∈ A ∪ C, μ n) = ∑ n ∈ oddSquarefreeUpper X, μ n :=
      Finset.sum_sdiff hsub
    simpa only [hzero, add_zero] using hsplit.symm

/-- The complete ordered square retains both mixed orientations. -/
theorem prime_semiprime_residual_complete_square
    {X : ℕ} {R : Finset ℕ}
    (hR : (∑ n ∈ Finset.Ioc 0 X, μ n) = ∑ n ∈ R, μ n) :
    (∑ n ∈ Finset.Ioc 0 X, μ n) ^ 2 =
      ∑ a ∈ R, ∑ b ∈ R, μ a * μ b := by
  rw [hR, pow_two, Finset.sum_mul_sum]

/-- The actual truncated convolution lift has the same residual below its
strict precision threshold. This is a coefficient-level source bridge. -/
theorem heathBrownLift_sum_eq_prime_semiprime_residual
    {N k X : ℕ} (hX : X < (N + 1) ^ k) {R : Finset ℕ}
    (hR : (∑ n ∈ Finset.Ioc 0 X, μ n) = ∑ n ∈ R, μ n) :
    (∑ n ∈ Finset.Ioc 0 X,
      RHLean.Analysis.MertensFiniteExtension.heathBrownLift
        (RHLean.Analysis.MertensFiniteExtension.mobiusPrefix N) k n) =
      ∑ n ∈ R, μ n := by
  rw [← hR]
  apply Finset.sum_congr rfl
  intro n hn
  exact RHLean.Analysis.MertensFiniteExtension.heathBrownLift_prefix_exact
    (lt_of_le_of_lt (Finset.mem_Ioc.mp hn).2 hX)

/-- A distinct endpoint cannot stay in the upper half throughout the entire
admission interval of p. Finite matching alone gives no static recurrence. -/
theorem upper_half_static_partner_eq {p m : ℕ} (hp : 0 < p)
    (hm : ∀ X : ℕ, p ≤ X → X < 2 * p → m ≤ X ∧ X < 2 * m) : m = p := by
  have hfirst := hm p (le_refl p) (by omega)
  have hlast := hm (2 * p - 1) (by omega) (by omega)
  omega

end RHLean.Proof
