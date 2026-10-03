import Mathlib
import RHLean.Proof.TerminalMertensReduction
import RHLean.Proof.ReplacementFibreCofactorWindows
import «research.NNS_ZERO_TARGET_ONE_BLOCK_ENERGY»

/-!
# Square-time derivative of the canonical prime-partner response

For a fixed cofactor c the canonical response at root R is the finite set of
fresh prime extensions q with

  R <= c*q <= R^2 - 1.

Advancing square time R -> R+1 therefore has two and only two effects:

* an upper-wall birth: c*q enters the new square block
  [R^2,(R+1)^2);
* a lower-wall death: the old partner lies exactly at c*q = R.

This is the pointwise carrier law behind the #877 update
  mu(R) - canonicalTotalIncrement R.
The root atom is the lower-wall death; it is not an unrelated correction.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Prime partners born when square time advances from R to R+1. -/
def squareRootCanonicalRoughTimeBirthBoundary (R c : ℕ) : Finset ℕ :=
  squareRootCanonicalRoughPrimePartnerSet (R + 1) c \
    squareRootCanonicalRoughPrimePartnerSet R c

/-- Prime partners deleted at the moving lower wall when square time advances. -/
def squareRootCanonicalRoughTimeDeathBoundary (R c : ℕ) : Finset ℕ :=
  squareRootCanonicalRoughPrimePartnerSet R c \
    squareRootCanonicalRoughPrimePartnerSet (R + 1) c

/-- **Upper-wall birth = one square block.** -/
theorem mem_squareRootCanonicalRoughTimeBirthBoundary_iff
    {R c q : ℕ} (hR : 2 ≤ R) (hc : 0 < c) :
    q ∈ squareRootCanonicalRoughTimeBirthBoundary R c ↔
      q.Prime ∧
        canonicalLargestPrimeFactor c < q ∧
        R ^ 2 ≤ c * q ∧
        c * q < (R + 1) ^ 2 := by
  unfold squareRootCanonicalRoughTimeBirthBoundary
  rw [Finset.mem_sdiff,
    mem_squareRootCanonicalRoughPrimePartnerSet_iff (by omega : 2 ≤ R + 1) hc,
    mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hc]
  unfold squareRootEndpoint
  constructor
  · rintro ⟨⟨hq, hrough, hloNew, hhiNew⟩, hnotOld⟩
    have hnotUpperOld : R ^ 2 - 1 < c * q := by
      by_contra h
      apply hnotOld
      refine ⟨hq, hrough, ?_, Nat.le_of_not_gt h⟩
      omega
    refine ⟨hq, hrough, ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨hq, hrough, hloBlock, hhiBlock⟩
    constructor
    · refine ⟨hq, hrough, ?_, ?_⟩ <;> omega
    · intro hold
      exact (Nat.not_le_of_gt (by omega : R ^ 2 - 1 < c * q)) hold.2.2.2

/-- **Lower-wall death is exactly the old root product c*q=R.** -/
theorem mem_squareRootCanonicalRoughTimeDeathBoundary_iff
    {R c q : ℕ} (hR : 2 ≤ R) (hc : 0 < c) :
    q ∈ squareRootCanonicalRoughTimeDeathBoundary R c ↔
      q.Prime ∧
        canonicalLargestPrimeFactor c < q ∧
        c * q = R := by
  unfold squareRootCanonicalRoughTimeDeathBoundary
  rw [Finset.mem_sdiff,
    mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hc,
    mem_squareRootCanonicalRoughPrimePartnerSet_iff (by omega : 2 ≤ R + 1) hc]
  unfold squareRootEndpoint
  constructor
  · rintro ⟨⟨hq, hrough, hloOld, hhiOld⟩, hnotNew⟩
    have hupperNew : c * q ≤ (R + 1) ^ 2 - 1 := by
      have : R ^ 2 - 1 ≤ (R + 1) ^ 2 - 1 := by nlinarith
      omega
    have hltNew : c * q < R + 1 := by
      by_contra h
      apply hnotNew
      exact ⟨hq, hrough, Nat.le_of_not_gt h, hupperNew⟩
    exact ⟨hq, hrough, by omega⟩
  · rintro ⟨hq, hrough, hroot⟩
    constructor
    · refine ⟨hq, hrough, ?_, ?_⟩ <;> omega
    · intro hnew
      omega

/-- The response finite difference is exactly births minus deaths. -/
theorem squareRootCanonicalRoughPrimePartnerCount_succ_sub_eq_timeBirth_sub_death
    (R c : ℕ) :
    squareRootCanonicalRoughPrimePartnerCount (R + 1) c -
        squareRootCanonicalRoughPrimePartnerCount R c =
      ((squareRootCanonicalRoughTimeBirthBoundary R c).card : ℂ) -
        ((squareRootCanonicalRoughTimeDeathBoundary R c).card : ℂ) := by
  rw [squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card,
    squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card]
  have hA := Finset.card_sdiff_add_card_inter
    (squareRootCanonicalRoughPrimePartnerSet (R + 1) c)
    (squareRootCanonicalRoughPrimePartnerSet R c)
  have hB := Finset.card_sdiff_add_card_inter
    (squareRootCanonicalRoughPrimePartnerSet R c)
    (squareRootCanonicalRoughPrimePartnerSet (R + 1) c)
  have hInter :
      (squareRootCanonicalRoughPrimePartnerSet R c ∩
          squareRootCanonicalRoughPrimePartnerSet (R + 1) c).card =
        (squareRootCanonicalRoughPrimePartnerSet (R + 1) c ∩
          squareRootCanonicalRoughPrimePartnerSet R c).card := by
    rw [Finset.inter_comm]
  have hInt :
      ((squareRootCanonicalRoughPrimePartnerSet (R + 1) c).card : ℤ) -
          ((squareRootCanonicalRoughPrimePartnerSet R c).card : ℤ) =
        ((squareRootCanonicalRoughTimeBirthBoundary R c).card : ℤ) -
          ((squareRootCanonicalRoughTimeDeathBoundary R c).card : ℤ) := by
    unfold squareRootCanonicalRoughTimeBirthBoundary
      squareRootCanonicalRoughTimeDeathBoundary
    omega
  exact_mod_cast hInt

/-- A time-birth prime produces a literal integer in the new square block. -/
theorem squareRootCanonicalRoughTimeBirth_product_mem_squareBlock
    {R c q : ℕ} (hR : 2 ≤ R) (hc : 0 < c)
    (hq : q ∈ squareRootCanonicalRoughTimeBirthBoundary R c) :
    c * q ∈ canonicalSquareBlock R := by
  have h :=
    (mem_squareRootCanonicalRoughTimeBirthBoundary_iff hR hc).1 hq
  simpa [canonicalSquareBlock, Finset.mem_Ico] using h.2.2

/-- If the parent is squarefree, a time-birth is exactly a fresh squarefree
prime extension with canonical parent c. -/
theorem squareRootCanonicalRoughTimeBirth_product_mem_parentFiber
    {R c q : ℕ} (hR : 3 ≤ R) (hc : 0 < c)
    (hcsq : Squarefree c)
    (hq : q ∈ squareRootCanonicalRoughTimeBirthBoundary R c) :
    c * q ∈ canonicalParentFiber R c := by
  have hdata :=
    (mem_squareRootCanonicalRoughTimeBirthBoundary_iff (by omega) hc).1 hq
  rcases hdata with ⟨hqPrime, hrough, hlo, hhi⟩
  have hqNotDvd : ¬ q ∣ c := by
    intro hdiv
    have hqmem : q ∈ c.primeFactors :=
      (Nat.mem_primeFactors.mpr ⟨hqPrime, hdiv, by
        intro hc1
        subst c
        norm_num at hrough⟩)
    have hqle : q ≤ canonicalLargestPrimeFactor c :=
      primeFactor_le_canonicalLargestPrimeFactor
        (by
          have hc1 : 1 ≤ c := hc
          by_contra hnot
          have : c = 1 := by omega
          subst c
          norm_num at hrough)
        hqmem
    omega
  have hprodSq : Squarefree (c * q) := by
    exact hcsq.mul (hqPrime.squarefree) (Nat.Coprime.symm
      (hqPrime.coprime_iff_not_dvd.mpr hqNotDvd))
  have hcq1 : 1 < c * q := by
    have hq2 := hqPrime.two_le
    nlinarith
  have hlpf : canonicalLargestPrimeFactor (c * q) = q := by
    simpa [Nat.mul_comm] using
      canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hqPrime hrough
  have hparent : canonicalCofactor (c * q) = c := by
    have hprod := canonicalCofactor_mul_largestPrimeFactor hcq1
    rw [hlpf] at hprod
    have hqpos := hqPrime.pos
    nlinarith
  unfold canonicalParentFiber
  simp only [Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨hlo, hhi⟩, hprodSq, hparent⟩

/-- Every canonical parent-fibre child recovers a unique upper-wall birth
prime, namely its largest prime factor. -/
theorem canonicalParentFiber_largestPrimeFactor_mem_timeBirth
    {R c m : ℕ} (hR : 3 ≤ R)
    (hm : m ∈ canonicalParentFiber R c) :
    canonicalLargestPrimeFactor m ∈
      squareRootCanonicalRoughTimeBirthBoundary R c := by
  rw [canonicalParentFiber, Finset.mem_filter] at hm
  rcases hm with ⟨hmBlock, hmsq, hparent⟩
  have hmBounds : R ^ 2 ≤ m ∧ m < (R + 1) ^ 2 := by
    simpa [squareBlockInterval, Finset.mem_Ico] using hmBlock
  have hm1 : 1 < m := by
    have h9 : 9 ≤ R ^ 2 := by nlinarith
    omega
  have hcpos0 : 0 < canonicalCofactor m := canonicalCofactor_pos hm1
  have hcpos : 0 < c := by simpa [hparent] using hcpos0
  have hqPrime : (canonicalLargestPrimeFactor m).Prime :=
    canonicalLargestPrimeFactor_prime hm1
  have hrough0 :
      canonicalLargestPrimeFactor (canonicalCofactor m) <
        canonicalLargestPrimeFactor m :=
    canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hm1 hmsq
  have hrough :
      canonicalLargestPrimeFactor c < canonicalLargestPrimeFactor m := by
    simpa [hparent] using hrough0
  have hprod0 := canonicalCofactor_mul_largestPrimeFactor hm1
  have hprod :
      c * canonicalLargestPrimeFactor m = m := by
    simpa [hparent] using hprod0
  apply (mem_squareRootCanonicalRoughTimeBirthBoundary_iff
    (by omega : 2 ≤ R) hcpos).2
  exact ⟨hqPrime, hrough, by simpa [hprod] using hmBounds.1,
    by simpa [hprod] using hmBounds.2⟩

/-- Birth-prime multiplication and largest-prime extraction are inverse on the
squarefree parent fibre. -/
theorem canonicalLargestPrimeFactor_mul_timeBirth
    {R c q : ℕ} (hR : 3 ≤ R) (hc : 0 < c)
    (hcsq : Squarefree c)
    (hq : q ∈ squareRootCanonicalRoughTimeBirthBoundary R c) :
    canonicalLargestPrimeFactor (c * q) = q := by
  have hdata :=
    (mem_squareRootCanonicalRoughTimeBirthBoundary_iff
      (by omega : 2 ≤ R) hc).1 hq
  exact canonicalLargestPrimeFactor_mul_prime_eq_of_rough
    hc hdata.1 hdata.2.1

/-- **Current-block parent fibres are exactly square-time response births.**

For a squarefree old parent c, multiplication q -> c*q is a bijection from the
new partner primes to the canonical children in the new square block. -/
theorem card_timeBirthBoundary_eq_parentFiber
    {R c : ℕ} (hR : 3 ≤ R) (hc : 0 < c) (hcsq : Squarefree c) :
    (squareRootCanonicalRoughTimeBirthBoundary R c).card =
      (canonicalParentFiber R c).card := by
  classical
  refine Finset.card_bij (fun q _hq => c * q) ?_ ?_ ?_
  · intro q hq
    exact squareRootCanonicalRoughTimeBirth_product_mem_parentFiber
      hR hc hcsq hq
  · intro q₁ hq₁ q₂ hq₂ heq
    exact Nat.eq_of_mul_eq_mul_left hc heq
  · intro m hm
    let q := canonicalLargestPrimeFactor m
    have hq :
        q ∈ squareRootCanonicalRoughTimeBirthBoundary R c := by
      dsimp [q]
      exact canonicalParentFiber_largestPrimeFactor_mem_timeBirth hR hm
    refine ⟨q, hq, ?_⟩
    rw [show q = canonicalLargestPrimeFactor m by rfl]
    rw [canonicalParentFiber, Finset.mem_filter] at hm
    have hm1 : 1 < m := by
      have hmBlock := hm.1
      have hmLow : R ^ 2 ≤ m := by
        simpa [squareBlockInterval, Finset.mem_Ico] using hmBlock
      have h9 : 9 ≤ R ^ 2 := by nlinarith
      omega
    have hprod := canonicalCofactor_mul_largestPrimeFactor hm1
    simpa [hm.2.2] using hprod

end RHLean.Proof
