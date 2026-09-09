import Mathlib
import RHLean.Proof.OneBlockInvariant
import RHLean.Proof.SecondContactInterfaceFluxRegister
import RHLean.Proof.SquareRootLowPrimeGoWallPartnerReassembly

/-!
# The endpoint square-residual mass carries no owner index

The literal first-owner wall identity leaves the square-residual mass

`squareRootLowPrimeLiteralWallSquareResidualMass R K = sum_{q <= K} F_{q^-}(X_R/q^2)`

inside the endpoint ledger.  Written that way it invites the wrong attack: bound
each owner's -- or each source scale's -- state separately and add the results
up.  That route cannot work here.  Each owner term is a signed Mertens-type
state at its own cutoff `B_q`, so a separate estimate of size `B_q/2` for each,
summed, is already `sum_q X/(2q^2)`, a constant multiple of `X`: strictly worse
than the single global support bound that the recombined population satisfies,
and it discards every cancellation between owners in the process.

This module removes the owner index from the object instead of estimating
through it.

`endpointSecondContactPopulation K X` is defined intrinsically -- squarefree
`m` with `P+(m) <= K` and `P+(m)*m <= X`, with no owner schedule anywhere in the
definition -- and
`squareRootLowPrimeGoSecondContactSources_wallSchedule_eq_endpointPopulation`
proves it is *the same finite set* as the owner-indexed Go source population on
the literal wall schedule.  Hence

`squareRootLowPrimeLiteralWallSquareResidualMass R K = - sum_{m in P(K,X_R)} mu(m)`,

one globally signed Mobius mass over one arithmetic population.  Substituted
back into the compiled wall identity, the endpoint ledger carries exactly that
one mass and nothing owner-indexed
(`squareRootLowPrimeLiteralWallPartnerLedgerMass_eq_endpoint_add_populationMass`).

The remaining sections describe the structure the single object actually has,
so that a contraction can be attempted on it directly.

* The sign is not free.  On this population `mu(m) = (-1)^omega(m)`, so the mass
  is an alternating sum of level cardinalities, graded by the number of distinct
  primes.
* The levels are separated by scale.  A source at level `k` satisfies
  `m^(k+1) <= X^k`, that is, it lies at scale `X^(k/(k+1))`.  Level one is
  exactly the primes `m` with `m^2 <= X`, the root-scale anchor already
  isolated; only levels of unbounded `k` reach the top scale at all.
* The whole object still admits one global estimate,
  `|mass| <= sqrt X + X/3`, taken once on the recombined population rather than
  owner by owner.

No new estimate, Mertens input, prime-distribution bound or asymptotic claim is
introduced here.  The graded scale law is exact and elementary, and it is *not*
a cancellation statement: bounding the alternating sum of level cardinalities by
anything smaller than their total remains open, and is precisely where the next
contraction has to occur.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-! ## Integer recombination of the owner-indexed residual total -/

/-- Integer form of the global signed recombination: the Möbius mass of the Go
second-contact population is the negated square-residual total. -/
theorem squareRootLowPrimeGoSecondContactSourceMoebiusSum_eq_neg_residualTotal
    {Q : Finset ℕ} {X : ℕ} (hprime : ∀ q ∈ Q, q.Prime) :
    (∑ m ∈ squareRootLowPrimeGoSecondContactSources Q X, μ m) =
      -squareRootLowPrimeGoWallSquareResidualTotal Q X := by
  have hpoint : ∀ q ∈ Q,
      (∑ m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X, μ m) =
        -squareRootLowPrimeGoWallSquareResidual q X := by
    intro q hqQ
    have hq := hprime q hqQ
    have himage :
        (∑ m ∈ squareRootLowPrimeGoWallSquareResidualChildren q X, μ m) =
          ∑ c ∈ squareRootLowPrimeGoSmoothCofactors q (X / (q * q)), μ (q * c) := by
      rw [squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage hq]
      apply Finset.sum_image
      intro a _ha b _hb hab
      exact Nat.eq_of_mul_eq_mul_left hq.pos hab
    rw [himage, squareRootLowPrimeGoWallSquareResidual_eq_smoothCofactorSum hq,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro c hc
    rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hc with
      ⟨hc1, _hcB, _hcsq, hrough⟩
    have hcPos : 0 < c := by omega
    have hflip : μ (c * q) = -μ c :=
      moebius_mul_prime_eq_neg_of_rough hcPos hq hrough
    have hcomm : q * c = c * q := Nat.mul_comm q c
    rw [hcomm, hflip]
  have hdisj :=
    squareRootLowPrimeGoWallSquareResidualChildren_pairwiseDisjoint Q X hprime
  unfold squareRootLowPrimeGoSecondContactSources
    squareRootLowPrimeGoWallSquareResidualTotal
  rw [Finset.sum_biUnion hdisj, Finset.sum_congr rfl hpoint,
    Finset.sum_neg_distrib]

/-! ## The intrinsic endpoint population -/

/-- **Endpoint second-contact population, owner-free.**  A squarefree `m` whose
canonical largest prime is admitted by the wall schedule and which still fits
after one further multiplication by that prime.  No owner index occurs in this
definition. -/
def endpointSecondContactPopulation (K X : ℕ) : Finset ℕ :=
  (Finset.Icc 2 X).filter fun m =>
    Squarefree m ∧ canonicalLargestPrimeFactor m ≤ K ∧
      canonicalLargestPrimeFactor m * m ≤ X

theorem mem_endpointSecondContactPopulation {K X m : ℕ} :
    m ∈ endpointSecondContactPopulation K X ↔
      (2 ≤ m ∧ m ≤ X) ∧
        Squarefree m ∧ canonicalLargestPrimeFactor m ≤ K ∧
          canonicalLargestPrimeFactor m * m ≤ X := by
  unfold endpointSecondContactPopulation
  rw [Finset.mem_filter, Finset.mem_Icc]

/-- **The owner index is redundant.**  The owner-indexed Go source population on
the literal wall schedule is literally the intrinsic endpoint population. -/
theorem squareRootLowPrimeGoSecondContactSources_wallSchedule_eq_endpointPopulation
    (K X : ℕ) :
    squareRootLowPrimeGoSecondContactSources
        (squareRootLowPrimeWallOldPrimeSet K) X =
      endpointSecondContactPopulation K X := by
  ext m
  constructor
  · intro hm
    unfold squareRootLowPrimeGoSecondContactSources at hm
    rcases Finset.mem_biUnion.mp hm with ⟨q, hqQ, hmq⟩
    rcases mem_squareRootLowPrimeWallOldPrimeSet.mp hqQ with ⟨hqPrime, hqK⟩
    have howner :=
      squareRootLowPrimeGoWallSquareResidualChild_owner hqPrime hmq
    have hcontactq :=
      squareRootLowPrimeGoWallSquareResidualChild_owner_mul_le hqPrime hmq
    rw [squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage
      hqPrime] at hmq
    rcases Finset.mem_image.mp hmq with ⟨c, hc, hcm⟩
    rcases mem_squareRootLowPrimeGoSmoothCofactors.mp hc with
      ⟨hc1, _hcB, hcsq, hrough⟩
    have hcPos : 0 < c := by omega
    have hflip : μ (c * q) = -μ c :=
      moebius_mul_prime_eq_neg_of_rough hcPos hqPrime hrough
    have hcne : μ c ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hcsq
    have hmne : μ m ≠ 0 := by
      rw [← hcm, Nat.mul_comm, hflip]
      simpa using hcne
    have hsq : Squarefree m :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmne
    have htwo : 2 * 1 ≤ q * c := Nat.mul_le_mul hqPrime.two_le hc1
    have hm2 : 2 ≤ m := by omega
    have hdouble : 2 * m ≤ q * m := Nat.mul_le_mul_right m hqPrime.two_le
    have hmX : m ≤ X := by omega
    refine mem_endpointSecondContactPopulation.mpr ⟨⟨hm2, hmX⟩, hsq, ?_, ?_⟩
    · rw [howner]
      exact hqK
    · rw [howner]
      exact hcontactq
  · intro hm
    rcases mem_endpointSecondContactPopulation.mp hm with
      ⟨⟨hm2, _hmX⟩, hsq, hK, hcontact⟩
    have hm1 : 1 < m := by omega
    have hqPrime : (canonicalLargestPrimeFactor m).Prime :=
      canonicalLargestPrimeFactor_prime hm1
    have hqQ : canonicalLargestPrimeFactor m ∈
        squareRootLowPrimeWallOldPrimeSet K :=
      mem_squareRootLowPrimeWallOldPrimeSet.mpr ⟨hqPrime, hK⟩
    have hfactor :
        canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
      canonicalCofactor_mul_largestPrimeFactor hm1
    have hcsq : Squarefree (canonicalCofactor m) :=
      hsq.squarefree_of_dvd ⟨canonicalLargestPrimeFactor m, hfactor.symm⟩
    have hrough :
        canonicalLargestPrimeFactor (canonicalCofactor m) <
          canonicalLargestPrimeFactor m :=
      canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hm1 hsq
    have hcPos : 1 ≤ canonicalCofactor m := by
      by_contra hcon
      have hc0 : canonicalCofactor m = 0 := by omega
      rw [hc0, Nat.zero_mul] at hfactor
      omega
    have hqqPos : 0 < canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m :=
      Nat.mul_pos hqPrime.pos hqPrime.pos
    have hcB : canonicalCofactor m ≤
        X / (canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m) := by
      refine (Nat.le_div_iff_mul_le hqqPos).2 ?_
      calc
        canonicalCofactor m *
            (canonicalLargestPrimeFactor m * canonicalLargestPrimeFactor m) =
            canonicalLargestPrimeFactor m *
              (canonicalCofactor m * canonicalLargestPrimeFactor m) := by ring
        _ = canonicalLargestPrimeFactor m * m := by rw [hfactor]
        _ ≤ X := hcontact
    unfold squareRootLowPrimeGoSecondContactSources
    refine Finset.mem_biUnion.mpr ⟨canonicalLargestPrimeFactor m, hqQ, ?_⟩
    rw [squareRootLowPrimeGoWallSquareResidualChildren_eq_smoothCofactorImage
      hqPrime]
    refine Finset.mem_image.mpr ⟨canonicalCofactor m, ?_, ?_⟩
    · exact mem_squareRootLowPrimeGoSmoothCofactors.mpr
        ⟨hcPos, hcB, hcsq, hrough⟩
    · rw [Nat.mul_comm]
      exact hfactor

/-! ## One globally signed mass in the endpoint -/

/-- **The endpoint square-residual mass is one signed Möbius sum.**  No owner
schedule, no per-scale decomposition, and no sum of separate estimates. -/
theorem squareRootLowPrimeLiteralWallSquareResidualMass_eq_neg_endpointPopulationMass
    (R K : ℕ) :
    squareRootLowPrimeLiteralWallSquareResidualMass R K =
      -∑ m ∈ endpointSecondContactPopulation K (squareRootEndpoint R), μ m := by
  have hprime : ∀ q ∈ squareRootLowPrimeWallOldPrimeSet K, q.Prime := by
    intro q hq
    exact (mem_squareRootLowPrimeWallOldPrimeSet.mp hq).1
  have h := squareRootLowPrimeGoSecondContactSourceMoebiusSum_eq_neg_residualTotal
    (Q := squareRootLowPrimeWallOldPrimeSet K) (X := squareRootEndpoint R) hprime
  rw [squareRootLowPrimeGoSecondContactSources_wallSchedule_eq_endpointPopulation]
    at h
  rw [squareRootLowPrimeLiteralWallSquareResidualMass_eq_goWallSquareResidualTotal]
  omega

/-- **The endpoint ledger with the single mass substituted.**  This is the
compiled #481 wall identity carrying one globally signed square-residual mass
instead of an owner-indexed sum. -/
theorem squareRootLowPrimeLiteralWallPartnerLedgerMass_eq_endpoint_add_populationMass
    {R K p : ℕ} (hR : 2 ≤ R) :
    squareRootLowPrimeLiteralWallPartnerLedgerMass R K p =
      (1 - frozenPrimeUniverseMass (primesUpTo K) (squareRootEndpoint R)) +
        (∑ m ∈ endpointSecondContactPopulation K (squareRootEndpoint R), μ m) -
        ∑ q ∈ squareRootLowPrimeWallOldPrimeSet K,
          frozenPrimeUniverseMass (primesUpTo (q - 1))
            (squareRootEndpoint R / p) := by
  rw [squareRootLowPrimeLiteralWallPartnerLedgerMass_eq_endpoint_sub_residual_sub_fixed
      hR,
    squareRootLowPrimeLiteralWallSquareResidualMass_eq_neg_endpointPopulationMass]
  ring

/-- The regrouping invariance of the flux register, read on the intrinsic
endpoint population: the owner-tagged and owner-free readings agree on every
finite selection of arithmetic states. -/
theorem endpointSecondContactPopulation_restrictedMass_eq
    (R K : ℕ) (N : Finset ℕ) :
    (∑ z ∈ (goRoughPrefixOccurrences (squareRootLowPrimeWallOldPrimeSet K)
        (squareRootEndpoint R)).filter
        (fun z => goRoughPrefixState z ∈ N), μ z.2) =
      ∑ m ∈ (endpointSecondContactPopulation K (squareRootEndpoint R)).filter
        (fun m => m ∈ N), -μ m := by
  have hprime : ∀ q ∈ squareRootLowPrimeWallOldPrimeSet K, q.Prime := by
    intro q hq
    exact (mem_squareRootLowPrimeWallOldPrimeSet.mp hq).1
  have h := goSecondContact_restrictedMass_eq hprime N
  rw [squareRootLowPrimeGoSecondContactSources_wallSchedule_eq_endpointPopulation]
    at h
  exact h

/-! ## The graded structure of the single object -/

/-- **The sign is the level parity.**  On the endpoint population the Möbius
weight is determined by the number of distinct primes, so the single global mass
is an alternating sum of level cardinalities. -/
theorem endpointSecondContactPopulation_moebius_eq_levelParity
    {K X m : ℕ} (hm : m ∈ endpointSecondContactPopulation K X) :
    μ m = (-1 : ℤ) ^ m.primeFactors.card :=
  moebius_eq_negOnePow_primeFactors_card
    (mem_endpointSecondContactPopulation.mp hm).2.1

/-- **Graded scale law.**  A source carrying `k` distinct primes lies at scale
`X^(k/(k+1))`.  Only levels of unbounded `k` reach the top scale. -/
theorem endpointSecondContactPopulation_pow_le
    {K X m : ℕ} (hm : m ∈ endpointSecondContactPopulation K X) :
    m ^ (m.primeFactors.card + 1) ≤ X ^ m.primeFactors.card := by
  rcases mem_endpointSecondContactPopulation.mp hm with
    ⟨⟨hm2, _hmX⟩, hsq, _hK, hcontact⟩
  have hm1 : 1 < m := by omega
  have hprod : ∏ p ∈ m.primeFactors, p = m :=
    Nat.prod_primeFactors_of_squarefree hsq
  have hbound : m ≤ canonicalLargestPrimeFactor m ^ m.primeFactors.card := by
    have hle : (∏ p ∈ m.primeFactors, p) ≤
        canonicalLargestPrimeFactor m ^ m.primeFactors.card := by
      apply Finset.prod_le_pow_card
      intro p hp
      exact primeFactor_le_canonicalLargestPrimeFactor hm1 hp
    rw [hprod] at hle
    exact hle
  have hmq : m * canonicalLargestPrimeFactor m ≤ X := by
    rw [Nat.mul_comm]
    exact hcontact
  calc
    m ^ (m.primeFactors.card + 1) = m ^ m.primeFactors.card * m := by ring
    _ ≤ m ^ m.primeFactors.card *
        canonicalLargestPrimeFactor m ^ m.primeFactors.card :=
      Nat.mul_le_mul (le_refl _) hbound
    _ = (m * canonicalLargestPrimeFactor m) ^ m.primeFactors.card := by
      rw [mul_pow]
    _ ≤ X ^ m.primeFactors.card := Nat.pow_le_pow_left hmq _

/-- **Level one is exactly the root-scale anchor.**  A source with a single
prime factor is that prime, and it satisfies `m^2 <= X`. -/
theorem endpointSecondContactPopulation_level_one
    {K X m : ℕ} (hm : m ∈ endpointSecondContactPopulation K X)
    (hlevel : m.primeFactors.card = 1) :
    m.Prime ∧ m * m ≤ X := by
  rcases mem_endpointSecondContactPopulation.mp hm with
    ⟨⟨hm2, _hmX⟩, hsq, _hK, hcontact⟩
  have hm1 : 1 < m := by omega
  have hmPrime : m.Prime := by
    rcases Finset.card_eq_one.mp hlevel with ⟨p, hp⟩
    have hprod : ∏ r ∈ m.primeFactors, r = m :=
      Nat.prod_primeFactors_of_squarefree hsq
    rw [hp, Finset.prod_singleton] at hprod
    have hpmem : p ∈ m.primeFactors := by
      rw [hp]
      exact Finset.mem_singleton_self p
    have hpPrime : p.Prime := (Nat.mem_primeFactors.mp hpmem).1
    rw [← hprod]
    exact hpPrime
  have hlpf : canonicalLargestPrimeFactor m = m :=
    (Nat.prime_dvd_prime_iff_eq (canonicalLargestPrimeFactor_prime hm1)
      hmPrime).mp (canonicalLargestPrimeFactor_dvd hm1)
  refine ⟨hmPrime, ?_⟩
  calc
    m * m = canonicalLargestPrimeFactor m * m := by rw [hlpf]
    _ ≤ X := hcontact

/-! ## One global estimate, taken once -/

/-- **Single global bound on the endpoint mass.**  The anchor-separated estimate
is applied once to the whole recombined population; no owner or source-scale
estimate is formed and none is summed. -/
theorem abs_squareRootLowPrimeLiteralWallSquareResidualMass_le_anchor_add_thirdScale
    (R K : ℕ) :
    |squareRootLowPrimeLiteralWallSquareResidualMass R K| ≤
      (Nat.sqrt (squareRootEndpoint R) : ℤ) +
        ((squareRootEndpoint R / 3 : ℕ) : ℤ) := by
  have hprime : ∀ q ∈ squareRootLowPrimeWallOldPrimeSet K, q.Prime := by
    intro q hq
    exact (mem_squareRootLowPrimeWallOldPrimeSet.mp hq).1
  rw [squareRootLowPrimeLiteralWallSquareResidualMass_eq_goWallSquareResidualTotal]
  exact abs_squareRootLowPrimeGoWallSquareResidualTotal_le_anchor_add_thirdScale
    hprime

end RHLean.Proof
