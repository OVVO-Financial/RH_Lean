import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedExternalTerminalMassBridge
import RHLean.Proof.TerminalMertensReduction

/-!
# Canonical rough covariance: physical fresh-prime descent

`LowWheelCanonicalRepeatedExternalTerminalMassBridge` puts the centered rough
covariance numerator on an exact sequential Euler-prime carrier.  One legal
parent/child pair `c, c*p` contributes only the finite difference of the rough
prime-partner response.

This file opens that difference on the literal partner sets from
`TerminalMertensReduction`.  It separates two geometrically different events:

* **loss**: a prime partner present at `c` disappears after adjoining `p`;
* **birth**: a new partner appears only because the child `p*c` crosses the
  square-root wall together with a still larger fresh prime.

The birth geometry is automatically lower-scale: every birth forces
`p*c < R`.  Once `R <= p*c`, births vanish identically.  In particular a fresh
prime already above the root gives its child zero rough response altogether.

The second half records the zero mode that prime pairing cannot destroy.  Every
fresh-prime parent/child pair has zero Mobius mass, so sequential prime descent
preserves the exact parity sum of the active carrier.  Combining this invariant
with response-only centering gives a sharper normal form for the covariance:

```text
card * covariance
  = cumulative signed prime boundaries
    + final raw rough correlation
    - original parity * global response mean.
```

No term is normed separately and no independence or mean-zero hypothesis is
introduced.  The remaining quantitative problem is therefore explicit: control
the signed loss/birth boundary accumulation and the raw response on the final
survivor carrier.  The only genuinely new positive partner capacity is born at
strictly smaller root scale.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughFreshPrimeDifference

attribute [local instance] Classical.propDecidable

namespace CanonicalRoughPrimeAdditionDescent

/-- **Physical loss/birth form of one centered covariance pair.**  The response
mean cancels inside the opposite-sign fresh-prime pair, leaving exactly the
literal partner loss minus the literal root-crossing birth population. -/
theorem squareRootCanonicalRoughResponseCenteredSummand_add_mul_freshPrime_eq_loss_sub_birth
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughResponseCenteredSummand R c +
        squareRootCanonicalRoughResponseCenteredSummand R (c * p) =
      canonicalMoebiusWeight c *
        (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) := by
  unfold squareRootCanonicalRoughResponseCenteredSummand
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R c hR,
    squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R (c * p) hR,
    canonicalMoebiusWeight_mul_prime_eq_neg_of_rough hc hp hfresh]
  have hdiff :=
    squareRootCanonicalRoughPrimePartnerCount_sub_freshChild_eq_loss_sub_birth
      (R := R) (c := c) (p := p)
  have hdiff' :
      squareRootCanonicalRoughPrimePartnerCount R c -
          squareRootCanonicalRoughPrimePartnerCount R (c * p) =
        ((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ) := by
    simpa [Nat.mul_comm] using hdiff
  calc
    canonicalMoebiusWeight c *
          (squareRootCanonicalRoughPrimePartnerCount R c -
            squareRootCanonicalRoughResponseMean R) +
        -canonicalMoebiusWeight c *
          (squareRootCanonicalRoughPrimePartnerCount R (c * p) -
            squareRootCanonicalRoughResponseMean R) =
      canonicalMoebiusWeight c *
        (squareRootCanonicalRoughPrimePartnerCount R c -
          squareRootCanonicalRoughPrimePartnerCount R (c * p)) := by ring
    _ = canonicalMoebiusWeight c *
        (((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ)) := by
      rw [hdiff']

/-- **Every genuinely new partner is born below the root.**  If `q` belongs to
the fresh-prime birth boundary, then the fresh child cofactor `p*c` is still
strictly smaller than `R`.  Thus all positive capacity creation in the
prime-addition descent is attached to a strictly lower root scale. -/
theorem squareRootCanonicalRoughFreshBirthBoundary_child_lt_root
    {R c p q : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p)
    (hq : q ∈ squareRootCanonicalRoughFreshBirthBoundary R c p) :
    p * c < R := by
  have hdata :=
    (mem_squareRootCanonicalRoughFreshBirthBoundary_iff
      hR hc hp hfresh).1 hq
  rcases hdata with ⟨_hqPrime, hpq, hcqR, _hchildRoot, _hchildUpper⟩
  have hpc_lt_qc : p * c < q * c :=
    Nat.mul_lt_mul_of_pos_right hpq hc
  have hpc_lt_cq : p * c < c * q := by
    simpa [Nat.mul_comm] using hpc_lt_qc
  exact hpc_lt_cq.trans hcqR

/-- Once the fresh child has reached the root, the centered pair has only a
loss boundary.  There is no positive birth term left to rebuild rough capacity. -/
theorem squareRootCanonicalRoughResponseCenteredSummand_add_mul_freshPrime_eq_loss_of_root_reached
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p)
    (hroot : R ≤ p * c) :
    squareRootCanonicalRoughResponseCenteredSummand R c +
        squareRootCanonicalRoughResponseCenteredSummand R (c * p) =
      canonicalMoebiusWeight c *
        ((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) := by
  rw [squareRootCanonicalRoughResponseCenteredSummand_add_mul_freshPrime_eq_loss_sub_birth
    hR hc hp hfresh]
  rw [squareRootCanonicalRoughFreshBirthBoundary_eq_empty_of_root_reached
    hR hc hp hfresh hroot]
  simp

/-- A fresh prime already above the square root gives its child no canonical
rough-prime partner at all.  Any further fresh partner would be still larger
than `p`, forcing the product past `R^2 - 1`. -/
theorem squareRootCanonicalRoughPrimePartnerSet_mul_freshPrime_eq_empty_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    squareRootCanonicalRoughPrimePartnerSet R (c * p) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hcp : 0 < c * p := Nat.mul_pos hc hp.pos
  have hdata :=
    (mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hcp).1 hq
  have hlpf := canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hp hfresh
  rw [hlpf] at hdata
  rcases hdata with ⟨_hqPrime, hpq, _hroot, hupper⟩
  have hRq : R ≤ q :=
    hRp.le.trans hpq.le
  have hRR_le_pq : R * R ≤ p * q :=
    Nat.mul_le_mul hRp.le hRq
  have hc1 : 1 ≤ c := hc
  have hp_le_cp : p ≤ c * p := by
    simpa using Nat.mul_le_mul_right p hc1
  have hpq_le_cpq : p * q ≤ (c * p) * q :=
    Nat.mul_le_mul_right q hp_le_cp
  have hXltRR : squareRootEndpoint R < R * R := by
    unfold squareRootEndpoint
    rw [pow_two]
    have hRRpos : 0 < R * R := Nat.mul_pos (by omega) (by omega)
    omega
  have hXlt : squareRootEndpoint R < (c * p) * q :=
    hXltRR.trans_le (hRR_le_pq.trans hpq_le_cpq)
  exact (Nat.not_lt_of_ge hupper) hXlt

/-- The corresponding collapsed rough response of a post-root fresh child is
zero. -/
theorem squareRootCanonicalRoughPrimePartnerCount_mul_freshPrime_eq_zero_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    squareRootCanonicalRoughPrimePartnerCount R (c * p) = 0 := by
  rw [squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card,
    squareRootCanonicalRoughPrimePartnerSet_mul_freshPrime_eq_empty_of_rootPrime
      hR hc hp hfresh hRp]
  simp

/-- Hence a post-root fresh-prime pair contributes exactly the parent's raw
rough correlation.  The child response and the global response mean cancel
completely inside the pair. -/
theorem squareRootCanonicalRoughResponseCenteredSummand_add_mul_freshPrime_eq_parent_raw_of_rootPrime
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) (hRp : R < p) :
    squareRootCanonicalRoughResponseCenteredSummand R c +
        squareRootCanonicalRoughResponseCenteredSummand R (c * p) =
      canonicalMoebiusWeight c *
        squareRootCanonicalRoughCofactorResponse R c := by
  unfold squareRootCanonicalRoughResponseCenteredSummand
  rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R c hR,
    squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R (c * p) hR,
    squareRootCanonicalRoughPrimePartnerCount_mul_freshPrime_eq_zero_of_rootPrime
      hR hc hp hfresh hRp,
    canonicalMoebiusWeight_mul_prime_eq_neg_of_rough hc hp hfresh]
  ring

/-! ## The parity zero mode is invariant under prime descent -/

/-- One complete fresh-prime paired population has zero canonical Mobius mass. -/
theorem sum_squareRootCanonicalRoughFreshPrimePairedOn_moebiusWeight_eq_zero
    {p : ℕ} (U : Finset ℕ) (hp : p.Prime) :
    (∑ n ∈ squareRootCanonicalRoughFreshPrimePairedOn p U,
        canonicalMoebiusWeight n) = 0 := by
  unfold squareRootCanonicalRoughFreshPrimePairedOn
  rw [Finset.sum_union
    (squareRootCanonicalRoughFreshPrimeParentsOn_disjoint_childrenOn U hp)]
  unfold squareRootCanonicalRoughFreshPrimeChildrenOn
  rw [Finset.sum_image]
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro c hcParent
    rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
      ⟨_hcU, hcpos, hcrough, _hcchild⟩
    rw [canonicalMoebiusWeight_mul_prime_eq_neg_of_rough hcpos hp hcrough]
    ring
  · intro a _ha b _hb hab
    exact Nat.mul_right_cancel hp.pos hab

/-- Removing one fresh-prime paired population preserves the exact Mobius parity
sum on the active carrier. -/
theorem sum_squareRootCanonicalRoughMoebiusWeight_eq_freshPrimeSurvivors
    {p : ℕ} (U : Finset ℕ) (hp : p.Prime) :
    (∑ n ∈ U, canonicalMoebiusWeight n) =
      ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
        canonicalMoebiusWeight n := by
  have hsub := squareRootCanonicalRoughFreshPrimePairedOn_subset p U
  have hsplit :
      (∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
          canonicalMoebiusWeight n) +
        (∑ n ∈ squareRootCanonicalRoughFreshPrimePairedOn p U,
          canonicalMoebiusWeight n) =
        ∑ n ∈ U, canonicalMoebiusWeight n := by
    simpa [squareRootCanonicalRoughFreshPrimeSurvivorsOn] using
      (Finset.sum_sdiff hsub (f := canonicalMoebiusWeight))
  rw [sum_squareRootCanonicalRoughFreshPrimePairedOn_moebiusWeight_eq_zero U hp]
    at hsplit
  simpa using hsplit.symm

/-- **Sequential parity invariant.**  No chronological sequence of genuine
fresh-prime pairing steps can change the total canonical Mobius mass of the
active carrier. -/
theorem sum_squareRootCanonicalRoughMoebiusWeight_eq_primeDescentSurvivors
    (ps : List ℕ) (U : Finset ℕ) (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ n ∈ U, canonicalMoebiusWeight n) =
      ∑ n ∈ squareRootCanonicalRoughPrimeDescentSurvivors ps U,
        canonicalMoebiusWeight n := by
  induction ps generalizing U with
  | nil =>
      simp [squareRootCanonicalRoughPrimeDescentSurvivors]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hps : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      calc
        (∑ n ∈ U, canonicalMoebiusWeight n) =
            ∑ n ∈ squareRootCanonicalRoughFreshPrimeSurvivorsOn p U,
              canonicalMoebiusWeight n :=
          sum_squareRootCanonicalRoughMoebiusWeight_eq_freshPrimeSurvivors U hp
        _ = ∑ n ∈ squareRootCanonicalRoughPrimeDescentSurvivors ps
              (squareRootCanonicalRoughFreshPrimeSurvivorsOn p U),
              canonicalMoebiusWeight n :=
          ih (squareRootCanonicalRoughFreshPrimeSurvivorsOn p U) hps
        _ = ∑ n ∈ squareRootCanonicalRoughPrimeDescentSurvivors (p :: ps) U,
              canonicalMoebiusWeight n := by rfl

/-- On any finite carrier, response-only centering is raw rough correlation
minus the carrier's exact Mobius parity times the global response mean. -/
theorem sum_squareRootCanonicalRoughResponseCentered_eq_raw_sub_parity_mul_mean
    (R : ℕ) (U : Finset ℕ) :
    (∑ n ∈ U, squareRootCanonicalRoughResponseCenteredSummand R n) =
      (∑ n ∈ U,
        canonicalMoebiusWeight n * squareRootCanonicalRoughCofactorResponse R n) -
      (∑ n ∈ U, canonicalMoebiusWeight n) *
        squareRootCanonicalRoughResponseMean R := by
  unfold squareRootCanonicalRoughResponseCenteredSummand
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]

/-- After sequential prime descent, the survivor centering term still contains
exactly the *original* carrier parity.  Prime pairing can move that zero mode but
cannot make it disappear. -/
theorem sum_primeDescentSurvivorResponseCentered_eq_raw_sub_originalParity_mul_mean
    (R : ℕ) (ps : List ℕ) (U : Finset ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ n ∈ squareRootCanonicalRoughPrimeDescentSurvivors ps U,
        squareRootCanonicalRoughResponseCenteredSummand R n) =
      (∑ n ∈ squareRootCanonicalRoughPrimeDescentSurvivors ps U,
        canonicalMoebiusWeight n * squareRootCanonicalRoughCofactorResponse R n) -
      (∑ n ∈ U, canonicalMoebiusWeight n) *
        squareRootCanonicalRoughResponseMean R := by
  rw [sum_squareRootCanonicalRoughResponseCentered_eq_raw_sub_parity_mul_mean]
  rw [← sum_squareRootCanonicalRoughMoebiusWeight_eq_primeDescentSurvivors
    ps U hprime]

/-- **Sharpened sequential covariance descent.**  The centered covariance
numerator is cumulative signed prime-boundary charge plus the raw rough
correlation on the final survivors, minus the invariant original parity zero
mode.  This is the exact quantity a record-descent estimate must control. -/
theorem sum_squareRootCanonicalRoughResponseCentered_eq_primeDescent_rawSurvivors
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ) (U : Finset ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ n ∈ U, squareRootCanonicalRoughResponseCenteredSummand R n) =
      squareRootCanonicalRoughPrimeDescentBoundaryMass R ps U +
        (∑ n ∈ squareRootCanonicalRoughPrimeDescentSurvivors ps U,
          canonicalMoebiusWeight n * squareRootCanonicalRoughCofactorResponse R n) -
        (∑ n ∈ U, canonicalMoebiusWeight n) *
          squareRootCanonicalRoughResponseMean R := by
  rw [sum_squareRootCanonicalRoughResponseCentered_eq_primeDescent
    R hR ps U hprime]
  rw [sum_primeDescentSurvivorResponseCentered_eq_raw_sub_originalParity_mul_mean
    R ps U hprime]
  ring

/-- **Physical canonical covariance normal form after prime descent.**  On the
actual cofactor carrier, the invariant parity is the repository's canonical
rough parity sum. -/
theorem squareRootCanonicalRoughCovariance_primeAdditionDescent_rawSurvivors
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (squareRootCanonicalRoughCofactorCard R : ℂ) *
        squareRootCanonicalRoughCovariance R =
      squareRootCanonicalRoughPrimeDescentBoundaryMass R ps
          (squareRootCanonicalRoughCofactorCarrier R) +
        (∑ n ∈ squareRootCanonicalRoughPrimeDescentSurvivors ps
            (squareRootCanonicalRoughCofactorCarrier R),
          canonicalMoebiusWeight n * squareRootCanonicalRoughCofactorResponse R n) -
        squareRootCanonicalRoughParitySum R *
          squareRootCanonicalRoughResponseMean R := by
  rw [squareRootCanonicalRoughCofactorCard_mul_covariance_eq_sum_responseCentered
    R hR]
  unfold squareRootCanonicalRoughCofactorCarrier
  rw [sum_squareRootCanonicalRoughResponseCentered_eq_primeDescent_rawSurvivors
    R hR ps (Finset.Icc 1 (squareRootEndpoint R)) hprime]
  rfl

end CanonicalRoughPrimeAdditionDescent

end RHLean.Proof