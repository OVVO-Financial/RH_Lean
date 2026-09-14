import RHLean.Proof.PostRootPartnerEulerMemory
import RHLean.Proof.SignedTransportAmplificationAudit

/-!
# The reciprocal Stokes step need not decrease physical energy

The signed Stokes identity is exact, but its reciprocal after-state is not the
raw state used by the next chronological step.  This module records a finite
obstruction on the actual physical state, rather than on an arbitrary vector.

At `R = 56`, the first descending prime is `3121`.  The current correlation is
`-8`, its raw boundary charge is `429`, and the reciprocal Euler next state is
`-25397 / 3121`.  Its squared norm is strictly greater than `64`.

The general first-step calculation also exposes the large diagonal: whenever
`X_R < 2*p` and `R < p <= X_R`, the only parent is `1`, and its boundary is the
entire prime count in `[R, X_R]`.

These results refute automatic stepwise energy dissipation.  They do not refute
the signed LOW-A estimate and do not provide its missing uniform constants.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Beyond half the endpoint, the initial physical parent carrier is `{1}`. -/
theorem initialFreshPrimeParents_eq_singleton_of_half_endpoint_lt
    {R p : ℕ} (hp : p.Prime) (hpX : p ≤ squareRootEndpoint R)
    (hhalf : squareRootEndpoint R < 2 * p) :
    squareRootCanonicalRoughFreshPrimeParentsOn p
        (Finset.Icc 1 (squareRootEndpoint R)) = {1} := by
  ext c
  rw [mem_squareRootCanonicalRoughFreshPrimeParentsOn,
    Finset.mem_singleton]
  constructor
  · rintro ⟨_hc, hcpos, _hfresh, hcp⟩
    have hcpUpper := (Finset.mem_Icc.mp hcp).2
    have hcsmall : c < 2 := by
      by_contra hnot
      have hc2 : 2 ≤ c := by omega
      have hmul := Nat.mul_le_mul_right p hc2
      omega
    omega
  · rintro rfl
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, by omega, ?_, ?_⟩
    · exact hp.one_lt.le.trans hpX
    · simpa [canonicalLargestPrimeFactor] using hp.one_lt
    · simpa using (Finset.mem_Icc.mpr ⟨hp.one_lt.le, hpX⟩ :
        p ∈ Finset.Icc 1 (squareRootEndpoint R))

/-- The unit cofactor sees exactly the primes in the physical endpoint interval. -/
theorem roughPrimePartnerSet_one_eq_primeInterval
    {R : ℕ} (hR : 2 ≤ R) :
    squareRootCanonicalRoughPrimePartnerSet R 1 =
      (Finset.Icc R (squareRootEndpoint R)).filter Nat.Prime := by
  ext q
  rw [mem_squareRootCanonicalRoughPrimePartnerSet_iff hR (by omega),
    Finset.mem_filter, Finset.mem_Icc]
  simp only [canonicalLargestPrimeFactor, lt_self_iff_false, one_mul]
  constructor
  · rintro ⟨hq, _hrough, hlow, hhigh⟩
    exact ⟨⟨hlow, hhigh⟩, hq⟩
  · rintro ⟨⟨hlow, hhigh⟩, hq⟩
    exact ⟨hq, hq.one_lt, hlow, hhigh⟩

/-- A first post-root step beyond half the endpoint carries the whole interval
prime count in one signed Stokes boundary charge. -/
theorem initialRawBoundary_eq_primeIntervalCard_of_half_endpoint_lt
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hRp : R < p) (hpX : p ≤ squareRootEndpoint R)
    (hhalf : squareRootEndpoint R < 2 * p) :
    squareRootCanonicalRoughAdaptiveRawBoundaryMass R p
        (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ)) =
      (((Finset.Icc R (squareRootEndpoint R)).filter Nat.Prime).card : ℂ) := by
  have hparent := initialFreshPrimeParents_eq_singleton_of_half_endpoint_lt
    hp hpX hhalf
  have hfresh : canonicalLargestPrimeFactor 1 < p := by
    simpa [canonicalLargestPrimeFactor] using hp.one_lt
  have hpair := squareRootCanonicalRoughRawCorrelationSummand_add_mul_freshPrime
    hR (c := 1) (by omega) hp hfresh
  have hchild :=
    squareRootCanonicalRoughPrimePartnerCount_mul_freshPrime_eq_zero_of_rootPrime
      hR (c := 1) (by omega) hp hfresh hRp
  unfold squareRootCanonicalRoughAdaptiveRawBoundaryMass
  rw [hparent, Finset.sum_singleton, one_mul, ← hpair]
  simp only [squareRootCanonicalRoughRawCorrelationSummand,
    squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R 1 hR,
    squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R (1 * p) hR,
    hchild, mul_zero, add_zero]
  rw [squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card,
    roughPrimePartnerSet_one_eq_primeInterval hR]
  simp [canonicalMoebiusWeight]

/-- The literal reciprocal Euler after-state for the initial unit raw field. -/
def canonicalRoughInitialReciprocalEulerNext (R p : ℕ) : ℂ :=
  let U := Finset.Icc 1 (squareRootEndpoint R)
  squareRootCanonicalRoughAdaptiveWeightedMass R
    (squareRootCanonicalRoughAdaptiveNextCarrier p U)
    (squareRootCanonicalRoughAdaptiveNextCoefficient p U (fun n => (n : ℂ)))

private theorem initialPrefix_56_3121_complete :
    SquareRootCanonicalRoughCompleteDescendingPrefix 56 3121 [] := by
  refine ⟨by simp, ?_⟩
  intro q hq hlarge hupper
  have hnone : ∀ q ∈ Finset.Icc 3122 3135, ¬q.Prime := by native_decide
  have hmem : q ∈ Finset.Icc 3122 3135 := by
    norm_num [squareRootEndpoint] at hupper
    exact Finset.mem_Icc.mpr ⟨by omega, hupper⟩
  exact (hnone q hmem hq).elim

/-- Exact finite physical endpoint used by the energy regression. -/
theorem canonicalRoughCorrelation_56_eq_neg_eight :
    squareRootCanonicalRoughCorrelation 56 = -8 := by
  have hsmall : mertensSummatoryInt 55 = -2 := by native_decide
  have hlarge : mertensSummatoryInt 3135 = 6 := by native_decide
  rw [squareRootCanonicalRoughCorrelation_eq_mertens_pred_sub_endpoint 56 (by omega)]
  change mertensSummatory 55 - mertensSummatory 3135 = (-8 : ℂ)
  rw [← mertensSummatoryInt_cast 55, ← mertensSummatoryInt_cast 3135,
    hsmall, hlarge]
  norm_num

/-- The first boundary is a positive prime count, despite the negative parent. -/
theorem initialRawBoundary_56_3121_eq_429 :
    squareRootCanonicalRoughAdaptiveRawBoundaryMass 56 3121
        (Finset.Icc 1 (squareRootEndpoint 56)) (fun _ => (1 : ℂ)) = 429 := by
  have hp : Nat.Prime 3121 := by norm_num
  rw [initialRawBoundary_eq_primeIntervalCard_of_half_endpoint_lt (R := 56)
    (by omega) hp (by omega) (by norm_num [squareRootEndpoint])
    (by norm_num [squareRootEndpoint])]
  have hcard : ((Finset.Icc 56 3135).filter Nat.Prime).card = 429 := by
    native_decide
  norm_num [squareRootEndpoint, hcard]

/-- The actual first reciprocal after-state is farther from zero. -/
theorem canonicalRoughInitialReciprocalEulerNext_56_3121 :
    canonicalRoughInitialReciprocalEulerNext 56 3121 =
      -(25397 : ℂ) / 3121 := by
  have h := evolvedRawBoundary_eq_scaledReciprocalDrop_of_completeDescendingPrefix
    56 (p := 3121) [] (by omega) (by norm_num) initialPrefix_56_3121_complete
  simp only [squareRootCanonicalRoughAdaptiveCarrier,
    squareRootCanonicalRoughAdaptiveRawCoefficient, mul_one] at h
  rw [initialRawBoundary_56_3121_eq_429] at h
  have hmass : squareRootCanonicalRoughAdaptiveRawWeightedMass 56
      (Finset.Icc 1 (squareRootEndpoint 56)) (fun _ => (1 : ℂ)) =
        squareRootCanonicalRoughCorrelation 56 := by
    simp [squareRootCanonicalRoughAdaptiveRawWeightedMass,
      squareRootCanonicalRoughRawCorrelationSummand,
      squareRootCanonicalRoughCorrelation]
  rw [hmass, canonicalRoughCorrelation_56_eq_neg_eight] at h
  change (429 : ℂ) = 3121 *
    (-8 - canonicalRoughInitialReciprocalEulerNext 56 3121) at h
  linear_combination (1 / (3121 : ℂ)) * h

/-- **Physical energy-growth counterexample.**  A fresh-prime Stokes drop does
not automatically give a nonincreasing quadratic potential, even at the first
step of a complete descending chronology. -/
theorem canonicalRoughInitialReciprocalEulerNext_energy_increases :
    ‖squareRootCanonicalRoughCorrelation 56‖ ^ 2 <
      ‖canonicalRoughInitialReciprocalEulerNext 56 3121‖ ^ 2 := by
  rw [canonicalRoughCorrelation_56_eq_neg_eight,
    canonicalRoughInitialReciprocalEulerNext_56_3121]
  norm_num [norm_div]

end RHLean.Proof
