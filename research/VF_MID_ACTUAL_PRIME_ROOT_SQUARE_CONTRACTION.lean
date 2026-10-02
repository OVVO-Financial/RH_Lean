import Mathlib
import «research.VF_MID_ALIGNED_STEP_GRAPH»
import «research.PRIME_WHEEL_ROUGH_SEAT_SQRT_SPECIALIZATION»
import RHLean.Proof.PostRootPartnerLogAlignment

/-!
# Actual-prime root-to-square contraction attack

This file records the exact endpoint geometry needed to compare the continuous-Li
root-to-square contraction with the actual-prime square-endpoint chronology.

There are three points.

1. The repository endpoint `squareRootEndpoint R = R^2 - 1` and the literal
   square endpoint `R^2` have exactly the same actual-prime carrier above the
   root.  The missing endpoint is the composite square itself.

2. More strongly, for every prime `q > R`, the reciprocal child cutoff is
   unchanged:
   `floor((R^2-1)/q) = floor(R^2/q)`.
   Thus the off-by-one is not an analytic error and costs no part of the
   VF vertical alignment budget.

3. The chronological Euler-hazard normalization already present in the repo is
   strictly subunit on every finite list of genuine primes:
   `0 <= hazard < 1`.
   The unresolved direct-VF attack is therefore not endpoint geometry.  It is
   the exact bridge from the raw actual-prime transport (whose displayed
   coefficient is one) to the already-compiled hazard-normalized signed ledger,
   where each new boundary enters with `1/q` and previous memory is multiplied
   by `1 - 1/q`.

No RH-scale estimate is assumed or asserted here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Actual primes strictly above the root and through the literal square. -/
def vfMidActualRootSquarePrimeCarrier (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (R ^ 2)).filter Nat.Prime

/-- The same carrier in the repository's canonical pre-square convention. -/
def vfMidActualPreSquarePrimeCarrier (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter Nat.Prime

private theorem square_not_prime_of_two_le
    {R : ℕ} (hR : 2 ≤ R) :
    ¬ Nat.Prime (R ^ 2) := by
  intro hprime
  have hdiv : R ^ 2 ∣ R * R := by
    simp [pow_two]
  have hRdiv : R ^ 2 ∣ R :=
    (hprime.dvd_mul.mp hdiv).elim id id
  have hle : R ^ 2 ≤ R :=
    Nat.le_of_dvd (by omega : 0 < R) hRdiv
  nlinarith

/-- **The pre-square and square actual-prime carriers are exactly equal.**
The only integer added by moving the endpoint from `R^2-1` to `R^2` is
`R^2`, which is composite for `R >= 2`. -/
theorem vfMidActualPreSquarePrimeCarrier_eq_rootSquare
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidActualPreSquarePrimeCarrier R =
      vfMidActualRootSquarePrimeCarrier R := by
  ext q
  simp only [vfMidActualPreSquarePrimeCarrier,
    vfMidActualRootSquarePrimeCarrier, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hRq, hqX⟩, hqPrime⟩
    have hXle : squareRootEndpoint R ≤ R ^ 2 := by
      unfold squareRootEndpoint
      omega
    exact ⟨⟨hRq, hqX.trans hXle⟩, hqPrime⟩
  · rintro ⟨⟨hRq, hqSq⟩, hqPrime⟩
    have hqNe : q ≠ R ^ 2 := by
      intro hq
      subst q
      exact square_not_prime_of_two_le hR hqPrime
    have hqPre : q ≤ squareRootEndpoint R := by
      unfold squareRootEndpoint
      omega
    exact ⟨⟨hRq, hqPre⟩, hqPrime⟩

/-- A prime strictly above `R` cannot divide `R^2`. -/
theorem not_dvd_square_of_root_lt_prime
    {R q : ℕ} (hqPrime : q.Prime) (hRq : R < q) :
    ¬ q ∣ R ^ 2 := by
  intro hdiv
  have hdiv' : q ∣ R * R := by
    simpa [pow_two] using hdiv
  have hqR : q ∣ R :=
    (hqPrime.dvd_mul.mp hdiv').elim id id
  have hqLe : q ≤ R :=
    Nat.le_of_dvd (by omega : 0 < R) hqR
  omega

/-- **The reciprocal child is also endpoint-invariant.**
For an actual prime owner above the root, subtracting the final composite
square changes neither the owner set nor its quotient child. -/
theorem squareRootEndpoint_div_eq_square_div_of_root_lt_prime
    {R q : ℕ} (hqPrime : q.Prime) (hRq : R < q) :
    squareRootEndpoint R / q = R ^ 2 / q := by
  let k : ℕ := R ^ 2 / q
  have hqPos : 0 < q := hqPrime.pos
  have hupper0 : R ^ 2 < q * (k + 1) := by
    dsimp [k]
    exact (Nat.div_lt_iff_lt_mul hqPos).1 (Nat.lt_succ_self _)
  have hlower0 : q * k ≤ R ^ 2 := by
    dsimp [k]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (R ^ 2) q
  have hlowerNe : q * k ≠ R ^ 2 := by
    intro heq
    have hdvd : q ∣ R ^ 2 := by
      refine ⟨k, ?_⟩
      simpa [Nat.mul_comm] using heq.symm
    exact not_dvd_square_of_root_lt_prime hqPrime hRq hdvd
  have hlower : q * k ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hupper : squareRootEndpoint R < (k + 1) * q := by
    unfold squareRootEndpoint
    have hs : R ^ 2 - 1 < R ^ 2 := by
      have : 0 < R ^ 2 := by positivity
      omega
    calc
      R ^ 2 - 1 < R ^ 2 := hs
      _ < q * (k + 1) := hupper0
      _ = (k + 1) * q := by ring
  have hdiv : squareRootEndpoint R / q = k := by
    apply Nat.div_eq_of_lt_le
    · exact hupper
    · simpa [Nat.mul_comm] using hlower
  simpa [k] using hdiv

/-- Prime-list Euler products are strictly positive. -/
theorem canonicalRoughPrimeListEulerProduct_pos
    (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    0 < canonicalRoughPrimeListEulerProduct ps := by
  induction ps with
  | nil =>
      simp [canonicalRoughPrimeListEulerProduct]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have htail : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hpRpos : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast hp.pos
      have hpRone : (1 : ℝ) < (p : ℝ) := by
        exact_mod_cast hp.one_lt
      have hfrac : (1 : ℝ) / (p : ℝ) < 1 := by
        exact (div_lt_one hpRpos).2 hpRone
      have hfactor : 0 < canonicalRoughEulerFactor p := by
        unfold canonicalRoughEulerFactor
        linarith
      simp only [canonicalRoughPrimeListEulerProduct]
      exact mul_pos hfactor (ih htail)

/-- Prime-list Euler products are at most one. -/
theorem canonicalRoughPrimeListEulerProduct_le_one
    (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    canonicalRoughPrimeListEulerProduct ps ≤ 1 := by
  induction ps with
  | nil =>
      simp [canonicalRoughPrimeListEulerProduct]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have htail : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hfactor0 : 0 ≤ canonicalRoughEulerFactor p :=
        canonicalRoughEulerFactor_nonneg hp
      have hfactor1 : canonicalRoughEulerFactor p ≤ 1 :=
        canonicalRoughEulerFactor_le_one hp
      have htail0 : 0 ≤ canonicalRoughPrimeListEulerProduct ps :=
        (canonicalRoughPrimeListEulerProduct_pos ps htail).le
      have htail1 := ih htail
      simp only [canonicalRoughPrimeListEulerProduct]
      calc
        canonicalRoughEulerFactor p * canonicalRoughPrimeListEulerProduct ps
            ≤ 1 * canonicalRoughPrimeListEulerProduct ps :=
          mul_le_mul_of_nonneg_right hfactor1 htail0
        _ ≤ 1 := by simpa using htail1

/-- **Strict actual-prime Euler-hazard budget.**
Unlike the raw transport sum, the chronological hazard-normalized prime ledger
has a genuinely subunit total coefficient on every finite prime schedule. -/
theorem postRootEulerHazardMass_nonneg_lt_one_of_prime_list
    (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    0 ≤ postRootEulerHazardMass ps ∧
      postRootEulerHazardMass ps < 1 := by
  rw [postRootEulerHazardMass_eq_one_sub_eulerProduct]
  have hpos := canonicalRoughPrimeListEulerProduct_pos ps hprime
  have hle := canonicalRoughPrimeListEulerProduct_le_one ps hprime
  constructor <;> linarith

/-- Specialization: any chronological list drawn from the actual root-to-square
prime carrier inherits the strict Euler-hazard budget.  Completeness or ordering
of the list is irrelevant for this scalar estimate. -/
theorem vfMidActualRootSquarePrimeSchedule_hazard_nonneg_lt_one
    (R : ℕ) (ps : List ℕ)
    (hmem : ∀ p ∈ ps, p ∈ vfMidActualRootSquarePrimeCarrier R) :
    0 ≤ postRootEulerHazardMass ps ∧
      postRootEulerHazardMass ps < 1 := by
  apply postRootEulerHazardMass_nonneg_lt_one_of_prime_list
  intro p hp
  exact (Finset.mem_filter.mp (hmem p hp)).2

/-- The fixed VF alignment phase never changes square-block increments.  This is
restated here only to keep the endpoint conclusion adjacent to the actual-prime
carrier lemmas above. -/
theorem vfMidInitialAnchor_preserves_square_increment
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidAlignedMass vfMidInitialAnchor (R + 1) -
        vfMidAlignedMass vfMidInitialAnchor R =
      vfMidBandMass R := by
  rw [vfMidAlignedMass_succ vfMidInitialAnchor hR]
  ring

end RHLean.Proof
