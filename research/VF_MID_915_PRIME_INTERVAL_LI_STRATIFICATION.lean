import Mathlib
import «research.VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION»
import «research.VF_MID_915_LATE_PREFIX_WEIGHTED_DYADIC»

/-!
# #915 actual prime / floor-Li stratification into arbitrary x/c bands

For X=(R+1)^2-1 a prime q>R and an odd cofactor c>=1 yield a
physical square-band site n=cq precisely when

  max(R,floor(R^2/c)) < q <= floor(X/c).

The prime-count comparison is EXACT. No short-interval PNT bound is
assumed. Original current VF charge is w_R-1 for c=1 (prime q), and
w_R for every odd c>=3 (composite cq, including squareful cofactor c).

The complete physical one-owner disjoint union will be independently
checked by finite actual-prime regression. This module formalizes the
ARBITRARY interval transport and the exact cofactor-weighted signed
remainder, not the unproved first-bad sign assertion.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis
open RHLean.Arithmetic RHLean.Proof
attribute [local instance] Classical.propDecidable

def vfMid915PrimeCofactorLower (R c : ℕ) : ℕ :=
  max R (R ^ 2 / c)

def vfMid915PrimeCofactorUpper (R c : ℕ) : ℕ :=
  ((R + 1) ^ 2 - 1) / c

/-! ## Exact physical sqrt-x geometry -/

/-- The actual prime q occurrences associated with each cofactor interval. -/
def vfMid915PhysicalPrimeCofactorFiber (R c : ℕ) : Finset ℕ :=
  (Finset.Ioc
    (vfMid915PrimeCofactorLower R c)
    (vfMid915PrimeCofactorUpper R c)).filter Nat.Prime

/-- No probabilistic heuristics: membership in a cofactor window is precisely
ACTUAL prime membership plus the original square-block physical inequalities. -/
theorem vfMid915PhysicalPrimeCofactorFiber_mem_iff
    {R c q : ℕ} (hc : 0 < c) :
    q ∈ vfMid915PhysicalPrimeCofactorFiber R c ↔
      q.Prime ∧ R < q ∧ R ^ 2 < c * q ∧
        c * q ≤ (R + 1) ^ 2 - 1 := by
  unfold vfMid915PhysicalPrimeCofactorFiber
  rw [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlow, hupp⟩, hqprime⟩
    have hbounds :
        R < q ∧ R ^ 2 / c < q := by
      exact (max_lt_iff.mp hlow)
    have hstart : R ^ 2 < c * q := by
      have h := (Nat.div_lt_iff_lt_mul hc).mp hbounds.2
      simpa [Nat.mul_comm] using h
    have hend : c * q ≤ (R + 1) ^ 2 - 1 := by
      have h := (Nat.le_div_iff_mul_le hc).mp hupp
      simpa [Nat.mul_comm] using h
    exact ⟨hqprime, hbounds.1, hstart, hend⟩
  · rintro ⟨hqprime, hroot, hstart, hend⟩
    refine ⟨⟨?_, ?_⟩, hqprime⟩
    · apply max_lt_iff.mpr
      constructor
      · exact hroot
      · apply (Nat.div_lt_iff_lt_mul hc).mpr
        simpa [Nat.mul_comm] using hstart
    · apply (Nat.le_div_iff_mul_le hc).mpr
      simpa [Nat.mul_comm] using hend

/-- The cofactor of a large-prime-factor site lies at or below R.
No new prime owner can be introduced by a cofactor above this root. -/
theorem vfMid915PhysicalPrimeCofactor_le_root
    {R c q : ℕ}
    (hq : R < q) (hsite : c * q ≤ (R + 1) ^ 2 - 1) :
    c ≤ R := by
  by_contra hnot
  have hc : R + 1 ≤ c := by omega
  have hq' : R + 1 ≤ q := by omega
  have hproduct := Nat.mul_le_mul hc hq'
  have hproduct' : (R + 1) ^ 2 ≤ c * q := by
    nlinarith [hproduct]
  have hpositive : 0 < (R + 1) ^ 2 := by positivity
  have hsmall : c * q < (R + 1) ^ 2 := by
    have hsub : (R + 1) ^ 2 - 1 < (R + 1) ^ 2 :=
      Nat.sub_lt hpositive (by norm_num)
    omega
  omega

/-- Two primes strictly above the root cannot have their product in the
current square clock. This is the geometric uniqueness restriction on
the REAL prime-factor carrier, not a density assertion. -/
theorem vfMid915TwoPostRootPrimes_product_exceeds_squareClock
    {R p q : ℕ} (hp : R < p) (hq : R < q) :
    (R + 1) ^ 2 ≤ p * q := by
  have hp' : R + 1 ≤ p := by omega
  have hq' : R + 1 ≤ q := by omega
  have hproduct := Nat.mul_le_mul hp' hq'
  nlinarith

def vfMid915ActualPrimeInterval (lo hi : ℕ) : ℤ :=
  (Nat.primeCounting hi : ℤ) - (Nat.primeCounting lo : ℤ)

def vfMid915ActualPrimeCofactorBand (R c : ℕ) : ℤ :=
  vfMid915ActualPrimeInterval
    (vfMid915PrimeCofactorLower R c)
    (vfMid915PrimeCofactorUpper R c)

def vfMid915FloorLiPrimeInterval (lo hi : ℕ) : ℤ :=
  vfMidFloorLiIntegerPotential hi - vfMidFloorLiIntegerPotential lo

def vfMid915FloorLiCofactorBand (R c : ℕ) : ℤ :=
  vfMid915FloorLiPrimeInterval
    (vfMid915PrimeCofactorLower R c)
    (vfMid915PrimeCofactorUpper R c)

/-- Actual-minus-floor-Li in ANY integer prime interval is exactly the
backlog difference at the same two endpoints. -/
theorem vfMid915ActualMinusFloorLi_interval_eq_backlog
    (lo hi : ℕ) :
    vfMid915ActualPrimeInterval lo hi -
      vfMid915FloorLiPrimeInterval lo hi =
    vfMidPrimeFloorLiIntegerBacklog hi -
      vfMidPrimeFloorLiIntegerBacklog lo := by
  unfold vfMid915ActualPrimeInterval
    vfMid915FloorLiPrimeInterval vfMidPrimeFloorLiIntegerBacklog
  ring

/-- Exact primitive signed event-mismatch packet on an arbitrary interval. -/
theorem vfMid915ActualMinusFloorLi_interval_eq_transport
    {lo hi : ℕ} (h : lo ≤ hi) :
    vfMid915ActualPrimeInterval lo hi -
      vfMid915FloorLiPrimeInterval lo hi =
    vfMidFloorLiSignedMismatchMass lo hi := by
  rw [vfMidFloorLiSignedMismatchMass_eq_backlog_increment h]
  exact vfMid915ActualMinusFloorLi_interval_eq_backlog lo hi

theorem vfMid915CofactorActualMinusFloorLi_eq_transport
    {R c : ℕ}
    (h : vfMid915PrimeCofactorLower R c ≤
      vfMid915PrimeCofactorUpper R c) :
    vfMid915ActualPrimeCofactorBand R c -
      vfMid915FloorLiCofactorBand R c =
    vfMidFloorLiSignedMismatchMass
      (vfMid915PrimeCofactorLower R c)
      (vfMid915PrimeCofactorUpper R c) := by
  exact vfMid915ActualMinusFloorLi_interval_eq_transport h

/-- Literal original current VF site weight, without Möbius reweighting. -/
def vfMid915CofactorPhysicalCharge (R c : ℕ) : ℝ :=
  if c = 1 then vfMidOddFractionalPrimeSeatWeight R - 1
  else vfMidOddFractionalPrimeSeatWeight R

def vfMid915StratifiedPhysicalActual (R : ℕ)
    (cofactors : Finset ℕ) : ℝ :=
  ∑ c ∈ cofactors,
    vfMid915CofactorPhysicalCharge R c *
      ((vfMid915ActualPrimeCofactorBand R c : ℤ) : ℝ)

def vfMid915StratifiedPhysicalFloorLi (R : ℕ)
    (cofactors : Finset ℕ) : ℝ :=
  ∑ c ∈ cofactors,
    vfMid915CofactorPhysicalCharge R c *
      ((vfMid915FloorLiCofactorBand R c : ℤ) : ℝ)

/-- All actual interval prime errors survive as signed literal boundaries. -/
def vfMid915StratifiedPhysicalMismatch (R : ℕ)
    (cofactors : Finset ℕ) : ℝ :=
  ∑ c ∈ cofactors,
    vfMid915CofactorPhysicalCharge R c *
      ((vfMidPrimeFloorLiIntegerBacklog
          (vfMid915PrimeCofactorUpper R c) -
        vfMidPrimeFloorLiIntegerBacklog
          (vfMid915PrimeCofactorLower R c) : ℤ) : ℝ)

/-- Exact signed cofactor-stratified reconciliation using genuine prime
counting and original site-dependent physical VF charges. -/
theorem vfMid915StratifiedPhysical_actual_eq_floorLi_add_mismatch
    (R : ℕ) (cofactors : Finset ℕ) :
    vfMid915StratifiedPhysicalActual R cofactors =
      vfMid915StratifiedPhysicalFloorLi R cofactors +
        vfMid915StratifiedPhysicalMismatch R cofactors := by
  unfold vfMid915StratifiedPhysicalActual
    vfMid915StratifiedPhysicalFloorLi
    vfMid915StratifiedPhysicalMismatch
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  have hband := vfMid915ActualMinusFloorLi_interval_eq_backlog
    (vfMid915PrimeCofactorLower R c)
    (vfMid915PrimeCofactorUpper R c)
  have hreal := congrArg (fun z : ℤ => (z : ℝ)) hband
  push_cast at hreal
  simp only [vfMid915ActualPrimeCofactorBand,
    vfMid915FloorLiCofactorBand]
  push_cast
  linear_combination (vfMid915CofactorPhysicalCharge R c) * hreal

/-- The sum of all genuine prime-cofactor window deviations is the
sum of their signed integer mismatch backlogs, without pretending the
short-interval errors are independent. -/
theorem vfMid915ActualBandSumMinusLi_eq_signedError
    (cofactors : Finset ℕ) (R : ℕ) :
    (∑ c ∈ cofactors,
      ((vfMid915ActualPrimeCofactorBand R c : ℤ) : ℝ)) -
    (∑ c ∈ cofactors,
      ((vfMid915FloorLiCofactorBand R c : ℤ) : ℝ)) =
    ∑ c ∈ cofactors,
      ((vfMidPrimeFloorLiIntegerBacklog
          (vfMid915PrimeCofactorUpper R c) -
        vfMidPrimeFloorLiIntegerBacklog
          (vfMid915PrimeCofactorLower R c) : ℤ) : ℝ) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  have hband := vfMid915ActualMinusFloorLi_interval_eq_backlog
    (vfMid915PrimeCofactorLower R c)
    (vfMid915PrimeCofactorUpper R c)
  simp only [vfMid915ActualPrimeCofactorBand,
    vfMid915FloorLiCofactorBand]
  exact_mod_cast hband


/-! ## Critical prime-square boundary exclusion -/

/-- A genuine q-prime >r multiplied by a cofactor <=r CANNOT be a square
exactly on the next endpoint. The deterministic Li staircase MAY jump at
this quotient endpoint; actual prime counting will not. -/
theorem vfMid915PrimeCofactorSquareEndpoint_excluded
    {r c q : ℕ}
    (hcr : c ≤ r) (hqr : r < q) (hqPrime : q.Prime) :
    c * q ≠ (r + 1) ^ 2 := by
  intro hsquare
  have hqdiv : q ∣ (r + 1) ^ 2 := by
    rw [← hsquare]
    exact dvd_mul_left q c
  have hqdivr : q ∣ r + 1 :=
    hqPrime.dvd_of_dvd_pow hqdiv
  have hqle : q ≤ r + 1 :=
    Nat.le_of_dvd (by omega : 0 < r + 1) hqdivr
  have hqeq : q = r + 1 := by omega
  subst q
  have hmul : c * (r + 1) ≤ r * (r + 1) :=
    Nat.mul_le_mul_right (r + 1) hcr
  nlinarith

/-- EXACT cofactor-first physical interval: for c<=r the prime count
across the closed quotient-square cutoffs equals the ACTUAL number of
sites c*q strictly BETWEEN consecutive squares, with genuine q>r.
No prime can land on the quotient-square endpoint, even though Li can. -/
theorem vfMid915PrimeCofactorSquareBand_iff_physical
    {r c q : ℕ} (hc : 0 < c) (hcr : c ≤ r) :
    (q.Prime ∧ r ^ 2 / c < q ∧ q ≤ (r + 1) ^ 2 / c) ↔
      (q.Prime ∧ r < q ∧ r ^ 2 < c * q ∧
        c * q < (r + 1) ^ 2) := by
  constructor
  · rintro ⟨hqPrime, hlow, hupp⟩
    have hstart : r ^ 2 < c * q := by
      have h := (Nat.div_lt_iff_lt_mul hc).mp hlow
      simpa [Nat.mul_comm] using h
    have hupper : c * q ≤ (r + 1) ^ 2 := by
      have h := (Nat.le_div_iff_mul_le hc).mp hupp
      simpa [Nat.mul_comm] using h
    have hroot : r < q := by
      by_contra hnot
      have hqle : q ≤ r := by omega
      have hmul : c * q ≤ r * r := Nat.mul_le_mul hcr hqle
      nlinarith
    have hnot := vfMid915PrimeCofactorSquareEndpoint_excluded
      hcr hroot hqPrime
    refine ⟨hqPrime, hroot, hstart, ?_⟩
    omega
  · rintro ⟨hqPrime, hroot, hstart, hupper⟩
    refine ⟨hqPrime, ?_, ?_⟩
    · apply (Nat.div_lt_iff_lt_mul hc).mpr
      simpa [Nat.mul_comm] using hstart
    · apply (Nat.le_div_iff_mul_le hc).mpr
      have hle : c * q ≤ (r + 1) ^ 2 := by omega
      simpa [Nat.mul_comm] using hle

/-! ## Cofactor-first historical Fubini and exact retained-weight Abel -/

/-- The quotient-square cutoff for one cofactor's ACTUAL prime counts.
Above its native cofactor threshold r>=c, the geometric root condition
q>r is automatic for all prime q between consecutive cutoffs. -/
def vfMid915PrimeCofactorSquareCutoff (r c : ℕ) : ℕ :=
  r ^ 2 / c

/-- The true integer prime-minus-Li backlog at cofactor-scaled square r²/c. -/
def vfMid915PrimeCofactorBacklog (r c : ℕ) : ℝ :=
  ((vfMidPrimeFloorLiIntegerBacklog
    (vfMid915PrimeCofactorSquareCutoff r c) : ℤ) : ℝ)

/-- Exact signed prime discrepancy on a cofactor's adjacent quotient-square
interval. This is the source's real event error, NOT an independent
probabilistic prime-density approximation. -/
theorem vfMid915PrimeCofactorBlock_actualMinusLi_eq_backlog
    (r c : ℕ) :
    vfMid915ActualPrimeInterval
        (vfMid915PrimeCofactorSquareCutoff r c)
        (vfMid915PrimeCofactorSquareCutoff (r + 1) c) -
      vfMid915FloorLiPrimeInterval
        (vfMid915PrimeCofactorSquareCutoff r c)
        (vfMid915PrimeCofactorSquareCutoff (r + 1) c) =
      vfMidPrimeFloorLiIntegerBacklog
        (vfMid915PrimeCofactorSquareCutoff (r + 1) c) -
      vfMidPrimeFloorLiIntegerBacklog
        (vfMid915PrimeCofactorSquareCutoff r c) := by
  exact vfMid915ActualMinusFloorLi_interval_eq_backlog _ _

/-- Exact retained-weight discrete Abel sum. The absence of a division
or sign bound makes this true for ANY actual sequence of prime events.
All completed intermediate integer events telescope before taking norms. -/
theorem vfMid915ExactWeightedAbel
    (w E : ℕ → ℝ) (A B : ℕ) (hAB : A ≤ B) :
    (∑ r ∈ Finset.Ico A B,
      w r * (E (r + 1) - E r)) =
      w B * E B - w A * E A +
        (∑ r ∈ Finset.Ico A B,
          (w r - w (r + 1)) * E (r + 1)) := by
  have hlocal (r : ℕ) :
      w r * (E (r + 1) - E r) =
        ((w (r + 1) * E (r + 1)) - (w r * E r)) +
          (w r - w (r + 1)) * E (r + 1) := by
    ring
  calc
    (∑ r ∈ Finset.Ico A B, w r * (E (r + 1) - E r)) =
        ∑ r ∈ Finset.Ico A B,
          ((w (r + 1) * E (r + 1)) - (w r * E r) +
            (w r - w (r + 1)) * E (r + 1)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact hlocal r
    _ = (∑ r ∈ Finset.Ico A B,
          ((w (r + 1) * E (r + 1)) - (w r * E r))) +
          (∑ r ∈ Finset.Ico A B,
            (w r - w (r + 1)) * E (r + 1)) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      have htelescope :
          (∑ r ∈ Finset.Ico A B,
            ((w (r + 1) * E (r + 1)) - (w r * E r))) =
            w B * E B - w A * E A :=
        Finset.sum_Ico_sub (fun r => w r * E r) hAB
      rw [htelescope]

/-- Historical starting square-root index for one original cofactor.
The c root threshold is imposed at the SAME time as the genuine
first-bad half-run anchor, not substituted retrospectively. -/
def vfMid915CofactorHistoryStart (A c : ℕ) : ℕ :=
  max A c

/-- Original VF scalar w_r is retained at every actual historical
integer site's NATIVE square block r; no use of w_B as a constant. -/
def vfMid915HistoricalCofactorTransportError (A B c : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico (vfMid915CofactorHistoryStart A c) B,
    vfMidOddFractionalPrimeSeatWeight r *
      (vfMid915PrimeCofactorBacklog (r + 1) c -
        vfMid915PrimeCofactorBacklog r c)

/-- The native historical weighted prime-interval Li error is EXACTLY a
small set of endpoint backlog charges plus a smooth coefficient-VARIATION
term. This is the cofactor-first multiscale boundary compression requested
for #915; no |historical z| denominator decompression occurs. -/
theorem vfMid915HistoricalCofactorTransportError_eq_endpoints_add_variation
    {A B c : ℕ} (hAB : vfMid915CofactorHistoryStart A c ≤ B) :
    vfMid915HistoricalCofactorTransportError A B c =
      vfMidOddFractionalPrimeSeatWeight B *
        vfMid915PrimeCofactorBacklog B c -
      vfMidOddFractionalPrimeSeatWeight (vfMid915CofactorHistoryStart A c) *
        vfMid915PrimeCofactorBacklog
          (vfMid915CofactorHistoryStart A c) c +
      (∑ r ∈ Finset.Ico (vfMid915CofactorHistoryStart A c) B,
        (vfMidOddFractionalPrimeSeatWeight r -
          vfMidOddFractionalPrimeSeatWeight (r + 1)) *
          vfMid915PrimeCofactorBacklog (r + 1) c) := by
  unfold vfMid915HistoricalCofactorTransportError
  exact vfMid915ExactWeightedAbel
    vfMidOddFractionalPrimeSeatWeight
    (fun r => vfMid915PrimeCofactorBacklog r c)
    (vfMid915CofactorHistoryStart A c) B hAB

end RHLean.Analysis
