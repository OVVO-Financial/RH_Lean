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
  nlinarith

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
  dsimp [vfMid915ActualPrimeCofactorBand,
    vfMid915FloorLiCofactorBand] at hband
  have hreal := congrArg (fun z : ℤ => (z : ℝ)) hband
  push_cast at hreal
  nlinarith

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
  dsimp [vfMid915ActualPrimeCofactorBand,
    vfMid915FloorLiCofactorBand] at hband
  exact_mod_cast hband

end RHLean.Analysis
