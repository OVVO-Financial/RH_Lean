import Mathlib
import RHLean.Proof.SurvivorZeroMode
import RHLean.Analysis.GrowingParentPhaseUniformity

/-!
# Exact prime and composite accounting inside the lifetime survivor

The absorbed lifetime mass is not the population of ordinary composites.
The complete survivor still contains both the `c = 1` prime fibre and all
`c >= 2` composite fibres. This file identifies the prime fibre with an exact
prime-count difference, retaining the strict moving-height cutoff, and gives
small witnesses showing that prime/composite and alive/dead are different
partitions.

No prime-distribution estimate or survivor power saving is assumed here.
-/

set_option autoImplicit false

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open CanonicalGapAncestryBridge
open RHLean.Analysis

/-- The integer cutoff of the pure-prime survivor fibre. -/
def survivorPrimeCutoff (Λ : ℝ) (t : ℕ) : ℕ :=
  ⌊Real.sqrt (2 * Λ * (t : ℝ) + 1)⌋₊

/-- At cofactor one, canonical source admissibility is exactly primality. -/
theorem canonicalSourceData_one_iff (q : ℕ) :
    CanonicalSourceData q 1 ↔ q.Prime := by
  constructor
  · exact fun h => h.1
  · intro hq
    refine ⟨hq, by omega, squarefree_one, by simp, ?_⟩
    intro p hp hpd
    exact (hp.not_dvd_one hpd).elim

/-- The prime fibre retains the exact strict moving-height condition. -/
theorem isSurvivorZeroModePair_one_iff (Λ : ℝ) (t q : ℕ) :
    IsSurvivorZeroModePair Λ t 1 q ↔
      q.Prime ∧ q ≤ squarePrefixEndpoint t ∧
        2 * Λ * (t : ℝ) < (q : ℝ) ^ 2 - 1 := by
  constructor
  · rintro ⟨hdata, hqX, hheight⟩
    have hq := (canonicalSourceData_one_iff q).1 hdata
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
    have hnonneg : 0 ≤ (q : ℝ) ^ 2 - 1 := by nlinarith
    refine ⟨hq, by simpa using hqX, ?_⟩
    simpa [abs_of_nonneg hnonneg] using hheight
  · rintro ⟨hq, hqX, hheight⟩
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
    have hnonneg : 0 ≤ (q : ℝ) ^ 2 - 1 := by nlinarith
    refine ⟨(canonicalSourceData_one_iff q).2 hq, by simpa using hqX, ?_⟩
    simpa [abs_of_nonneg hnonneg] using hheight

/-- The floor-square-root cutoff is bracketed by two consecutive squares. -/
theorem survivorPrimeCutoff_bounds {Λ : ℝ} (hΛ : 0 ≤ Λ) (t : ℕ) :
    (survivorPrimeCutoff Λ t : ℝ) ^ 2 ≤ 2 * Λ * (t : ℝ) + 1 ∧
      2 * Λ * (t : ℝ) + 1 < ((survivorPrimeCutoff Λ t : ℝ) + 1) ^ 2 := by
  have harg : 0 ≤ 2 * Λ * (t : ℝ) + 1 := by positivity
  have hs0 := Real.sqrt_nonneg (2 * Λ * (t : ℝ) + 1)
  have hs2 := Real.sq_sqrt harg
  have hlo := Nat.floor_le hs0
  have hhi := Nat.lt_floor_add_one (Real.sqrt (2 * Λ * (t : ℝ) + 1))
  change (survivorPrimeCutoff Λ t : ℝ) ≤
    Real.sqrt (2 * Λ * (t : ℝ) + 1) at hlo
  change Real.sqrt (2 * Λ * (t : ℝ) + 1) <
    (survivorPrimeCutoff Λ t : ℝ) + 1 at hhi
  have hsqlo := (sq_le_sq₀ (Nat.cast_nonneg _) hs0).mpr hlo
  have hsqhi := (sq_lt_sq₀ hs0 (by positivity)).mpr hhi
  constructor <;> nlinarith

/-- A square-bracket cutoff converts the strict prime height gate exactly. -/
theorem survivorPrimeHeight_iff_cutoff
    {Λ : ℝ} {t q k : ℕ}
    (hlo : (k : ℝ) ^ 2 ≤ 2 * Λ * (t : ℝ) + 1)
    (hhi : 2 * Λ * (t : ℝ) + 1 < ((k : ℝ) + 1) ^ 2) :
    2 * Λ * (t : ℝ) < (q : ℝ) ^ 2 - 1 ↔ k < q := by
  constructor
  · intro hheight
    by_contra hnot
    have hqk : (q : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (show q ≤ k by omega)
    have hsq := (sq_le_sq₀ (Nat.cast_nonneg q) (Nat.cast_nonneg k)).mpr hqk
    nlinarith
  · intro hkq
    have hnext : (k : ℝ) + 1 ≤ (q : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hkq)
    have hsq := (sq_le_sq₀ (by positivity) (Nat.cast_nonneg q)).mpr hnext
    nlinarith

/-- Exact cofactor-one source predicate with an integer cutoff. -/
theorem isSurvivorZeroModePair_one_iff_cutoff
    {Λ : ℝ} {t q k : ℕ}
    (hlo : (k : ℝ) ^ 2 ≤ 2 * Λ * (t : ℝ) + 1)
    (hhi : 2 * Λ * (t : ℝ) + 1 < ((k : ℝ) + 1) ^ 2) :
    IsSurvivorZeroModePair Λ t 1 q ↔
      q.Prime ∧ q ≤ squarePrefixEndpoint t ∧ k < q := by
  rw [isSurvivorZeroModePair_one_iff,
    survivorPrimeHeight_iff_cutoff hlo hhi]

/-- The prime fibre is exactly the larger prime prefix minus the cutoff prefix. -/
theorem survivorZeroModePrimeFiber_one_eq_primeSdiff_of_bounds
    {Λ : ℝ} {t k : ℕ}
    (hlo : (k : ℝ) ^ 2 ≤ 2 * Λ * (t : ℝ) + 1)
    (hhi : 2 * Λ * (t : ℝ) + 1 < ((k : ℝ) + 1) ^ 2) :
    survivorZeroModePrimeFiber Λ t 1 =
      ((Finset.Icc 2 (squarePrefixEndpoint t)).filter Nat.Prime) \
        ((Finset.Icc 2 k).filter Nat.Prime) := by
  classical
  ext q
  constructor
  · intro hqmem
    rcases Finset.mem_filter.mp hqmem with ⟨hqI, hpair⟩
    rcases (isSurvivorZeroModePair_one_iff_cutoff hlo hhi).1 hpair with
      ⟨hqPrime, _hqX, hkq⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hqI, hqPrime⟩, ?_⟩
    intro hsmall
    have hqk := (Finset.mem_Icc.mp (Finset.mem_filter.mp hsmall).1).2
    omega
  · intro hqmem
    rcases Finset.mem_sdiff.mp hqmem with ⟨hfull, hsmall⟩
    rcases Finset.mem_filter.mp hfull with ⟨hqI, hqPrime⟩
    have hkq : k < q := by
      by_contra hnot
      apply hsmall
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hqPrime.two_le, by omega⟩, hqPrime⟩
    apply Finset.mem_filter.mpr
    exact ⟨hqI, (isSurvivorZeroModePair_one_iff_cutoff hlo hhi).2
      ⟨hqPrime, (Finset.mem_Icc.mp hqI).2, hkq⟩⟩

/-- Exact natural prime-count difference for the pure-prime kernel. -/
theorem survivorZeroModeKernel_one_eq_primeCount_sub_of_bounds
    {Λ : ℝ} {t k : ℕ}
    (hlo : (k : ℝ) ^ 2 ≤ 2 * Λ * (t : ℝ) + 1)
    (hhi : 2 * Λ * (t : ℝ) + 1 < ((k : ℝ) + 1) ^ 2)
    (hkX : k ≤ squarePrefixEndpoint t) :
    survivorZeroModeKernel Λ t 1 =
      primeCountUpTo (squarePrefixEndpoint t) - primeCountUpTo k := by
  classical
  have hsub : ((Finset.Icc 2 k).filter Nat.Prime) ⊆
      ((Finset.Icc 2 (squarePrefixEndpoint t)).filter Nat.Prime) := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqI, hqPrime⟩
    rcases Finset.mem_Icc.mp hqI with ⟨hq2, hqk⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hq2, hqk.trans hkX⟩, hqPrime⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [survivorZeroModeKernel,
    survivorZeroModePrimeFiber_one_eq_primeSdiff_of_bounds hlo hhi]
  unfold primeCountUpTo
  omega

/-- The prime component carries the negative sign of `mu(q)`. -/
theorem survivorPrimeZeroMode_eq_neg_kernel
    (Λ : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    survivorPrimeZeroMode Λ t = -(survivorZeroModeKernel Λ t 1 : ℂ) := by
  classical
  have hsq : 2 ≤ (t + 1) ^ 2 := by nlinarith
  have hX : 1 ≤ squarePrefixEndpoint t := by
    unfold squarePrefixEndpoint
    omega
  simp [survivorPrimeZeroMode, Finset.sum_ite_eq', Finset.mem_Icc,
    hX, canonicalMoebiusWeight]

/-- Exact prime survivor for any integer cutoff bracketed by consecutive squares. -/
theorem survivorPrimeZeroMode_eq_neg_primeCount_sub_of_bounds
    {Λ : ℝ} {t k : ℕ} (ht : 1 ≤ t)
    (hlo : (k : ℝ) ^ 2 ≤ 2 * Λ * (t : ℝ) + 1)
    (hhi : 2 * Λ * (t : ℝ) + 1 < ((k : ℝ) + 1) ^ 2)
    (hkX : k ≤ squarePrefixEndpoint t) :
    survivorPrimeZeroMode Λ t =
      -((primeCountUpTo (squarePrefixEndpoint t) - primeCountUpTo k : ℕ) : ℂ) := by
  rw [survivorPrimeZeroMode_eq_neg_kernel Λ ht,
    survivorZeroModeKernel_one_eq_primeCount_sub_of_bounds hlo hhi hkX]

/-- Exact prime survivor at the canonical floor-square-root cutoff. -/
theorem survivorPrimeZeroMode_eq_neg_primeCount_sub
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {t : ℕ} (ht : 1 ≤ t)
    (hkX : survivorPrimeCutoff Λ t ≤ squarePrefixEndpoint t) :
    survivorPrimeZeroMode Λ t =
      -((primeCountUpTo (squarePrefixEndpoint t) -
        primeCountUpTo (survivorPrimeCutoff Λ t) : ℕ) : ℂ) := by
  exact survivorPrimeZeroMode_eq_neg_primeCount_sub_of_bounds ht
    (survivorPrimeCutoff_bounds hΛ t).1
    (survivorPrimeCutoff_bounds hΛ t).2 hkX

/-- The composite survivor retains the full signed cancellation against primes. -/
theorem survivorCompositeZeroMode_eq_survivor_add_primeCount_sub
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {t : ℕ} (ht : 1 ≤ t)
    (hkX : survivorPrimeCutoff Λ t ≤ squarePrefixEndpoint t) :
    survivorCompositeZeroMode Λ t = survivorZeroMode Λ t +
      ((primeCountUpTo (squarePrefixEndpoint t) -
        primeCountUpTo (survivorPrimeCutoff Λ t) : ℕ) : ℂ) := by
  have hsplit := survivorZeroMode_eq_prime_add_composite Λ t
  rw [survivorPrimeZeroMode_eq_neg_primeCount_sub hΛ ht hkX] at hsplit
  linear_combination -hsplit

/-- Once the fixed height parameter is below the stage, its prime cutoff is
at most the stage, much smaller than the square endpoint. -/
theorem survivorPrimeCutoff_le_stage
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {t : ℕ} (ht : 1 ≤ t)
    (hstage : 2 * Λ ≤ (t : ℝ)) :
    survivorPrimeCutoff Λ t ≤ t := by
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hprod := mul_le_mul_of_nonneg_right hstage (Nat.cast_nonneg t)
  have hlo := (survivorPrimeCutoff_bounds hΛ t).1
  by_contra hnot
  have hnext : (t : ℝ) + 1 ≤ (survivorPrimeCutoff Λ t : ℝ) := by
    exact_mod_cast (show t + 1 ≤ survivorPrimeCutoff Λ t by omega)
  have hsq := (sq_le_sq₀ (by positivity) (Nat.cast_nonneg _)).mpr hnext
  nlinarith

/-- A prime term can be alive before it is absorbed by the moving boundary. -/
theorem prime_two_survives_stage_one :
    IsSurvivorZeroModePair 1 1 1 2 := by
  rw [isSurvivorZeroModePair_one_iff]
  norm_num [squarePrefixEndpoint]

/-- The same prime term is no longer alive at the next stage. -/
theorem prime_two_not_survivor_stage_two :
    ¬ IsSurvivorZeroModePair 1 2 1 2 := by
  rw [isSurvivorZeroModePair_one_iff]
  norm_num [squarePrefixEndpoint]

/-- The composite integer `6 = 2 * 3` is still represented in the survivor
at stage two, so survival does not mean primality. -/
theorem composite_six_survives_stage_two :
    IsSurvivorZeroModePair 1 2 2 3 := by
  refine ⟨?_, by norm_num [squarePrefixEndpoint], by norm_num⟩
  refine ⟨by norm_num, by norm_num, Nat.prime_two.squarefree, by norm_num, ?_⟩
  intro p hp hpd
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpd
  subst p
  norm_num

end RHLean.Proof
