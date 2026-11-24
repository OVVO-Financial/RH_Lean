import RHLean.Analysis.AlpogeSquareClockSignedHistorySampling
import RHLean.Proof.LowWheelHighPrimeSurvivor

/-!
# Completed square-wheel candidate capacity

The candidate and removal masses below are defined from actual finite sets,
logarithmic weights and the original kernel `N/n - 1`. Their difference is
proved equal to the complete native `Gz`; neither mass is defined using `Gz`.

A square-dependent prefix wheel supplies a concrete prime-complete candidate
set. Square boundary sites are retained when the partial wheel permits them
and are removed as composites, so no boundary correction is discarded.

The proper-prime-power term is kept independently of the candidate set. Even
the single site `4` gives a linear lower bound for this term. It cannot be
discarded as a square-root error in this weighted kernel.

These are exact source and accounting theorems. They do not prove the open
lower bound on removed composite capacity at square-root precision.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

/-- The original nonnegative kernel on `1 <= n <= N`. -/
def nativeSquareCandidateKernel (N n : ℕ) : ℝ := (N : ℝ) / (n : ℝ) - 1

/-- Logarithmic mass of an actual candidate site. -/
def nativeSquareCandidateWeight (N n : ℕ) : ℝ :=
  Real.log (n : ℝ) * nativeSquareCandidateKernel N n

/-- All nonprime von Mangoldt entries. Only proper prime powers contribute. -/
def nativeSquareProperPowerCapacity (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Prime),
    Λ n * nativeSquareCandidateKernel N n

/-- Centered candidate capacity, including the entire proper-power correction. -/
def nativeSquareCandidateCapacity (C : Finset ℕ) (N : ℕ) : ℝ :=
  (∑ n ∈ C, nativeSquareCandidateWeight N n) +
    nativeSquareProperPowerCapacity N - (N : ℝ) * Real.log (N : ℝ) +
      (1 + Real.eulerMascheroniConstant) * (N : ℝ)

/-- Capacity removed at the actual composite candidate sites. -/
def nativeSquareCompositeRemoval (C : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ C.filter (fun n => ¬ n.Prime), nativeSquareCandidateWeight N n

theorem nativeSquareCandidateKernel_nonneg {N n : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    0 ≤ nativeSquareCandidateKernel N n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hle : (n : ℝ) ≤ N := by exact_mod_cast hnN
  unfold nativeSquareCandidateKernel
  exact sub_nonneg.mpr ((one_le_div hnpos).mpr hle)

theorem nativeSquareCandidateWeight_nonneg {N n : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    0 ≤ nativeSquareCandidateWeight N n := by
  exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hn))
    (nativeSquareCandidateKernel_nonneg hn hnN)

theorem nativeSquareProperPowerCapacity_nonneg (N : ℕ) :
    0 ≤ nativeSquareProperPowerCapacity N := by
  apply Finset.sum_nonneg
  intro n hn
  have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (nativeSquareCandidateKernel_nonneg hnI.1 hnI.2)

/-- Finite expansion of the complete prime-power source before centering. -/
theorem nativeSquareCandidateKernel_vonMangoldt_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, Λ n * nativeSquareCandidateKernel N n) =
      (N : ℝ) * nativeLambdaRecip N - nativePsi N := by
  unfold nativeLambdaRecip nativePsi
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  unfold nativeSquareCandidateKernel
  ring

/-- Removing all composite candidate sites leaves precisely the native source.
The hypotheses are set containment and prime coverage, with no analytic bound. -/
theorem nativeAlpogeGz_eq_candidateCapacity_sub_removal
    (C : Finset ℕ) (N : ℕ)
    (hC : C ⊆ Finset.Icc 1 N)
    (hprime : ∀ p ∈ Finset.Icc 1 N, p.Prime → p ∈ C) :
    nativeAlpogeGz N =
      nativeSquareCandidateCapacity C N - nativeSquareCompositeRemoval C N := by
  classical
  have hset : C.filter Nat.Prime = (Finset.Icc 1 N).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun hp => ⟨hC hp.1, hp.2⟩,
      fun hp => ⟨hprime p hp.1 hp.2, hp.2⟩⟩
  have hprimeWeight :
      (∑ p ∈ C.filter Nat.Prime, nativeSquareCandidateWeight N p) =
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          Λ p * nativeSquareCandidateKernel N p := by
    rw [hset]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
    rfl
  have hcandidate := Finset.sum_filter_add_sum_filter_not
    (s := C) (p := Nat.Prime) (f := nativeSquareCandidateWeight N)
  have hsource := Finset.sum_filter_add_sum_filter_not
    (s := Finset.Icc 1 N) (p := Nat.Prime)
    (f := fun n => Λ n * nativeSquareCandidateKernel N n)
  rw [hprimeWeight] at hcandidate
  rw [nativeSquareCandidateKernel_vonMangoldt_sum] at hsource
  unfold nativeAlpogeGz nativeSquareCandidateCapacity
    nativeSquareCompositeRemoval nativeSquareProperPowerCapacity
  linarith only [hcandidate, hsource]

/-- Exact equivalence of the proposed removal estimate and the original bound.
This theorem explicitly retains the unproved quantitative inequality. -/
theorem nativeAlpogeGz_le_iff_candidateRemoval
    (C : Finset ℕ) (N : ℕ) (B : ℝ)
    (hC : C ⊆ Finset.Icc 1 N)
    (hprime : ∀ p ∈ Finset.Icc 1 N, p.Prime → p ∈ C) :
    nativeAlpogeGz N ≤ B ↔
      nativeSquareCandidateCapacity C N - B ≤ nativeSquareCompositeRemoval C N := by
  rw [nativeAlpogeGz_eq_candidateCapacity_sub_removal C N hC hprime]
  constructor <;> intro h <;> linarith only [h]

/-- Changing the prime-complete candidate set changes capacity and removal by
exactly the same amount. In particular, early sites cannot be discarded on
only one side of the accounting identity. -/
theorem nativeSquareCandidateCapacity_change_eq_removal_change
    (C D : Finset ℕ) (N : ℕ)
    (hC : C ⊆ Finset.Icc 1 N) (hD : D ⊆ Finset.Icc 1 N)
    (hpC : ∀ p ∈ Finset.Icc 1 N, p.Prime → p ∈ C)
    (hpD : ∀ p ∈ Finset.Icc 1 N, p.Prime → p ∈ D) :
    nativeSquareCandidateCapacity C N - nativeSquareCandidateCapacity D N =
      nativeSquareCompositeRemoval C N - nativeSquareCompositeRemoval D N := by
  have h1 := nativeAlpogeGz_eq_candidateCapacity_sub_removal C N hC hpC
  have h2 := nativeAlpogeGz_eq_candidateCapacity_sub_removal D N hD hpD
  linarith only [h1, h2]

/-- Native candidate carrier: one prefix-wheel cutoff for each square block.
The first primes are included automatically because their square roots are
smaller than themselves. Composite square boundaries retain their exact cost. -/
def nativeSquarePrefixCandidates (cutoff : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter fun n => lowWheelHighSurvivor (cutoff (Nat.sqrt n)) n

theorem nativeSquarePrefixCandidates_subset (cutoff : ℕ → ℕ) (N : ℕ) :
    nativeSquarePrefixCandidates cutoff N ⊆ Finset.Icc 1 N := by
  intro n hn
  have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  exact Finset.mem_Icc.mpr ⟨by omega, hnI.2⟩

theorem nativeSquarePrefixCandidates_contains_prime
    (cutoff : ℕ → ℕ) (hcutoff : ∀ r, cutoff r ≤ r)
    (N p : ℕ) (hpN : p ∈ Finset.Icc 1 N) (hp : p.Prime) :
    p ∈ nativeSquarePrefixCandidates cutoff N := by
  have hroot : Nat.sqrt p < p := by
    have hsquare := Nat.sqrt_le' p
    by_contra hnot
    have hle : p ≤ Nat.sqrt p := by omega
    have hpow := Nat.pow_le_pow_left hle 2
    have hp2 := hp.two_le
    nlinarith
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hp.two_le, (Finset.mem_Icc.mp hpN).2⟩, ?_⟩
  intro q hq hqdvd
  have hqprime := prime_of_mem_primesUpTo hq
  have hqcut := (mem_primesUpTo.mp hq).2
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hp).mp hqdvd
  have hcut := hcutoff (Nat.sqrt p)
  omega

/-- Source identity instantiated on actual native square-dependent wheels. -/
theorem nativeAlpogeGz_eq_squarePrefixCapacity_sub_removal
    (cutoff : ℕ → ℕ) (hcutoff : ∀ r, cutoff r ≤ r) (N : ℕ) :
    nativeAlpogeGz N =
      nativeSquareCandidateCapacity (nativeSquarePrefixCandidates cutoff N) N -
        nativeSquareCompositeRemoval (nativeSquarePrefixCandidates cutoff N) N := by
  exact nativeAlpogeGz_eq_candidateCapacity_sub_removal _ N
    (nativeSquarePrefixCandidates_subset cutoff N)
    (nativeSquarePrefixCandidates_contains_prime cutoff hcutoff N)

/-- At the full square-root cutoff the candidate set is exactly the primes. -/
theorem nativeSquarePrefixCandidates_full_eq_primes (N : ℕ) :
    nativeSquarePrefixCandidates (fun r => r) N = nativePrimeSet N := by
  classical
  ext n
  constructor
  · intro hn
    have hni := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hsurv := (Finset.mem_filter.mp hn).2
    have hprime : n.Prime := by
      by_contra hnot
      have hn1 : n ≠ 1 := by omega
      have hfactor := Nat.minFac_prime hn1
      have hsquare := Nat.minFac_sq_le_self (by omega : 0 < n) hnot
      have hroot : n.minFac ≤ Nat.sqrt n :=
        Nat.le_sqrt.mpr (by simpa only [pow_two] using hsquare)
      exact hsurv n.minFac (mem_primesUpTo.mpr ⟨hfactor, hroot⟩)
        (Nat.minFac_dvd n)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hni.2⟩, hprime⟩
  · intro hn
    exact nativeSquarePrefixCandidates_contains_prime (fun r => r) (fun _ => le_rfl)
      N n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2

/-- The single proper prime power `4` already contributes a linear weight. -/
theorem nativeSquareProperPowerCapacity_four_lower (N : ℕ) (hN : 4 ≤ N) :
    Real.log 2 * ((N : ℝ) / 4 - 1) ≤ nativeSquareProperPowerCapacity N := by
  classical
  have hmem : 4 ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Prime) := by
    norm_num [Finset.mem_filter, Finset.mem_Icc, hN]
  have hsum := Finset.single_le_sum
    (s := (Finset.Icc 1 N).filter (fun n => ¬ n.Prime))
    (f := fun n => Λ n * nativeSquareCandidateKernel N n)
    (fun n hn =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (nativeSquareCandidateKernel_nonneg
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2)) hmem
  have hfour : Λ 4 = Real.log 2 := by
    have heq : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [heq, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  simpa only [nativeSquareCandidateKernel, Nat.cast_ofNat, hfour,
    nativeSquareProperPowerCapacity] using hsum

/-- A fixed positive linear lower bound: the completed power correction is
not a root-scale remainder. No asymptotic prime theorem is needed. -/
theorem nativeSquareProperPowerCapacity_linear_lower (N : ℕ) (hN : 8 ≤ N) :
    (Real.log 2 / 8) * (N : ℝ) ≤ nativeSquareProperPowerCapacity N := by
  have hfour := nativeSquareProperPowerCapacity_four_lower N (by omega)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hNR : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hprice : 0 ≤ Real.log 2 * ((N : ℝ) - 8) :=
    mul_nonneg hlog (by linarith)
  nlinarith only [hfour, hprice]

end RHLean.Analysis
