import Mathlib
import «research.ALPOGE_GZ_VFMID_DELTA_TRANSFER_20261122»
import RHLean.Analysis.NativePNTChebyshev

/-!
# Alpoge Gz as the EXACT weighted delta(t) history in native arithmetic

The full von Mangoldt Gz ramp splits into:
  - actual ordinary prime counting increments pi(n)-pi(n-1);
  - genuine higher-prime-power sites, with their original Lambda weights.
The actual prime increment is then decomposed into
  Delta(n)-Delta(n-1) + Li_2(n)-Li_2(n-1)
and Delta is changed EXACTLY to the original VF_mid prime error plus
its deterministic quadrature correction.

No smallness is assigned to any of these summands. No RH or
analytic estimate is imported. This is the integer-grid Abel source
underlying the continuous logarithmic kernel.

This file supplements the earlier real cutoff identity
alpogeRealPrimeDelta_eq_vfMid_add_quadrature.
-/

noncomputable section
open Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Alpoge's original linear kernel applied to an integer arithmetic site.
Only positive sites are sampled in all definitions below. -/
def alpogeNativeRampWeight (N n : ℕ) : ℝ :=
  Real.log (n : ℝ) * ((N : ℝ) / (n : ℝ) - 1)

/-- Actual von Mangoldt ramp with all prime powers present. -/
def alpogeNativeLambdaRamp (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    Λ n * ((N : ℝ) / (n : ℝ) - 1)

/-- Its literal prime contribution, no models or substitutions. -/
def alpogeNativePrimeRamp (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime,
    Λ n * ((N : ℝ) / (n : ℝ) - 1)

/-- Its literal nonprime von Mangoldt contribution. It is supported
only at higher prime powers, since Lambda vanishes elsewhere. -/
def alpogeNativeHigherPrimePowerRamp (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬Nat.Prime n),
    Λ n * ((N : ℝ) / (n : ℝ) - 1)

/-- The exact original Gz is the full Lambda ramp minus its
explicit x log x centering. -/
theorem nativeAlpogeGz_eq_lambdaRamp (N : ℕ) :
    nativeAlpogeGz N =
      alpogeNativeLambdaRamp N -
        (N : ℝ) * Real.log (N : ℝ) +
        (1 + Real.eulerMascheroniConstant) * (N : ℝ) := by
  have hsum :
      (N : ℝ) *
          (∑ n ∈ Finset.Icc 1 N, Λ n / (n : ℝ)) -
        (∑ n ∈ Finset.Icc 1 N, Λ n) =
      ∑ n ∈ Finset.Icc 1 N,
        Λ n * ((N : ℝ) / (n : ℝ) - 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  unfold nativeAlpogeGz nativeLambdaRecip nativePsi
    alpogeNativeLambdaRamp
  rw [hsum]

/-- Source-preserving exact split of Lambda between the prime population
and the higher-prime-power remainder. No triangle inequality. -/
theorem alpogeNativeLambdaRamp_eq_prime_add_higher (N : ℕ) :
    alpogeNativeLambdaRamp N =
      alpogeNativePrimeRamp N + alpogeNativeHigherPrimePowerRamp N := by
  unfold alpogeNativeLambdaRamp alpogeNativePrimeRamp
    alpogeNativeHigherPrimePowerRamp
  symm
  exact Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 N) Nat.Prime (fun n => Λ n * ((N : ℝ) / (n : ℝ) - 1))

/-- Prime part with actual log p weights, as mandated by Lambda(p)=log p. -/
def alpogeOrdinaryPrimeRamp (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (if Nat.Prime n then alpogeNativeRampWeight N n else 0)

/-- No prime-power source is replaced or approximated by this identity. -/
theorem alpogeNativePrimeRamp_eq_primeLogRamp (N : ℕ) :
    alpogeNativePrimeRamp N = alpogeOrdinaryPrimeRamp N := by
  unfold alpogeNativePrimeRamp alpogeOrdinaryPrimeRamp
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hp : Nat.Prime n
  · simp [hp, alpogeNativeRampWeight,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [hp]

/-- The genuine jump of the prime-counting staircase at n. -/
def alpogePrimeCountIncrement (n : ℕ) : ℝ :=
  (Nat.primeCounting n : ℝ) -
    (Nat.primeCounting (n - 1) : ℝ)

/-- Each prime is counted ONCE at its own integer endpoint; all other
sites contribute zero. Uses actual Mathlib Nat.primeCounting. -/
theorem alpogePrimeCountIncrement_eq_indicator (n : ℕ) :
    alpogePrimeCountIncrement n =
      if Nat.Prime n then 1 else 0 := by
  cases n with
  | zero =>
      simp [alpogePrimeCountIncrement, Nat.not_prime_zero]
  | succ k =>
      have hc : Nat.primeCounting (k + 1) =
          Nat.primeCounting k + (if Nat.Prime (k + 1) then 1 else 0) := by
        change Nat.count Nat.Prime ((k + 1) + 1) =
          Nat.count Nat.Prime (k + 1) +
            (if Nat.Prime (k + 1) then 1 else 0)
        exact Nat.count_succ Nat.Prime (k + 1)
      unfold alpogePrimeCountIncrement
      show (Nat.primeCounting (k + 1) : ℝ) - (Nat.primeCounting k : ℝ) =
        if Nat.Prime (k + 1) then 1 else 0
      rw [hc]
      split_ifs <;> push_cast <;> ring

/-- Ordinary prime ramp is literally a weighted first difference of
the genuine prime-counting function. -/
theorem alpogeOrdinaryPrimeRamp_eq_pi_increments (N : ℕ) :
    alpogeOrdinaryPrimeRamp N =
      ∑ n ∈ Finset.Icc 1 N,
        alpogeNativeRampWeight N n * alpogePrimeCountIncrement n := by
  unfold alpogeOrdinaryPrimeRamp
  apply Finset.sum_congr rfl
  intro n _hn
  rw [alpogePrimeCountIncrement_eq_indicator]
  split_ifs <;> ring

/-- The exact TRUE prime-minus-Li discrepancy at integer sites. -/
def alpogeDiscretePrimeDelta (n : ℕ) : ℝ :=
  (Nat.primeCounting n : ℝ) -
    vfMidLogarithmicIntegralFromTwo (n : ℝ)

/-- The deterministic Li_2 increment at a natural site. -/
def alpogeDiscreteLiIncrement (n : ℕ) : ℝ :=
  vfMidLogarithmicIntegralFromTwo (n : ℝ) -
    vfMidLogarithmicIntegralFromTwo ((n - 1 : ℕ) : ℝ)

/-- Exact discrete prime-versus-Li splitting, with NO bound or smoothing. -/
theorem alpogePrimeIncrement_eq_delta_add_li (n : ℕ) :
    alpogePrimeCountIncrement n =
      (alpogeDiscretePrimeDelta n -
        alpogeDiscretePrimeDelta (n - 1)) +
      alpogeDiscreteLiIncrement n := by
  unfold alpogePrimeCountIncrement
    alpogeDiscretePrimeDelta alpogeDiscreteLiIncrement
  ring

/-- The signed Abel first-difference history of actual pi minus Li_2. -/
def alpogeDeltaFiniteAbelHistory (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    alpogeNativeRampWeight N n *
      (alpogeDiscretePrimeDelta n - alpogeDiscretePrimeDelta (n - 1))

/-- Entire deterministic Li reference history, not bounded or discarded. -/
def alpogeLiFiniteReferenceHistory (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    alpogeNativeRampWeight N n * alpogeDiscreteLiIncrement n

/-- Exact prime ramp = signed prime-minus-Li history + Li reference mass.
No "random primes" or independent prime/composite estimates. -/
theorem alpogeOrdinaryPrimeRamp_eq_delta_add_li (N : ℕ) :
    alpogeOrdinaryPrimeRamp N =
      alpogeDeltaFiniteAbelHistory N +
        alpogeLiFiniteReferenceHistory N := by
  rw [alpogeOrdinaryPrimeRamp_eq_pi_increments]
  unfold alpogeDeltaFiniteAbelHistory alpogeLiFiniteReferenceHistory
  calc
    (∑ n ∈ Finset.Icc 1 N,
      alpogeNativeRampWeight N n * alpogePrimeCountIncrement n) =
      (∑ n ∈ Finset.Icc 1 N,
        (alpogeNativeRampWeight N n *
            (alpogeDiscretePrimeDelta n -
              alpogeDiscretePrimeDelta (n - 1)) +
         alpogeNativeRampWeight N n *
            alpogeDiscreteLiIncrement n)) := by
              apply Finset.sum_congr rfl
              intro n _hn
              rw [alpogePrimeIncrement_eq_delta_add_li]
              ring
    _ = _ := Finset.sum_add_distrib

/-- EXACT full Gz source in terms of delta history, honest Li reference,
and original higher-prime-power correction. The only estimates needed
later must apply to this COMPLETE signed expression. -/
theorem nativeAlpogeGz_eq_delta_history_plus_primePowers
    (N : ℕ) :
    nativeAlpogeGz N =
      alpogeDeltaFiniteAbelHistory N +
        alpogeLiFiniteReferenceHistory N +
        alpogeNativeHigherPrimePowerRamp N -
        (N : ℝ) * Real.log (N : ℝ) +
        (1 + Real.eulerMascheroniConstant) * (N : ℝ) := by
  rw [nativeAlpogeGz_eq_lambdaRamp,
    alpogeNativeLambdaRamp_eq_prime_add_higher,
    alpogeNativePrimeRamp_eq_primeLogRamp,
    alpogeOrdinaryPrimeRamp_eq_delta_add_li]

/-- At every natural cutoff the real-coordinate delta exactly equals the
native discrete delta. The continuum interpolation is NOT dropped. -/
theorem alpogeDiscretePrimeDelta_eq_real (n : ℕ) :
    alpogeDiscretePrimeDelta n = alpogeRealPrimeDelta (n : ℝ) := by
  simp [alpogeDiscretePrimeDelta, alpogeRealPrimeDelta,
    vfMidPrimeLiError, vfMidPrimeCount]

/-- Original signed discrete delta in the native VF_mid coordinates. -/
def alpogeVFMidFiniteAbelHistory (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, alpogeNativeRampWeight N n *
    (alpogeVFMidPrimeDelta (n : ℝ) -
      alpogeVFMidPrimeDelta ((n - 1 : ℕ) : ℝ))

/-- Exact (and *not* pointwise O(1)!) quadrature first-difference history. -/
def alpogeQuadratureFiniteAbelHistory (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, alpogeNativeRampWeight N n *
    (alpogeVFMidQuadratureDelta (n : ℝ) -
      alpogeVFMidQuadratureDelta ((n - 1 : ℕ) : ℝ))

/-- The weighted genuine prime delta is EXACTLY its VF_mid coordinate
plus the weighted midpoint quadrature history. The signed terms
are summed before any separate absolute bounds are attempted. -/
theorem alpogeDeltaFiniteAbelHistory_eq_vfMid_add_quadrature (N : ℕ) :
    alpogeDeltaFiniteAbelHistory N =
      alpogeVFMidFiniteAbelHistory N +
        alpogeQuadratureFiniteAbelHistory N := by
  unfold alpogeDeltaFiniteAbelHistory
    alpogeVFMidFiniteAbelHistory alpogeQuadratureFiniteAbelHistory
  calc
    (∑ n ∈ Finset.Icc 1 N,
      alpogeNativeRampWeight N n *
        (alpogeDiscretePrimeDelta n -
          alpogeDiscretePrimeDelta (n - 1))) =
      (∑ n ∈ Finset.Icc 1 N,
        (alpogeNativeRampWeight N n *
            (alpogeVFMidPrimeDelta (n : ℝ) -
              alpogeVFMidPrimeDelta ((n - 1 : ℕ) : ℝ)) +
         alpogeNativeRampWeight N n *
            (alpogeVFMidQuadratureDelta (n : ℝ) -
              alpogeVFMidQuadratureDelta ((n - 1 : ℕ) : ℝ)))) := by
          apply Finset.sum_congr rfl
          intro n _hn
          rw [alpogeDiscretePrimeDelta_eq_real,
            alpogeDiscretePrimeDelta_eq_real]
          rw [alpogeRealPrimeDelta_eq_vfMid_add_quadrature,
            alpogeRealPrimeDelta_eq_vfMid_add_quadrature]
          ring
    _ = _ := Finset.sum_add_distrib

/-- FINAL exact signed native coordinate identity, retaining all sources:
    Gz = weighted(pi-VF_mid) + weighted(VF_mid-Li2) +
         exact Li-reference + genuine higher-prime powers + main centering.
This is a genuine source derivation, *not* an assumed operator equation. -/
theorem nativeAlpogeGz_eq_weightedVFMidDelta_and_primePowers
    (N : ℕ) :
    nativeAlpogeGz N =
      alpogeVFMidFiniteAbelHistory N +
        alpogeQuadratureFiniteAbelHistory N +
        alpogeLiFiniteReferenceHistory N +
        alpogeNativeHigherPrimePowerRamp N -
        (N : ℝ) * Real.log (N : ℝ) +
        (1 + Real.eulerMascheroniConstant) * (N : ℝ) := by
  rw [nativeAlpogeGz_eq_delta_history_plus_primePowers,
    alpogeDeltaFiniteAbelHistory_eq_vfMid_add_quadrature]

/-- If the genuine *whole* source just identified is O(R), then the
square-lattice quantitative Gz premise is literally discharged.
This theorem avoids replacing a character/prime-power source by an
unrelated proxy. The bound itself is an EXPLICIT arithmetic hypothesis. -/
theorem alpogeSquareCritical_of_complete_VFMid_source
    (C : ℝ) (hC : 0 ≤ C)
    (hSignedSource : ∀ R : ℕ, 2 ≤ R →
      |alpogeVFMidFiniteAbelHistory (R ^ 2) +
        alpogeQuadratureFiniteAbelHistory (R ^ 2) +
        alpogeLiFiniteReferenceHistory (R ^ 2) +
        alpogeNativeHigherPrimePowerRamp (R ^ 2) -
        ((R ^ 2 : ℕ) : ℝ) * Real.log ((R ^ 2 : ℕ) : ℝ) +
        (1 + Real.eulerMascheroniConstant) * ((R ^ 2 : ℕ) : ℝ)| ≤
        C * (R : ℝ)) :
    AlpogeCriticalSquareGzStatement := by
  refine ⟨C, hC, ?_⟩
  intro R hR
  rw [nativeAlpogeGz_eq_weightedVFMidDelta_and_primePowers]
  exact hSignedSource R hR

end RHLean.Analysis
