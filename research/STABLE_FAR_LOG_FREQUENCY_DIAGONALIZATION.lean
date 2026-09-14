import Mathlib
import RHLean.Proof.CanonicalRoughBoundaryProfileAbelReturn
import RHLean.Proof.FarSurvivorRenewal_is_LowerMertens
import RHLean.Proof.LowWheelCanonicalSqrtDenseContraction
import RHLean.Proof.SquareRootPredecessorPrimeCells

/-!
# Exact log-frequency form of the FAR-4 Euler cancellation

This file tests the frequency interpretation of the already-compiled signed
Euler/q^2 mechanism without replacing the physical Mobius field by a periodic
surrogate and without taking a norm.

There are two exact statements.

1. In logarithmic scale `t = log x`, a q^2 daughter is the same pure frequency
   mode translated by `2 log q`.  Translation is therefore multiplication by a
   single phase.  The original ownerwise Mertens column is exactly the
   zero-frequency member of the resulting finite family.

2. A prime-by-prime Euler telescope with an arbitrary complex weight is finite
   Abel summation.  Specializing the weight to `exp(i*tau*log p)` shows that the
   failure of exact zero-frequency cancellation at nonzero frequency is *only*
   the discrete phase-gradient term.  No unsigned support count is introduced.

This is a coordinate theorem, not an energy estimate: no bound on the phase
variation is asserted here.  Its purpose is to expose, on the same finite
arithmetic objects used by FAR-4, the precise signed mechanism that a later
quantitative alignment theorem would have to control.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Pure log-frequency modes and q^2 translation -/

/-- A pure frequency on logarithmic scale. -/
def stableFarLogFrequencyMode (tau t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((tau * t : ℝ) : ℂ))

/-- The same frequency sampled at the logarithm of an integer coordinate. -/
def stableFarPrimeLogPhase (tau : ℝ) (n : ℕ) : ℂ :=
  stableFarLogFrequencyMode tau (Real.log (n : ℝ))

/-- Phase multiplier induced by the q^2 dilation `x -> x/q^2`. -/
def stableFarQ2LogFrequencyMultiplier (tau : ℝ) (q : ℕ) : ℂ :=
  stableFarLogFrequencyMode tau (-(2 * Real.log (q : ℝ)))

@[simp] theorem stableFarLogFrequencyMode_zero_frequency (t : ℝ) :
    stableFarLogFrequencyMode 0 t = 1 := by
  simp [stableFarLogFrequencyMode]

@[simp] theorem stableFarPrimeLogPhase_zero_frequency (n : ℕ) :
    stableFarPrimeLogPhase 0 n = 1 := by
  simp [stableFarPrimeLogPhase]

@[simp] theorem stableFarPrimeLogPhase_one (tau : ℝ) :
    stableFarPrimeLogPhase tau 1 = 1 := by
  simp [stableFarPrimeLogPhase, stableFarLogFrequencyMode]

@[simp] theorem stableFarQ2LogFrequencyMultiplier_zero_frequency (q : ℕ) :
    stableFarQ2LogFrequencyMultiplier 0 q = 1 := by
  simp [stableFarQ2LogFrequencyMultiplier]

/-- **Translation diagonalizes a pure log-frequency.** -/
theorem stableFarLogFrequencyMode_shift
    (tau t a : ℝ) :
    stableFarLogFrequencyMode tau (t - a) =
      stableFarLogFrequencyMode tau (-a) *
        stableFarLogFrequencyMode tau t := by
  unfold stableFarLogFrequencyMode
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **q^2 daughters are phase-rotated copies of the same frequency.**
There is no new mode on the child side: only the scalar multiplier changes. -/
theorem stableFarLogFrequencyMode_q2_shift
    (tau t : ℝ) (q : ℕ) :
    stableFarLogFrequencyMode tau
        (t - 2 * Real.log (q : ℝ)) =
      stableFarQ2LogFrequencyMultiplier tau q *
        stableFarLogFrequencyMode tau t := by
  simpa [stableFarQ2LogFrequencyMultiplier] using
    stableFarLogFrequencyMode_shift tau t (2 * Real.log (q : ℝ))

/-! ## The ownerwise q^2 Mertens column as a frequency family -/

/-- Phase-twisted odd-owner q^2 Mertens column.  At frequency zero this is
literally the current FAR-4 ownerwise Mertens column. -/
def farFourOddMertensLogFrequencyColumn (R : ℕ) (tau : ℝ) : ℂ :=
  ∑ q ∈ (primesUpTo (R - 1)).erase 2,
    stableFarQ2LogFrequencyMultiplier tau q *
      (((mertensSummatoryInt (squareRootEndpoint R / (q * q)) : ℤ) : ℂ))

/-- The physical ownerwise Mertens column is the zero-frequency fibre. -/
@[simp] theorem farFourOddMertensLogFrequencyColumn_zero (R : ℕ) :
    farFourOddMertensLogFrequencyColumn R 0 =
      farFourOddMertensColumn R := by
  unfold farFourOddMertensLogFrequencyColumn farFourOddMertensColumn
  push_cast
  simp

/-! ## Complex finite Abel summation: cancellation versus phase variation -/

/-- **Complex weighted finite Abel identity.**

The zero-frequency telescope is the special case `a = 1`.  For a nonconstant
frequency weight every failure to telescope is localized exactly in the
coefficient differences `a(n+1)-a(n)`; there is no additional arithmetic
remainder. -/
theorem complex_weighted_boundaryDrop_eq_abel
    (a B : ℕ → ℂ) {K : ℕ} (hK : 1 ≤ K) :
    (∑ n ∈ Finset.Icc 1 K, a n * (B (n - 1) - B n)) =
      a 1 * B 0 - a K * B K +
        ∑ n ∈ Finset.Ico 1 K, (a (n + 1) - a n) * B n := by
  induction K, hK using Nat.le_induction with
  | base =>
      simp
      ring
  | succ K hK ih =>
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ K + 1), ih,
        Finset.sum_Ico_succ_top hK]
      simp only [Nat.add_sub_cancel]
      ring

/-- If a profile moves only when a prime is adjoined, its prime-indexed weighted
drops are the full weighted Abel transform. -/
theorem complex_weighted_prime_boundaryDrop_eq_abel
    (a B : ℕ → ℂ) (K : ℕ) (hK : 1 ≤ K)
    (hstat : ∀ n, ¬ n.Prime → B n = B (n - 1)) :
    (∑ q ∈ primesUpTo K, a q * (B (q - 1) - B q)) =
      a 1 * B 0 - a K * B K +
        ∑ n ∈ Finset.Ico 1 K, (a (n + 1) - a n) * B n := by
  have hprimeToAll :
      (∑ q ∈ primesUpTo K, a q * (B (q - 1) - B q)) =
        ∑ n ∈ Finset.Icc 1 K, a n * (B (n - 1) - B n) := by
    refine Finset.sum_subset (primesUpTo_subset_Icc_one K) ?_
    intro n hn hnot
    have hnle : n ≤ K := (Finset.mem_Icc.mp hn).2
    have hnp : ¬ n.Prime := by
      intro hp
      exact hnot (mem_primesUpTo.mpr ⟨hp, hnle⟩)
    rw [hstat n hnp]
    ring
  rw [hprimeToAll, complex_weighted_boundaryDrop_eq_abel a B hK]

/-! ## Apply the frequency Abel identity to the frozen Euler profile -/

/-- Complex form of the signed frozen-window profile. -/
def stableFarFrozenWindowProfile (A B n : ℕ) : ℂ :=
  ((frozenPrimeUniverseWindowMass (primesUpTo n) A B : ℤ) : ℂ)

/-- The frozen profile is stationary at composite cutoffs. -/
theorem stableFarFrozenWindowProfile_eq_pred_of_not_prime
    (A B : ℕ) {n : ℕ} (hn : ¬ n.Prime) :
    stableFarFrozenWindowProfile A B n =
      stableFarFrozenWindowProfile A B (n - 1) := by
  unfold stableFarFrozenWindowProfile
  rw [primesUpTo_eq_pred_of_not_prime hn]

/-- One prime drop of the frozen profile is exactly the corresponding
predecessor window.  This is the pointwise step hidden inside the unweighted
high-prime telescope. -/
theorem stableFarFrozenWindowProfile_primeDrop_eq_window
    (A B p : ℕ) (hAB : A ≤ B) (hp : p.Prime) :
    stableFarFrozenWindowProfile A B (p - 1) -
        stableFarFrozenWindowProfile A B p =
      ((frozenPrimeUniverseWindowMass (primesUpTo (p - 1))
          (A / p) (B / p) : ℤ) : ℂ) := by
  have hB := frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor p B hp
  have hA := frozenPrimeUniverseMass_primesUpTo_step_eq_sub_predecessor p A hp
  unfold predecessorPrimeMass at hB hA
  unfold stableFarFrozenWindowProfile
  rw [frozenPrimeUniverseWindowMass_eq_sub hAB]
  rw [frozenPrimeUniverseWindowMass_eq_sub hAB]
  rw [frozenPrimeUniverseWindowMass_eq_sub (Nat.div_le_div_right hAB)]
  rw [hB, hA]
  push_cast
  ring

/-- **Exact log-frequency decomposition of the prime-by-prime Euler telescope.**

At frequency zero the phase gradient vanishes and the whole high-prime column
collapses to two endpoints.  At nonzero frequency the only obstruction is the
signed discrete phase-gradient term displayed on the right. -/
theorem frozenPrimeUniverse_logFrequency_telescope
    (tau : ℝ) (A B K : ℕ) (hK : 1 ≤ K) (hAB : A ≤ B) :
    (∑ p ∈ primesUpTo K,
      stableFarPrimeLogPhase tau p *
        ((frozenPrimeUniverseWindowMass (primesUpTo (p - 1))
          (A / p) (B / p) : ℤ) : ℂ)) =
      stableFarFrozenWindowProfile A B 0 -
        stableFarPrimeLogPhase tau K * stableFarFrozenWindowProfile A B K +
        ∑ n ∈ Finset.Ico 1 K,
          (stableFarPrimeLogPhase tau (n + 1) -
            stableFarPrimeLogPhase tau n) *
            stableFarFrozenWindowProfile A B n := by
  calc
    (∑ p ∈ primesUpTo K,
      stableFarPrimeLogPhase tau p *
        ((frozenPrimeUniverseWindowMass (primesUpTo (p - 1))
          (A / p) (B / p) : ℤ) : ℂ)) =
      ∑ p ∈ primesUpTo K,
        stableFarPrimeLogPhase tau p *
          (stableFarFrozenWindowProfile A B (p - 1) -
            stableFarFrozenWindowProfile A B p) := by
              apply Finset.sum_congr rfl
              intro p hpMem
              rw [stableFarFrozenWindowProfile_primeDrop_eq_window
                A B p hAB (prime_of_mem_primesUpTo hpMem)]
    _ = stableFarPrimeLogPhase tau 1 * stableFarFrozenWindowProfile A B 0 -
        stableFarPrimeLogPhase tau K * stableFarFrozenWindowProfile A B K +
        ∑ n ∈ Finset.Ico 1 K,
          (stableFarPrimeLogPhase tau (n + 1) -
            stableFarPrimeLogPhase tau n) *
            stableFarFrozenWindowProfile A B n :=
      complex_weighted_prime_boundaryDrop_eq_abel
        (stableFarPrimeLogPhase tau)
        (stableFarFrozenWindowProfile A B) K hK
        (fun n hn => stableFarFrozenWindowProfile_eq_pred_of_not_prime A B hn)
    _ = stableFarFrozenWindowProfile A B 0 -
        stableFarPrimeLogPhase tau K * stableFarFrozenWindowProfile A B K +
        ∑ n ∈ Finset.Ico 1 K,
          (stableFarPrimeLogPhase tau (n + 1) -
            stableFarPrimeLogPhase tau n) *
            stableFarFrozenWindowProfile A B n := by simp

/-- **Zero-frequency cancellation.**  All phase-gradient leakage disappears,
leaving the exact signed endpoint telescope. -/
theorem frozenPrimeUniverse_zeroFrequency_telescope
    (A B K : ℕ) (hK : 1 ≤ K) (hAB : A ≤ B) :
    (∑ p ∈ primesUpTo K,
      ((frozenPrimeUniverseWindowMass (primesUpTo (p - 1))
        (A / p) (B / p) : ℤ) : ℂ)) =
      stableFarFrozenWindowProfile A B 0 -
        stableFarFrozenWindowProfile A B K := by
  have h := frozenPrimeUniverse_logFrequency_telescope 0 A B K hK hAB
  simpa using h

/-! ## Specialize to the owner-first stable-far geometry -/

/-- There is no prime at or below one, so the owner-first high-prime set starts
from the full prime prefix. -/
theorem frozenPrimeUniverseHighPrimeSet_one_eq_primesUpTo (K : ℕ) :
    frozenPrimeUniverseHighPrimeSet 1 K = primesUpTo K := by
  unfold frozenPrimeUniverseHighPrimeSet
  have h1 : primesUpTo 1 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rcases mem_primesUpTo.mp hp with ⟨hpPrime, hpLe⟩
    have hp2 := hpPrime.two_le
    omega
  rw [h1, Finset.sdiff_empty]

/-- **Frequency form of the owner-first returned-window column.**

For fixed old owner `q` and far prime `p`, every returned-owner window is one
sample of the same log-frequency family.  The unweighted collapse is the
`tau=0` fibre; at general `tau`, all noncancellation is concentrated in the
explicit phase-gradient term. -/
theorem stableFar_ownerFirst_logFrequency_decomposition
    (tau : ℝ) (X q p : ℕ) (hq : q.Prime) (hp : p.Prime) :
    (∑ r ∈ frozenPrimeUniverseHighPrimeSet 1 (q - 1),
      stableFarPrimeLogPhase tau r *
        ((frozenPrimeUniverseWindowMass (primesUpTo (r - 1))
          (X / (q * q * p * r)) (X / (q * p * r)) : ℤ) : ℂ)) =
      stableFarFrozenWindowProfile
          (X / (q * q * p)) (X / (q * p)) 0 -
        stableFarPrimeLogPhase tau (q - 1) *
          stableFarFrozenWindowProfile
            (X / (q * q * p)) (X / (q * p)) (q - 1) +
        ∑ n ∈ Finset.Ico 1 (q - 1),
          (stableFarPrimeLogPhase tau (n + 1) -
            stableFarPrimeLogPhase tau n) *
            stableFarFrozenWindowProfile
              (X / (q * q * p)) (X / (q * p)) n := by
  have hq2 : 2 ≤ q := hq.two_le
  have hK : 1 ≤ q - 1 := by omega
  have hqq : q ≤ q * q := by
    simpa using Nat.mul_le_mul_left q hq.one_le
  have hden : q * p ≤ q * q * p := Nat.mul_le_mul_right p hqq
  have hdenPos : 0 < q * p := Nat.mul_pos hq.pos hp.pos
  have hAB : X / (q * q * p) ≤ X / (q * p) :=
    Nat.div_le_div_left hden hdenPos
  have hfreq := frozenPrimeUniverse_logFrequency_telescope tau
    (X / (q * q * p)) (X / (q * p)) (q - 1) hK hAB
  rw [frozenPrimeUniverseHighPrimeSet_one_eq_primesUpTo] 
  simpa [Nat.div_div_eq_div_mul, Nat.mul_assoc] using hfreq

end RHLean.Proof
