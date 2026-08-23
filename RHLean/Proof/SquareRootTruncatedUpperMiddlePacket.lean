import Mathlib
import RHLean.Analysis.PrimeSieveAbelIdentity
import RHLean.Analysis.SquareRootMiddleSequentialCoherence
import RHLean.Proof.LargePrimeTerminalFlipLayers

/-!
# Truncated upper-middle reciprocal packet

At the canonical square endpoint `X_R = R^2 - 1`, the complete post-root prime
fibre with reciprocal label `d = floor(X_R / q)` contributes `-M(d)`: the
untouched prime seat contributes `-1`, while its proper-multiple terminal flips
contribute `1 - M(d)`.  Thus the same-sign upper block `d = 1` and the middle
layers `d >= 2` must be kept in one signed object.

This file defines the truncated packet

`U_R(K) = - sum_{1 <= d <= K} N_R(d) M(d)`,

where `N_R(d)` is the exact reciprocal-layer prime population.  It then gives a
finite Abel form without any analytic estimate.  The post-root prime prefix is
clipped at the root,

`P_R(d) = pi(max R (floor(X_R/d))) - pi(R)`,

so that on every quotient-support layer

`N_R(d) = P_R(d) - P_R(d+1)`.

The repository's existing generic Abel theorem therefore gives

`U_R(K)
  = - sum_{1 <= d <= K} mu(d) P_R(d) + M(K) P_R(K+1)`.

For `K >= 1`, separating the unit term makes the upper boundary explicit:

`U_R(K)
  = -P_R(1) - sum_{2 <= d <= K} mu(d) P_R(d)
      + M(K) P_R(K+1)`.

No bound on `K`, on `U_R(K)`, on prime counts, or on Mertens values is asserted.
The point is to preserve the exact upper/middle cancellation before any norm or
completion of the reciprocal coordinate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- Clipped post-root prime prefix at reciprocal depth `d`.

The `max R` is essential at the terminal quotient boundary.  It makes this
prefix zero once the reciprocal cutoff has fallen to the root and ensures that
successive differences agree exactly with the repository's clipped reciprocal
prime intervals. -/
def squareRootPostRootPrimePrefix (R d : ℕ) : ℂ :=
  primeSievePrefixPrimeCount (max R (squareRootEndpoint R / d)) -
    primeSievePrefixPrimeCount R

/-- The signed upper-plus-middle packet through reciprocal layer `K`.

The leading minus sign is the actual post-root source sign: one complete prime
fibre contributes `-M(d)`, not the proper-multiple flip mass `1-M(d)` by itself.
-/
def squareRootTruncatedUpperMiddlePacket (R K : ℕ) : ℂ :=
  -∑ d ∈ Finset.Icc 1 K,
    primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
      mertensSummatory d

/-- Every reciprocal layer strictly below the root support is the forward
difference of the clipped post-root prime prefix. -/
theorem squareRoot_reciprocalPrimeCount_eq_postRootPrefix_diff
    {R d : ℕ} (hR : 1 ≤ R) (hd1 : 1 ≤ d) (hdR : d < R) :
    primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d =
      squareRootPostRootPrimePrefix R d -
        squareRootPostRootPrimePrefix R (d + 1) := by
  have htop : squareRootEndpoint R / (R + 1) = R - 1 :=
    squareRootQuotientSupportTop_eq_pred R hR
  have hdSupport :
      d ∈ primeSieveQuotientSupport R (squareRootEndpoint R) := by
    unfold primeSieveQuotientSupport
    rw [htop]
    exact Finset.mem_Icc.mpr ⟨hd1, by omega⟩
  have hRlt : R < squareRootEndpoint R / d :=
    lt_div_of_mem_primeSieveQuotientSupport hdSupport
  have hmono :
      squareRootEndpoint R / (d + 1) ≤ squareRootEndpoint R / d :=
    Nat.div_le_div_left (by omega) (by omega)
  have hle :
      primeSieveReciprocalLower R (squareRootEndpoint R) d ≤
        primeSieveReciprocalUpper (squareRootEndpoint R) d := by
    unfold primeSieveReciprocalLower primeSieveReciprocalUpper
    exact max_le hRlt.le hmono
  rw [primeSieveReciprocalPrimeCount_eq_sub R (squareRootEndpoint R) d hle]
  unfold squareRootPostRootPrimePrefix
    primeSieveReciprocalLower primeSieveReciprocalUpper
  rw [max_eq_right hRlt.le]
  ring

/-- The truncated upper-middle packet is an exact finite Abel packet.

The theorem is restricted only by `K < R`, i.e. by the physical reciprocal
support.  No estimate is used. -/
theorem squareRootTruncatedUpperMiddlePacket_eq_abel
    (R K : ℕ) (hR : 1 ≤ R) (hK : K < R) :
    squareRootTruncatedUpperMiddlePacket R K =
      -(∑ d ∈ Finset.Icc 1 K,
          (((μ d : ℤ) : ℂ)) * squareRootPostRootPrimePrefix R d) +
        mertensSummatory K * squareRootPostRootPrimePrefix R (K + 1) := by
  have hrewrite :
      (∑ d ∈ Finset.Icc 1 K,
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d) =
        ∑ d ∈ Finset.Icc 1 K,
          mertensSummatory d *
            (squareRootPostRootPrimePrefix R d -
              squareRootPostRootPrimePrefix R (d + 1)) := by
    apply Finset.sum_congr rfl
    intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, hdK⟩
    rw [squareRoot_reciprocalPrimeCount_eq_postRootPrefix_diff
      hR hd1 (hdK.trans_lt hK)]
    ring
  unfold squareRootTruncatedUpperMiddlePacket
  rw [hrewrite,
    sum_mertensSummatory_mul_forwardDifference]
  ring

/-- Abel form with the unit term separated.  This is the exact algebraic form
that keeps the large upper boundary inside the same packet as the shallow
middle corrections. -/
theorem squareRootTruncatedUpperMiddlePacket_eq_upper_add_abelMiddle
    (R K : ℕ) (hR : 1 ≤ R) (hK1 : 1 ≤ K) (hKR : K < R) :
    squareRootTruncatedUpperMiddlePacket R K =
      -squareRootPostRootPrimePrefix R 1 -
        (∑ d ∈ Finset.Icc 2 K,
          (((μ d : ℤ) : ℂ)) * squareRootPostRootPrimePrefix R d) +
        mertensSummatory K * squareRootPostRootPrimePrefix R (K + 1) := by
  rw [squareRootTruncatedUpperMiddlePacket_eq_abel R K hR hKR]
  have hset :
      Finset.Icc 1 K = ({1} : Finset ℕ) ∪ Finset.Icc 2 K := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({1} : Finset ℕ) (Finset.Icc 2 K) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rw [Finset.mem_singleton] at hd1
    subst d
    simp at hd2
  rw [hset, Finset.sum_union hdisj]
  simp [ArithmeticFunction.moebius_apply_one]
  ring

/-- The first reciprocal layer is exactly the same-sign top-prime block, with
its source sign.  This is the guardrail against treating the middle section as a
self-cancelling object. -/
theorem squareRootTruncatedUpperMiddlePacket_one_eq_neg_topCard
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootTruncatedUpperMiddlePacket R 1 =
      -((squareRootTopFibrePrimes R).card : ℂ) := by
  unfold squareRootTruncatedUpperMiddlePacket
  rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) by decide]
  simp only [Finset.sum_singleton]
  rw [squareRootReciprocalPrimeCount_one_eq_topCard R hR]
  have hM1 : mertensSummatory 1 = 1 := by
    rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
    simp [cofactorMobiusPrefixMass, canonicalMoebiusWeight]
  rw [hM1]
  ring

end RHLean.Proof
