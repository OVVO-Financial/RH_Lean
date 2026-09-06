import Mathlib
import RHLean.Proof.MutableSupportBound
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Proof.PrimeCombReciprocalBandCancellation

/-!
# Vanishing transition relevance

This module formalizes the final deterministic asymptotic transfer.  A transition
support `U n` is measured on the linear scale of the square block by

```text
card (U n) / n.
```

If the settled complement has zero Möbius mass, PR #153 gives
`|Δ_n| <= card (U n)`.  Dividing by `n` shows that vanishing transition relevance
forces the normalized square-block discrepancy to vanish as well.

The arithmetic construction of the genuine severed transition support, and the
proof that its relevance vanishes, remain separate inputs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators Topology
open Filter

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- Transition relevance on the natural linear scale of the square block. -/
def transitionRelevance (U : ℕ → Finset ℕ) (n : ℕ) : ℝ :=
  ((U n).card : ℝ) / (n : ℝ)

/-- Absolute square-block discrepancy normalized by the same linear scale. -/
def normalizedSquareBlockDiscrepancy (n : ℕ) : ℝ :=
  |(squareBlockMoebius n : ℝ)| / (n : ℝ)

/-- Epsilon/eventually formulation of vanishing transition relevance. -/
def TransitionRelevanceVanishes (U : ℕ → Finset ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, transitionRelevance U n ≤ ε

/-- Epsilon/eventually formulation of `Δ_n = o(n)`. -/
def SquareBlockDiscrepancyVanishes : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, normalizedSquareBlockDiscrepancy n ≤ ε

/-- Pointwise transfer: the normalized block discrepancy is bounded by transition
relevance whenever the settled complement has zero Möbius mass. -/
theorem normalizedSquareBlockDiscrepancy_le_transitionRelevance
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    {n : ℕ} (hn : 0 < n) :
    normalizedSquareBlockDiscrepancy n ≤ transitionRelevance U n := by
  have hInt : |squareBlockMoebius n| ≤ ((U n).card : ℤ) :=
    abs_squareBlockMoebius_le_mutable_card (hU n) (hinterior n)
  have hReal : |(squareBlockMoebius n : ℝ)| ≤ ((U n).card : ℝ) := by
    exact_mod_cast hInt
  unfold normalizedSquareBlockDiscrepancy transitionRelevance
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (div_le_div_iff_of_pos_right hnReal).2 hReal

/-- Vanishing transition relevance forces `Δ_n = o(n)` in epsilon/eventually
form.  No further cancellation estimate is used. -/
theorem squareBlockDiscrepancyVanishes_of_transitionRelevanceVanishes
    (U : ℕ → Finset ℕ)
    (hU : ∀ n, U n ⊆ squareBlockInterval n)
    (hinterior : ∀ n, ∑ m ∈ squareBlockInterval n \ U n, μ m = 0)
    (hvanish : TransitionRelevanceVanishes U) :
    SquareBlockDiscrepancyVanishes := by
  intro ε hε
  have hrel := hvanish ε hε
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    omega
  filter_upwards [hrel, hpos] with n hnRel hnPos
  exact le_trans
    (normalizedSquareBlockDiscrepancy_le_transitionRelevance U hU hinterior hnPos)
    hnRel

/-! ## Ordered prime replication as deterministic Möbius transport

The fixed lower Möbius prefix is not resampled by post-root primes.  This
section identifies the user's cofactor-first response with the repository's
existing high transport and therefore with its exact dyadic compression.
-/

/-- Complete signed replication response of the fixed prefix at the square
endpoint `X_R = R^2 - 1`. -/
def orderedPrimeReplicationResponse (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Ico 1 R,
    canonicalMoebiusWeight c *
      ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
        (Nat.primeCounting R : ℂ))

/-- The `c=1,2` channels cancel everything except the inert top-prime block. -/
theorem orderedPrimeReplication_firstTwo_eq_topCard
    (R : ℕ) :
    (∑ c ∈ ({1, 2} : Finset ℕ),
      canonicalMoebiusWeight c *
        ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
          (Nat.primeCounting R : ℂ))) =
      ((squareRootTopFibrePrimes R).card : ℂ) := by
  have hmu1 : canonicalMoebiusWeight 1 = 1 := by
    simp [canonicalMoebiusWeight]
  have hmu2 : canonicalMoebiusWeight 2 = -1 := by
    unfold canonicalMoebiusWeight
    rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  have htop := squareRootTopFibrePrimes_card_add_primeCounting_half R
  have htopC :
      ((squareRootTopFibrePrimes R).card : ℂ) +
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) =
        (Nat.primeCounting (squareRootEndpoint R) : ℂ) := by
    exact_mod_cast htop
  have htopDiff :
      (Nat.primeCounting (squareRootEndpoint R) : ℂ) -
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) =
        ((squareRootTopFibrePrimes R).card : ℂ) := by
    symm
    exact (eq_sub_iff_add_eq).2 htopC
  calc
    (∑ c ∈ ({1, 2} : Finset ℕ),
      canonicalMoebiusWeight c *
        ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
          (Nat.primeCounting R : ℂ))) =
        (Nat.primeCounting (squareRootEndpoint R) : ℂ) -
          (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) := by
      simp [hmu1, hmu2]
      ring
    _ = ((squareRootTopFibrePrimes R).card : ℂ) := htopDiff

/-- **Exact global identification.**  The full ordered replication response is
exactly the existing cofactor-first transport.  No iid or probabilistic input
appears. -/
theorem orderedPrimeReplicationResponse_eq_transport
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationResponse R = squareRootTransportCofactorFirst R := by
  classical
  let lowC : Finset ℕ := Finset.Icc 3 (R - 1)
  have hset :
      Finset.Ico 1 R = ({1, 2} : Finset ℕ) ∪ lowC := by
    ext c
    simp only [lowC, Finset.mem_Ico, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hdisj : Disjoint ({1, 2} : Finset ℕ) lowC := by
    rw [Finset.disjoint_left]
    intro c hc12 hclow
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc12
    rcases Finset.mem_Icc.mp hclow with ⟨hc3, _hcTop⟩
    omega
  have hmiddle := squareRootMiddleMertensTail_eq_swappedPrimeCounting R hR
  unfold orderedPrimeReplicationResponse
  rw [hset, Finset.sum_union hdisj,
    orderedPrimeReplication_firstTwo_eq_topCard R]
  change ((squareRootTopFibrePrimes R).card : ℂ) +
      (∑ c ∈ Finset.Icc 3 (R - 1),
        canonicalMoebiusWeight c *
          ((Nat.primeCounting (squareRootEndpoint R / c) : ℂ) -
            (Nat.primeCounting R : ℂ))) = squareRootTransportCofactorFirst R
  rw [← hmiddle, squareRootTransportCofactorFirst_eq_primeFirst,
    squareRootTransportPrimeFirst_eq_middleMertensTail_add_topCard R hR]

/-- **Global deterministic non-iid compression.**  The whole ordered prime
replication of the fixed Möbius prefix is exactly the repository's odd dyadic
boundary mass. -/
theorem orderedPrimeReplicationResponse_eq_dyadicBoundaryMass
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationResponse R =
      squareRootDyadicTransportBoundaryMass R := by
  rw [orderedPrimeReplicationResponse_eq_transport R hR,
    squareRootTransportCofactorFirst_eq_dyadicBoundaryMass]

end RHLean.Proof
