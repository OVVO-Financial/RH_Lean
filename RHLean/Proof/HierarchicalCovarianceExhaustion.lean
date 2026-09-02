import Mathlib
import RHLean.Analysis.SquareRootPrimeCountGap
import RHLean.Analysis.SquareRootMiddleSequentialCoherence
import RHLean.Proof.LargePrimeTerminalFlipLayers
import RHLean.Proof.SquareRootPredecessorPrimeCells

/-!
# Hierarchical covariance exhaustion

This file records the exact multi-prime hierarchy behind the square-root
post-root corridor.  It deliberately stays before norms and makes no
independence or random-sign assumption.

At `X_R = R^2 - 1`, the first parity face is the prime-2 face.  Pairing the
middle prime population against the untouched top-prime population leaves the
exact geometric count gap

`middle - top = 2*pi(X_R/2) - pi(X_R) - pi(R)`.

The remaining contribution is not another free same-sign block: it is the
lower-scale reciprocal hierarchy

`- sum_{3 <= d < R} N_R(d) * M(d)`.

The `d = 2` layer has disappeared exactly because `M(2)=0`.  Thus the complete
upper-prime signed state is a prime-count difference plus only deeper Euler
faces.

Two further facts encode the shrinking leverage of later prime injections:

* the predecessor state of a fresh prime `p` is evaluated only at the child
  cutoff `floor(k/p)`, and these cutoffs decrease as the prime grows;
* once the complete predecessor Boolean cube fits, the corresponding signed
  predecessor mass is exactly zero.

Finally, nonsquarefree cofactors contribute exactly zero under the terminal
large-prime flip.  This is the pointwise structural fact behind the familiar
~39.2% zero density of the Moebius function; no asymptotic density input is used
in the theorem below.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

/-- The complete post-root upper-prime state after putting the untouched
`c = 1` top-prime seats back together with the genuine middle terminal flips. -/
def squareRootHierarchicalUpperPrimeMass (R : ℕ) : ℂ :=
  squareRootMiddleTerminalFlipMass R -
    ((squareRootTopFibrePrimes R).card : ℂ)

private theorem hierarchical_mertensSummatory_two : mertensSummatory 2 = 0 := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
  unfold cofactorMobiusPrefixMass
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide]
  simp [canonicalMoebiusWeight,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]

/-- **Hierarchical covariance exhaustion.**  The entire upper-prime signed
state is the first prime-2 population gap minus only the genuinely deeper
reciprocal Euler layers.  The potentially coherent `d = 2` layer is absent
*exactly*, because `M(2)=0`.

This is the deterministic multi-prime refinement of the one-for-one
middle/top picture: the first face is a pure difference of prime populations,
while every later face is already weighted by a completed lower-scale Mertens
state.  No absolute values are taken. -/
theorem squareRootHierarchicalCovarianceExhaustion
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootHierarchicalUpperPrimeMass R =
      squareRootMiddleTopPrimeCountGapMass R -
        ∑ d ∈ Finset.Icc 3 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d := by
  have hset :
      Finset.Icc 2 (R - 1) =
        ({2} : Finset ℕ) ∪ Finset.Icc 3 (R - 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj :
      Disjoint ({2} : Finset ℕ) (Finset.Icc 3 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro d hd2 hd3
    rw [Finset.mem_singleton] at hd2
    subst d
    simp at hd3
  unfold squareRootHierarchicalUpperPrimeMass
    squareRootMiddleTerminalFlipMass
    squareRootMiddleTopPrimeCountGapMass
  rw [squareRootMiddleMertensTail_eq_reciprocalPrimeLayers R hR,
    hset, Finset.sum_union hdisj]
  simp [hierarchical_mertensSummatory_two]
  ring

/-- The same exhaustion with the first face written as the literal prime-count
difference

`2*pi(X_R/2) - pi(X_R) - pi(R)`.
-/
theorem squareRootHierarchicalCovarianceExhaustion_primeCounting
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootHierarchicalUpperPrimeMass R =
      (2 * (Nat.primeCounting (squareRootEndpoint R / 2) : ℂ) -
          (Nat.primeCounting (squareRootEndpoint R) : ℂ) -
          (Nat.primeCounting R : ℂ)) -
        ∑ d ∈ Finset.Icc 3 (R - 1),
          primeSieveReciprocalPrimeCount R (squareRootEndpoint R) d *
            mertensSummatory d := by
  rw [squareRootHierarchicalCovarianceExhaustion R hR]
  have hgap :
      squareRootMiddleTopPrimeCountGapMass R =
        ((squareRootMiddleTopPrimeCountGap R : ℤ) : ℂ) := by
    unfold squareRootMiddleTopPrimeCountGapMass
    rw [squareRootMiddleTopPrimeCountGap_eq_card_sub R hR]
    push_cast
  rw [hgap]
  unfold squareRootMiddleTopPrimeCountGap
  push_cast
  ring

/-- **Later primes have smaller child cutoffs.**  This is the literal support
contraction behind the hierarchy: if `p <= q`, then the old state inspected by
`q` is no deeper than the one inspected by `p`.  It is a support statement,
not a claim that the signed masses are monotone. -/
theorem hierarchicalChildCutoff_antitone
    {p q k : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    k / q ≤ k / p := by
  apply (Nat.le_div_iff_mul_le hp).2
  calc
    (k / q) * p ≤ (k / q) * q := Nat.mul_le_mul_left (k / q) hpq
    _ ≤ k := Nat.div_mul_le_self k q

/-- **Exact exhaustion after a complete predecessor cube.**  Once all old
Boolean faces below `p` fit inside the child cutoff, the fresh-prime correction
is identically zero. -/
theorem hierarchicalPredecessorMass_eq_zero_of_complete_old_cube
    {p k : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hfit : p * primeFaceProduct (primesUpTo (p - 1)) ≤ k) :
    predecessorPrimeMass p k = 0 :=
  predecessorPrimeMass_eq_zero_of_predPrimeCube_complete hp hp2 hfit

/-- **Moebius-zero seats are removed pointwise.**  A nonsquarefree lower
cofactor remains zero after adjoining a fresh large prime.  This is the exact
construction-level zero mechanism; no density estimate is needed. -/
theorem hierarchicalTerminalFlip_eq_zero_of_cofactor_not_squarefree
    {X c q : ℕ} (hq : q.Prime) (hqRoot : Nat.sqrt X < q)
    (hcpos : 0 < c) (hcqX : c * q ≤ X)
    (hnsq : ¬ Squarefree c) :
    μ (c * q) = 0 :=
  moebius_mul_largePrime_eq_zero_of_cofactor_not_squarefree
    hq hqRoot hcpos hcqX hnsq

end RHLean.Proof

end
