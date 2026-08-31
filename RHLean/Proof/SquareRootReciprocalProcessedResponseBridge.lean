import Mathlib
import RHLean.Proof.SquareRootBornPostTailLowPrimeRemainder
import RHLean.Proof.SquareRootLowPrimeHighResponseMonotone

/-!
# Reciprocal depth versus processed response: the common moving boundary

The reciprocal packet and the literal response seats do **not** have the same
support.  For `c ≤ K` the high response is

`HighResponse R K j c = (N_R(K) - j) + P_R(K+1)`,

which by the Abel telescope `N_R(K) + P_R(K+1) = P_R(K)` is the single number

`B_{R,K,j} = P_R(K) - j`,

independent of `c`.  So the response seats see only reciprocal depths at least
`K`, while depths `1, …, K-1` — the top fibre among them — have already been
eliminated into the packet.

This file names the eliminated part,

`A_{R,K,j}(c) = P_R(c) - B_{R,K,j}`  for `c ≤ K`,  and `0` beyond,

and proves the exact conservation law

`A_{R,K,j}(c) + HighResponse R K j c = P_R(c)`.

Read as flux and inventory: `P_R(c)` is the total post-root capacity of the
cofactor, `HighResponse` is what remains as literal seats at the current moving
boundary, and `A` is what has already crossed and been compressed into the
packet.  The top block lives in `A_{R,K,j}(1)`, which is why it is not a vertex
of the seat carrier.

No estimate, PNT input, or asymptotic appears here: everything is the finite
Abel telescope plus antitonicity of the post-root prefix.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The moving common boundary of the high response at partial crossing depth
`(K, j)`.  For every shallow cofactor the high response equals this one number. -/
def squareRootProcessedResponseBoundary (R K j : ℕ) : ℕ :=
  squareRootPostRootPrimePrefixCard R K - j

/-- Post-root capacity of a cofactor that has already crossed the moving
boundary, i.e. been eliminated into the reciprocal packet. -/
def squareRootProcessedPostRootCapacity (R K j c : ℕ) : ℕ :=
  if c ≤ K then
    squareRootPostRootPrimePrefixCard R c - squareRootProcessedResponseBoundary R K j
  else 0

/-- **The high response of a shallow cofactor is the moving boundary.**
This is the Abel telescope `N_R(K) + P_R(K+1) = P_R(K)` in response
coordinates, and it is where the `c`-independence comes from. -/
theorem squareRootBornPostTailHighResponse_eq_processedResponseBoundary
    (R K j c : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hcK : c ≤ K) :
    squareRootBornPostTailHighResponse R K j c =
      squareRootProcessedResponseBoundary R K j := by
  have hlayer :=
    squareRootReciprocalPrimeLayerCard_add_postRootPrimePrefixCard R K hR hK hKR
  unfold squareRootBornPostTailHighResponse squareRootProcessedResponseBoundary
  rw [if_pos hcK]
  omega

/-- The moving boundary never exceeds the capacity of a shallower cofactor. -/
theorem squareRootProcessedResponseBoundary_le_prefixCard
    (R K j c : ℕ) (hc : 1 ≤ c) (hcK : c ≤ K) :
    squareRootProcessedResponseBoundary R K j ≤
      squareRootPostRootPrimePrefixCard R c := by
  have hanti :=
    squareRootPostRootPrimePrefixCard_antitone (R := R) (a := c) (b := K) hc hcK
  unfold squareRootProcessedResponseBoundary
  omega

/-- **Exact conservation between eliminated flux and remaining inventory.**

`already crossed + still seated = total post-root capacity`. -/
theorem squareRootProcessedPostRootCapacity_add_highResponse_eq_prefixCard
    (R K j c : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hc : 1 ≤ c) (hcK : c ≤ K) :
    squareRootProcessedPostRootCapacity R K j c +
        squareRootBornPostTailHighResponse R K j c =
      squareRootPostRootPrimePrefixCard R c := by
  have hhigh :=
    squareRootBornPostTailHighResponse_eq_processedResponseBoundary
      R K j c hR hK hKR hj hcK
  have hble := squareRootProcessedResponseBoundary_le_prefixCard R K j c hc hcK
  unfold squareRootProcessedPostRootCapacity
  rw [if_pos hcK, hhigh]
  omega

/-- Closed form of the eliminated capacity on the shallow range. -/
theorem squareRootProcessedPostRootCapacity_eq_sub
    (R K j c : ℕ) (hcK : c ≤ K) :
    squareRootProcessedPostRootCapacity R K j c =
      squareRootPostRootPrimePrefixCard R c -
        (squareRootPostRootPrimePrefixCard R K - j) := by
  unfold squareRootProcessedPostRootCapacity squareRootProcessedResponseBoundary
  rw [if_pos hcK]

/-- At the crossing depth itself the eliminated capacity is exactly the number
of already-admitted layer primes. -/
theorem squareRootProcessedPostRootCapacity_self
    (R K j : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K) :
    squareRootProcessedPostRootCapacity R K j K = j := by
  have hlayer :=
    squareRootReciprocalPrimeLayerCard_add_postRootPrimePrefixCard R K hR hK hKR
  rw [squareRootProcessedPostRootCapacity_eq_sub R K j K (le_refl K)]
  omega

/-- With no layer prime admitted the boundary is the full depth-`K` prefix, so
nothing at depth `K` has been eliminated yet. -/
theorem squareRootProcessedPostRootCapacity_zero
    (R K : ℕ) (hK : 1 ≤ K) :
    squareRootProcessedPostRootCapacity R K 0 K = 0 := by
  rw [squareRootProcessedPostRootCapacity_eq_sub R K 0 K (le_refl K)]
  omega

end RHLean.Proof
