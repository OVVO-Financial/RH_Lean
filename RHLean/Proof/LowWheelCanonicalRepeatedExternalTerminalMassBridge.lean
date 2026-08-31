import Mathlib
import RHLean.Analysis.SquareRootTransportTopFibreNoGo
import RHLean.Analysis.SquareRootCanonicalRoughCovariance

/-!
# Prime-deletion Hall obstruction and rough-partner fresh-prime difference

The canonically oriented downcross carrier invites a graph-theoretic pairing:
connect opposite Mobius signs when one tail integer is obtained from the other
by adding or deleting one prime.  The actual crossing-prime deletion graph is a
subgraph of this more generous one-prime graph.

This module records the obstruction before attempting any Hall estimate.  Every
prime in the inert top half `(X_R / 2, X_R]`, where `X_R = R^2 - 1`, is an
isolated negative vertex even in the enlarged graph.  Hence every crossing-prime
deletion graph has Hall defect at least the cardinality of the complete top
prime fibre.

The second section attacks the remaining Othello/Euler question directly: how
the canonical rough-prime partner multiplicity changes under a fresh-prime
extension `c -> c*p`.  The reciprocal-depth sum collapses exactly to one clipped
prime window.  A fresh-prime move changes both ends of that window, so the
response is not a nested capacity.  The signed parent/child contribution is an
exact difference of an upper prime-count boundary and a lower prime-count
boundary.  A concrete finite witness shows that partners can simultaneously
enter at the lower end and leave at the upper end.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

namespace CrossingPrimeDeletionGraph

/-- Negative nonzero-Mobius vertices in the square-root Mertens tail. -/
def squareRootTailNegativePart (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter fun n => μ n = -1

/-- Positive nonzero-Mobius vertices in the square-root Mertens tail. -/
def squareRootTailPositivePart (R : ℕ) : Finset ℕ :=
  (Finset.Ioc R (squareRootEndpoint R)).filter fun n => μ n = 1

/-- Enlarged one-prime adjacency on opposite signs in the Mertens tail.

The intended crossing-prime deletion graph is a subgraph: here we allow *any*
prime insertion/deletion which stays in the tail.  Proving isolation in this
supergraph is therefore stronger than proving it for the canonical crossing
move alone. -/
def OnePrimeTailAdjacent (R n m : ℕ) : Prop :=
  n ∈ squareRootTailNegativePart R ∧
    m ∈ squareRootTailPositivePart R ∧
      ∃ p : ℕ, p.Prime ∧ (n = p * m ∨ m = p * n)

/-- Positive neighbors of a set of negative tail vertices. -/
def onePrimeTailNeighbors (R : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (squareRootTailPositivePart R).filter fun m =>
    ∃ n ∈ S, OnePrimeTailAdjacent R n m

/-- Hall deficiency of one negative subset. -/
def onePrimeTailHallDefectAt (R : ℕ) (S : Finset ℕ) : ℕ :=
  S.card - (onePrimeTailNeighbors R S).card

/-- Maximum Hall deficiency over all negative subsets. -/
noncomputable def onePrimeTailHallDefect (R : ℕ) : ℕ :=
  ((squareRootTailNegativePart R).powerset.image
      (onePrimeTailHallDefectAt R)).max'
    (by
      refine ⟨onePrimeTailHallDefectAt R ∅, ?_⟩
      exact Finset.mem_image.mpr
        ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), rfl⟩)

/-- Top-half primes are genuine negative vertices of the Mertens tail. -/
theorem squareRootTopFibrePrimes_subset_negative
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootTopFibrePrimes R ⊆ squareRootTailNegativePart R := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
  rcases Finset.mem_Ioc.mp hqIoc with ⟨hqHalf, hqX⟩
  have hmul : R * 2 ≤ squareRootEndpoint R := by
    have hRR : 3 * R ≤ R * R := Nat.mul_le_mul hR (le_refl R)
    have hsq : squareRootEndpoint R = R * R - 1 := by
      unfold squareRootEndpoint
      rw [pow_two]
    rw [hsq]
    omega
  have hhalf : R ≤ squareRootEndpoint R / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 hmul
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨hhalf.trans_lt hqHalf, hqX⟩, ?_⟩
  simpa using ArithmeticFunction.moebius_apply_prime hqPrime

/-- **Top-prime isolation.**  A top-half prime has no opposite-sign neighbor
obtained by inserting or deleting one prime while remaining in the tail.

Deletion cannot factor the prime nontrivially.  Insertion cannot remain below
`X_R`, since every inserted prime is at least `2` and `q > X_R / 2`. -/
theorem squareRootTopFibrePrimes_neighbors_eq_empty
    (R : ℕ) (hR : 3 ≤ R) :
    onePrimeTailNeighbors R (squareRootTopFibrePrimes R) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmPos, hneighbor⟩
  rcases hneighbor with ⟨q, hqTop, hadj⟩
  rcases hadj with ⟨_hqNeg, _hmPos, p, hpPrime, hrel⟩
  have hmTail := (Finset.mem_filter.mp hmPos).1
  rcases Finset.mem_Ioc.mp hmTail with ⟨hRm, hmX⟩
  rcases Finset.mem_filter.mp hqTop with ⟨hqIoc, hqPrime⟩
  rcases Finset.mem_Ioc.mp hqIoc with ⟨hqHalf, _hqX⟩
  rcases hrel with hqeq | hmeq
  · have hmdvd : m ∣ q := by
      refine ⟨p, ?_⟩
      simpa [Nat.mul_comm] using hqeq
    rcases hqPrime.eq_one_or_self_of_dvd m hmdvd with hm1 | hmq
    · omega
    · subst m
      have hp2 : 2 ≤ p := hpPrime.two_le
      have hqpos : 0 < q := hqPrime.pos
      nlinarith
  · have hXlt2q : squareRootEndpoint R < 2 * q := by
      have h :=
        (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).1 hqHalf
      simpa [Nat.mul_comm] using h
    have h2q_le_pq : 2 * q ≤ p * q := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hpPrime.two_le
    have hXltm : squareRootEndpoint R < m := by
      rw [hmeq]
      exact hXlt2q.trans_le h2q_le_pq
    omega

/-- The Hall deficiency witnessed by the top-prime set is exactly its full
cardinality. -/
theorem onePrimeTailHallDefectAt_topFibre
    (R : ℕ) (hR : 3 ≤ R) :
    onePrimeTailHallDefectAt R (squareRootTopFibrePrimes R) =
      (squareRootTopFibrePrimes R).card := by
  rw [onePrimeTailHallDefectAt,
    squareRootTopFibrePrimes_neighbors_eq_empty R hR]
  simp

/-- **Hall no-go.**  Even the enlarged one-prime graph has Hall defect at least
the entire inert top-prime population.  The canonical crossing-prime deletion
graph, having fewer edges, cannot do better on this witness. -/
theorem squareRootTopFibrePrimes_card_le_onePrimeTailHallDefect
    (R : ℕ) (hR : 3 ≤ R) :
    (squareRootTopFibrePrimes R).card ≤ onePrimeTailHallDefect R := by
  rw [← onePrimeTailHallDefectAt_topFibre R hR]
  unfold onePrimeTailHallDefect
  apply Finset.le_max'
  apply Finset.mem_image.mpr
  refine ⟨squareRootTopFibrePrimes R, ?_, rfl⟩
  exact Finset.mem_powerset.mpr
    (squareRootTopFibrePrimes_subset_negative R hR)

end CrossingPrimeDeletionGraph

namespace CanonicalRoughFreshPrimeDifference

/-- Prefix prime count clipped at the canonical roughness threshold. -/
private def clippedPrimePrefix (y x d : ℕ) : ℂ :=
  primeSievePrefixPrimeCount (max y (x / d))

/-- Every reciprocal prime layer is one forward difference of clipped prefix
prime counts.  This remains exact after the interval has clipped to empty. -/
theorem primeSieveReciprocalPrimeCount_eq_clippedPrefix_diff
    (y x d : ℕ) (hd : 1 ≤ d) :
    primeSieveReciprocalPrimeCount y x d =
      clippedPrimePrefix y x d - clippedPrimePrefix y x (d + 1) := by
  have hmono : x / (d + 1) ≤ x / d :=
    Nat.div_le_div_left (by omega) hd
  by_cases hy : y ≤ x / d
  · have hle : primeSieveReciprocalLower y x d ≤
        primeSieveReciprocalUpper x d := by
      unfold primeSieveReciprocalLower primeSieveReciprocalUpper
      exact max_le hy hmono
    rw [primeSieveReciprocalPrimeCount_eq_sub y x d hle]
    unfold clippedPrimePrefix primeSieveReciprocalLower
      primeSieveReciprocalUpper
    rw [max_eq_right hy]
  · have hxy : x / d < y := Nat.lt_of_not_ge hy
    have hnext : x / (d + 1) < y := hmono.trans_lt hxy
    have hle : primeSieveReciprocalUpper x d ≤
        primeSieveReciprocalLower y x d := by
      unfold primeSieveReciprocalUpper primeSieveReciprocalLower
      exact hxy.le.trans (le_max_left _ _)
    unfold primeSieveReciprocalPrimeCount primeSieveReciprocalInterval
    rw [Finset.Ioc_eq_empty_of_le hle]
    simp [clippedPrimePrefix, max_eq_left hxy.le, max_eq_left hnext.le]

private theorem sum_Icc_forwardDifference
    (f : ℕ → ℂ) (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, (f d - f (d + 1))) =
      f 1 - f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
      ring

/-- Lower endpoint of the complete canonical rough-prime partner window. -/
def squareRootCanonicalRoughPrimePartnerLower (R c : ℕ) : ℕ :=
  max (canonicalLargestPrimeFactor c)
    ((squareRootEndpoint R / c) / R)

/-- Upper endpoint of the complete canonical rough-prime partner window. -/
def squareRootCanonicalRoughPrimePartnerUpper (R c : ℕ) : ℕ :=
  max (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c)

/-- The literal prime window whose cardinality is the complete partner count. -/
def squareRootCanonicalRoughPrimePartnerWindow (R c : ℕ) : Finset ℕ :=
  (Finset.Ioc
      (squareRootCanonicalRoughPrimePartnerLower R c)
      (squareRootCanonicalRoughPrimePartnerUpper R c)).filter Nat.Prime

/-- **Partner-window collapse.**  The sum over every positive reciprocal depth
below `R` telescopes to one clipped prime-count interval. -/
theorem squareRootCanonicalRoughPrimePartnerCount_eq_prefixWindow
    {R c : ℕ} (hR : 1 ≤ R) :
    squareRootCanonicalRoughPrimePartnerCount R c =
      primeSievePrefixPrimeCount
          (squareRootCanonicalRoughPrimePartnerUpper R c) -
        primeSievePrefixPrimeCount
          (squareRootCanonicalRoughPrimePartnerLower R c) := by
  unfold squareRootCanonicalRoughPrimePartnerCount
    squareRootCanonicalRoughPrimeMultiplicity
  calc
    (∑ z ∈ Finset.Icc 1 (R - 1),
        primeSieveReciprocalPrimeCount
          (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z) =
      ∑ z ∈ Finset.Icc 1 (R - 1),
        (clippedPrimePrefix (canonicalLargestPrimeFactor c)
            (squareRootEndpoint R / c) z -
          clippedPrimePrefix (canonicalLargestPrimeFactor c)
            (squareRootEndpoint R / c) (z + 1)) := by
        apply Finset.sum_congr rfl
        intro z hz
        have hz1 : 1 ≤ z := (Finset.mem_Icc.mp hz).1
        rw [primeSieveReciprocalPrimeCount_eq_clippedPrefix_diff
          (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z hz1]
    _ = clippedPrimePrefix (canonicalLargestPrimeFactor c)
          (squareRootEndpoint R / c) 1 -
        clippedPrimePrefix (canonicalLargestPrimeFactor c)
          (squareRootEndpoint R / c) R := by
        have htel := sum_Icc_forwardDifference
          (clippedPrimePrefix (canonicalLargestPrimeFactor c)
            (squareRootEndpoint R / c)) (R - 1)
        rw [Nat.sub_add_cancel hR] at htel
        exact htel
    _ = primeSievePrefixPrimeCount
          (squareRootCanonicalRoughPrimePartnerUpper R c) -
        primeSievePrefixPrimeCount
          (squareRootCanonicalRoughPrimePartnerLower R c) := by
        simp [clippedPrimePrefix,
          squareRootCanonicalRoughPrimePartnerUpper,
          squareRootCanonicalRoughPrimePartnerLower]

/-- Cardinality form of the same collapse: the complete response is literally
one prime window, not an opaque sum of reciprocal layers. -/
theorem squareRootCanonicalRoughPrimePartnerCount_eq_windowCard
    {R c : ℕ} (hR : 1 ≤ R) :
    squareRootCanonicalRoughPrimePartnerCount R c =
      ((squareRootCanonicalRoughPrimePartnerWindow R c).card : ℂ) := by
  rw [squareRootCanonicalRoughPrimePartnerCount_eq_prefixWindow hR]
  let L := squareRootCanonicalRoughPrimePartnerLower R c
  let U := squareRootCanonicalRoughPrimePartnerUpper R c
  have hdiv : (squareRootEndpoint R / c) / R ≤ squareRootEndpoint R / c :=
    Nat.div_le_self _ _
  have hLU : L ≤ U := by
    dsimp [L, U, squareRootCanonicalRoughPrimePartnerLower,
      squareRootCanonicalRoughPrimePartnerUpper]
    exact max_le_max_left _ hdiv
  have hsplit := Finset.sum_Ioc_consecutive
    (f := primeSievePrimeIndicator) (Nat.zero_le L) hLU
  have hinterval :
      primeSievePrefixPrimeCount U - primeSievePrefixPrimeCount L =
        ∑ q ∈ Finset.Ioc L U, primeSievePrimeIndicator q := by
    unfold primeSievePrefixPrimeCount at hsplit ⊢
    linear_combination hsplit
  rw [show squareRootCanonicalRoughPrimePartnerUpper R c = U by rfl,
    show squareRootCanonicalRoughPrimePartnerLower R c = L by rfl,
    hinterval]
  unfold squareRootCanonicalRoughPrimePartnerWindow
  rw [show squareRootCanonicalRoughPrimePartnerLower R c = L by rfl,
    show squareRootCanonicalRoughPrimePartnerUpper R c = U by rfl,
    ← Finset.sum_filter]
  simp [primeSievePrimeIndicator]

/-- A fresh prime becomes the canonical largest prime factor of its arithmetic
child, so both clipped partner-window endpoints have an explicit child form. -/
theorem squareRootCanonicalRoughPrimePartnerUpper_mul_freshPrime
    {R c p : ℕ} (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughPrimePartnerUpper R (c * p) =
      max p (squareRootEndpoint R / (c * p)) := by
  unfold squareRootCanonicalRoughPrimePartnerUpper
  rw [canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hp hrough]

theorem squareRootCanonicalRoughPrimePartnerLower_mul_freshPrime
    {R c p : ℕ} (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughPrimePartnerLower R (c * p) =
      max p ((squareRootEndpoint R / (c * p)) / R) := by
  unfold squareRootCanonicalRoughPrimePartnerLower
  rw [canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hp hrough]

/-- Prime-count mass lost at the upper endpoint under `c -> c*p`. -/
def squareRootCanonicalRoughFreshPrimeUpperBoundary
    (R c p : ℕ) : ℂ :=
  primeSievePrefixPrimeCount
      (squareRootCanonicalRoughPrimePartnerUpper R c) -
    primeSievePrefixPrimeCount
      (squareRootCanonicalRoughPrimePartnerUpper R (c * p))

/-- Signed displacement of the lower endpoint under `c -> c*p`.  This quantity
need not be nonnegative: lower partners may enter as reciprocal depth rescales. -/
def squareRootCanonicalRoughFreshPrimeLowerBoundary
    (R c p : ℕ) : ℂ :=
  primeSievePrefixPrimeCount
      (squareRootCanonicalRoughPrimePartnerLower R c) -
    primeSievePrefixPrimeCount
      (squareRootCanonicalRoughPrimePartnerLower R (c * p))

/-- **Exact fresh-prime finite difference.**  The response difference is an
upper prime-count boundary minus a lower prime-count boundary. -/
theorem squareRootCanonicalRoughPrimePartnerCount_sub_mul_eq_boundaries
    {R c p : ℕ} (hR : 1 ≤ R) :
    squareRootCanonicalRoughPrimePartnerCount R c -
        squareRootCanonicalRoughPrimePartnerCount R (c * p) =
      squareRootCanonicalRoughFreshPrimeUpperBoundary R c p -
        squareRootCanonicalRoughFreshPrimeLowerBoundary R c p := by
  rw [squareRootCanonicalRoughPrimePartnerCount_eq_prefixWindow hR,
    squareRootCanonicalRoughPrimePartnerCount_eq_prefixWindow hR]
  unfold squareRootCanonicalRoughFreshPrimeUpperBoundary
    squareRootCanonicalRoughFreshPrimeLowerBoundary
  ring

/-- Explicit fresh-prime form of the same two-boundary law. -/
theorem squareRootCanonicalRoughPrimePartnerCount_sub_mul_freshPrime
    {R c p : ℕ} (hR : 1 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughPrimePartnerCount R c -
        squareRootCanonicalRoughPrimePartnerCount R (c * p) =
      (primeSievePrefixPrimeCount
          (squareRootCanonicalRoughPrimePartnerUpper R c) -
        primeSievePrefixPrimeCount
          (max p (squareRootEndpoint R / (c * p)))) -
      (primeSievePrefixPrimeCount
          (squareRootCanonicalRoughPrimePartnerLower R c) -
        primeSievePrefixPrimeCount
          (max p ((squareRootEndpoint R / (c * p)) / R))) := by
  rw [squareRootCanonicalRoughPrimePartnerCount_sub_mul_eq_boundaries hR]
  unfold squareRootCanonicalRoughFreshPrimeUpperBoundary
    squareRootCanonicalRoughFreshPrimeLowerBoundary
  rw [squareRootCanonicalRoughPrimePartnerUpper_mul_freshPrime hc hp hrough,
    squareRootCanonicalRoughPrimePartnerLower_mul_freshPrime hc hp hrough]

/-- **Othello parent/child law at the actual terminal kernel.**  The fresh-prime
sign flip converts the two positive partner multiplicities into the signed
prime-count boundary difference above. -/
theorem canonicalMoebiusWeight_mul_primePartnerCount_pair_eq_boundaries
    {R c p : ℕ} (hR : 1 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hrough : canonicalLargestPrimeFactor c < p) :
    canonicalMoebiusWeight c * squareRootCanonicalRoughPrimePartnerCount R c +
        canonicalMoebiusWeight (c * p) *
          squareRootCanonicalRoughPrimePartnerCount R (c * p) =
      canonicalMoebiusWeight c *
        (squareRootCanonicalRoughFreshPrimeUpperBoundary R c p -
          squareRootCanonicalRoughFreshPrimeLowerBoundary R c p) := by
  rw [canonicalMoebiusWeight_mul_prime_eq_neg_of_rough hc hp hrough,
    ← mul_sub]
  rw [squareRootCanonicalRoughPrimePartnerCount_sub_mul_eq_boundaries hR]

/-- Freshness holds in the smallest nontrivial example used below. -/
theorem two_fresh_for_unit :
    (2 : ℕ).Prime ∧ canonicalLargestPrimeFactor 1 < 2 := by
  native_decide

/-- **Two-way non-nesting witness.**  At `R=10`, the fresh move `1 -> 2`
admits the lower partner `5` while simultaneously ejecting the upper partner
`53`.  Thus neither partner window contains the other.  Any successful global
ancestry estimate must retain the signed upper-minus-lower recoupling; it cannot
replace this by monotone capacity loss or absolute edge variation. -/
theorem freshPrimePartnerWindow_not_nested :
    5 ∈ squareRootCanonicalRoughPrimePartnerWindow 10 2 ∧
      5 ∉ squareRootCanonicalRoughPrimePartnerWindow 10 1 ∧
      53 ∈ squareRootCanonicalRoughPrimePartnerWindow 10 1 ∧
      53 ∉ squareRootCanonicalRoughPrimePartnerWindow 10 2 := by
  native_decide

end CanonicalRoughFreshPrimeDifference

end RHLean.Proof
