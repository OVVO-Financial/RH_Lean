import Mathlib
import «research.DYADIC_SMOOTH_HIGH_JOINT_PACKET»
import RHLean.Analysis.SquareRootTransportTopFibreNoGo

/-!
# Long-range transport tether: exact bridge and cardinality guardrail

A high square-root transport source really does jump from the square endpoint
back to a canonical cofactor below the root. The exact coordinate is not the
cofactor alone, however: it is the pair

    (canonical cofactor, canonical largest prime).

This file makes that long-range tether public and proves it is injective while
the prime label is retained.

It then records the obstruction to turning that reindexing into an O(R)
cardinality bound. The root projection alone is many-to-one. In fact every
top-half prime q in (X_R/2, X_R] has canonical cofactor 1, so the whole top
prime fibre is tethered to the single root vertex 1. The existing top-fibre
no-go theorem shows that this fibre has one native same-sign unit for every
such prime.

At R=56 the fibre contains exactly 198 primes. Thus the long-range incidence
graph is real, but it is a bipartite graph with prime multiplicity, not a
matching into at most R root vertices.

No analytic estimate or norm is used here.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- The exact long-range coordinate of a high transport source. -/
def squareRootLongRangeTether (m : ℕ) : ℕ × ℕ :=
  (canonicalCofactor m, canonicalLargestPrimeFactor m)

/-- Root coordinate after forgetting the prime label. -/
def squareRootLongRangeRoot (m : ℕ) : ℕ :=
  (squareRootLongRangeTether m).1

/-- Prime coordinate of the same tether. -/
def squareRootLongRangePrime (m : ℕ) : ℕ :=
  (squareRootLongRangeTether m).2

/-- Every high transport source is nontrivial. -/
theorem one_lt_of_mem_squareRootHighTransportSourceSet_public
    {R m : ℕ} (hR : 1 ≤ R)
    (hm : m ∈ squareRootHighTransportSourceSet R) :
    1 < m := by
  have hhigh := (Finset.mem_filter.mp hm).2
  by_contra hnot
  have hP : canonicalLargestPrimeFactor m = 1 := by
    unfold canonicalLargestPrimeFactor
    rw [dif_neg hnot]
  omega

/-- Exact long-range tether. Every high source lands in the canonical
cofactor/large-prime pair carrier. In particular its cofactor is below R and
its prime coordinate lies above R. -/
theorem squareRootLongRangeTether_mem_pairSet
    {R m : ℕ} (hR : 1 ≤ R)
    (hm : m ∈ squareRootHighTransportSourceSet R) :
    squareRootLongRangeTether m ∈ squareRootTransportPairSet R := by
  rcases Finset.mem_filter.mp hm with ⟨hmPrefix, hhigh⟩
  have hmgt : 1 < m :=
    one_lt_of_mem_squareRootHighTransportSourceSet_public hR hm
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR
  have hmLt : m < R ^ 2 := by
    simpa [cumulativeSquarePrefixSet, hpred] using hmPrefix
  have hprod :
      canonicalCofactor m * canonicalLargestPrimeFactor m = m :=
    canonicalCofactor_mul_largestPrimeFactor hmgt
  have hqPrime : (canonicalLargestPrimeFactor m).Prime :=
    canonicalLargestPrimeFactor_prime hmgt
  have hcPos : 0 < canonicalCofactor m := by
    by_contra hnot
    have hc0 : canonicalCofactor m = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hc0, zero_mul] at hprod
    omega
  have hcR : canonicalCofactor m < R := by
    by_contra hnot
    have hRc : R ≤ canonicalCofactor m := Nat.le_of_not_gt hnot
    have hleft : R * R ≤ canonicalCofactor m * R :=
      Nat.mul_le_mul_right R hRc
    have hright :
        canonicalCofactor m * R <
          canonicalCofactor m * canonicalLargestPrimeFactor m :=
      Nat.mul_lt_mul_of_pos_left hhigh hcPos
    have hRRm : R ^ 2 < m := by
      rw [pow_two]
      calc
        R * R ≤ canonicalCofactor m * R := hleft
        _ < canonicalCofactor m * canonicalLargestPrimeFactor m := hright
        _ = m := hprod
    omega
  have hmX : m ≤ squareRootEndpoint R := by
    unfold squareRootEndpoint
    omega
  have hqDvd : canonicalLargestPrimeFactor m ∣ m :=
    canonicalLargestPrimeFactor_dvd hmgt
  have hqLe : canonicalLargestPrimeFactor m ≤ m :=
    Nat.le_of_dvd (by omega) hqDvd
  have hqX : canonicalLargestPrimeFactor m ≤ squareRootEndpoint R :=
    hqLe.trans hmX
  unfold squareRootLongRangeTether squareRootTransportPairSet
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Ico.mpr ⟨Nat.succ_le_iff.mpr hcPos, hcR⟩,
        Finset.mem_Ioc.mpr ⟨hhigh, hqX⟩⟩
  · exact ⟨hqPrime, by simpa [hprod] using hmX⟩

/-- The long-range tether retains the exact source product. -/
theorem squareRootLongRangeTether_product_eq
    {R m : ℕ} (hR : 1 ≤ R)
    (hm : m ∈ squareRootHighTransportSourceSet R) :
    (squareRootLongRangeTether m).1 *
        (squareRootLongRangeTether m).2 = m := by
  have hmgt :=
    one_lt_of_mem_squareRootHighTransportSourceSet_public hR hm
  simpa [squareRootLongRangeTether] using
    canonicalCofactor_mul_largestPrimeFactor hmgt

/-- The full long-range coordinate is injective on high sources. This is the
legitimate sense in which the tether is a matching: the prime label must remain
part of the target coordinate. -/
theorem squareRootLongRangeTether_injective_on_high
    {R m n : ℕ} (hR : 1 ≤ R)
    (hm : m ∈ squareRootHighTransportSourceSet R)
    (hn : n ∈ squareRootHighTransportSourceSet R)
    (h : squareRootLongRangeTether m = squareRootLongRangeTether n) :
    m = n := by
  have hmprod := squareRootLongRangeTether_product_eq hR hm
  have hnprod := squareRootLongRangeTether_product_eq hR hn
  calc
    m = (squareRootLongRangeTether m).1 *
        (squareRootLongRangeTether m).2 := hmprod.symm
    _ = (squareRootLongRangeTether n).1 *
        (squareRootLongRangeTether n).2 := by rw [h]
    _ = n := hnprod

/-- The root end of every high-source tether lies strictly below R. -/
theorem squareRootLongRangeRoot_lt
    {R m : ℕ} (hR : 1 ≤ R)
    (hm : m ∈ squareRootHighTransportSourceSet R) :
    squareRootLongRangeRoot m < R := by
  have ht := squareRootLongRangeTether_mem_pairSet hR hm
  rcases Finset.mem_filter.mp ht with ⟨hbase, _⟩
  rcases Finset.mem_product.mp hbase with ⟨hc, _hq⟩
  exact (Finset.mem_Ico.mp hc).2

/-- The prime end of every high-source tether lies strictly above R. -/
theorem squareRootLongRangePrime_gt
    {R m : ℕ} (hR : 1 ≤ R)
    (hm : m ∈ squareRootHighTransportSourceSet R) :
    R < squareRootLongRangePrime m := by
  have ht := squareRootLongRangeTether_mem_pairSet hR hm
  rcases Finset.mem_filter.mp ht with ⟨hbase, _⟩
  rcases Finset.mem_product.mp hbase with ⟨_hc, hq⟩
  exact (Finset.mem_Ioc.mp hq).1

/-! ## The root projection is not a cardinality bottleneck -/

/-- A top-fibre prime is literally tethered to the unit root. -/
theorem squareRootTopFibrePrime_longRangeTether_eq_unit
    {R q : ℕ} (hq : q ∈ squareRootTopFibrePrimes R) :
    squareRootLongRangeTether q = (1, q) := by
  have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2
  have hlpf : canonicalLargestPrimeFactor q = q := by
    simpa using
      (canonicalLargestPrimeFactor_mul_prime_eq
        (c := 1) (q := q) (by norm_num) hqPrime.one_lt hqPrime)
  have hcofactor : canonicalCofactor q = 1 := by
    simpa using
      (canonicalCofactor_mul_prime_eq
        (c := 1) (q := q) (by norm_num) hqPrime.one_lt hqPrime)
  simp [squareRootLongRangeTether, hlpf, hcofactor]

/-- For R >= 3 every top-fibre prime is also an atom of the high part of the
top odd dyadic annulus from the Item-87 packet. -/
theorem squareRootTopFibrePrime_mem_dyadicAnnulusHigh
    {R q : ℕ} (hR : 3 ≤ R)
    (hq : q ∈ squareRootTopFibrePrimes R) :
    q ∈ squareRootDyadicAnnulusHighSet R := by
  rcases Finset.mem_filter.mp hq with ⟨hqRange, hqPrime⟩
  rcases Finset.mem_Ioc.mp hqRange with ⟨hhalfq, hqX⟩
  have htwoRlt : 2 * R < R * R :=
    Nat.mul_lt_mul_of_pos_right (by omega : 2 < R) (by omega : 0 < R)
  have hRhalf : R ≤ squareRootEndpoint R / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).2
    unfold squareRootEndpoint
    rw [pow_two]
    omega
  have hRq : R < q := lt_of_le_of_lt hRhalf hhalfq
  have hodd : Odd q := hqPrime.odd_of_ne_two (by omega)
  have htwice' : squareRootEndpoint R < q * 2 :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < (2 : ℕ))).1 hhalfq
  have htwice : squareRootEndpoint R < 2 * q := by
    simpa [Nat.mul_comm] using htwice'
  have hboundary :
      q ∈ dyadicCofactorBoundary (squareRootEndpoint R) :=
    mem_dyadicCofactorBoundary.mpr
      ⟨hqPrime.one_le, hqX, hodd, htwice⟩
  have hlpf : canonicalLargestPrimeFactor q = q := by
    simpa using
      (canonicalLargestPrimeFactor_mul_prime_eq
        (c := 1) (q := q) (by norm_num) hqPrime.one_lt hqPrime)
  unfold squareRootDyadicAnnulusHighSet
  exact Finset.mem_filter.mpr ⟨hboundary, by simpa [hlpf] using hRq⟩

/-- Concrete kernel witness: two distinct high top-annulus atoms at R=56 have
the same root endpoint 1. Thus forgetting the prime label destroys
injectivity. -/
theorem squareRootLongRangeRoot_not_injective_at_56 :
    ∃ m n : ℕ,
      m ∈ squareRootDyadicAnnulusHighSet 56 ∧
      n ∈ squareRootDyadicAnnulusHighSet 56 ∧
      m ≠ n ∧
      squareRootLongRangeRoot m = squareRootLongRangeRoot n := by
  have h1571 : 1571 ∈ squareRootTopFibrePrimes 56 := by
    native_decide
  have h1579 : 1579 ∈ squareRootTopFibrePrimes 56 := by
    native_decide
  refine ⟨1571, 1579,
    squareRootTopFibrePrime_mem_dyadicAnnulusHigh (by norm_num) h1571,
    squareRootTopFibrePrime_mem_dyadicAnnulusHigh (by norm_num) h1579,
    by norm_num, ?_⟩
  have ht1 := squareRootTopFibrePrime_longRangeTether_eq_unit h1571
  have ht2 := squareRootTopFibrePrime_longRangeTether_eq_unit h1579
  simp [squareRootLongRangeRoot, ht1, ht2]

/-- Exact finite size of the same-sign unit-root top fibre at the first
production root. -/
theorem squareRootTopFibrePrimes_card_56 :
    (squareRootTopFibrePrimes 56).card = 198 := by
  native_decide

/-- The unit-root fibre alone already has more atoms than the entire root
interval has coordinates at R=56. -/
theorem squareRootTopFibrePrimes_card_gt_root_56 :
    56 < (squareRootTopFibrePrimes 56).card := by
  rw [squareRootTopFibrePrimes_card_56]
  norm_num

end RHLean.Proof
