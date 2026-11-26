import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-!
# Newton readouts modulo an integral ideal

The finite coefficients are computed once from each sequence at zero.  A tail
bound then gives the same readout at every natural input.  For separable
products the support can be cut by total degree using joint coefficient
divisibility.
-/

namespace RHLean.Geometry.NativeNewtonCongruence

open scoped BigOperators

noncomputable section

variable {O : Type*} [CommRing O]

/-- The integral Newton coefficient of order `j`. -/
def coefficient (f : ℕ → O) (j : ℕ) : O :=
  ((fwdDiff (1 : ℕ))^[j] f) 0

/-- A finite integer-valued binomial-basis expression, evaluated at `n`. -/
def readout (f : ℕ → O) (L n : ℕ) : O :=
  ∑ j ∈ Finset.range (L + 1), (n.choose j : O) * coefficient f j

private theorem exact_at (f : ℕ → O) (n : ℕ) : f n = readout f n n := by
  simpa [readout, coefficient, nsmul_eq_mul] using
    (shift_eq_sum_fwdDiff_iter (1 : ℕ) f n (0 : ℕ))

/-- A single fixed truncation works at every exponent, including inputs smaller
than the cutoff. -/
theorem sub_readout_mem (I : Ideal O) (f : ℕ → O) (L : ℕ)
    (htail : ∀ j, L < j → coefficient f j ∈ I) (n : ℕ) :
    f n - readout f L n ∈ I := by
  let q := Ideal.Quotient.mk I
  let term (j : ℕ) := q ((n.choose j : O) * coefficient f j)
  have hinput (j : ℕ) (hj : n < j) : term j = 0 := by
    simp [term, Nat.choose_eq_zero_of_lt hj]
  have htail' (j : ℕ) (hj : L < j) : term j = 0 := by
    have hz : q (coefficient f j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (htail j hj)
    change q ((n.choose j : O) * coefficient f j) = 0
    rw [map_mul, hz, mul_zero]
  have hsum : ∑ j ∈ Finset.range (n + 1), term j =
      ∑ j ∈ Finset.range (L + 1), term j := by
    rcases le_total n L with h | h
    · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h))
      intro j _ hj
      exact hinput j (Nat.not_lt.mp fun hlt => hj (Finset.mem_range.mpr hlt))
    · symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h))
      intro j _ hj
      exact htail' j (Nat.not_lt.mp fun hlt => hj (Finset.mem_range.mpr hlt))
  apply Ideal.Quotient.eq.mp
  calc
    q (f n) = ∑ j ∈ Finset.range (n + 1), term j := by
      rw [exact_at f n]
      exact map_sum q _ _
    _ = ∑ j ∈ Finset.range (L + 1), term j := hsum
    _ = q (readout f L n) := (map_sum q _ _).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A fixed array of multivariate binomial coefficients supported in total
degree at most `L`, with separable Newton coefficients computed at zero. -/
def totalReadout (f : ι → ℕ → O) (L : ℕ) (n : ι → ℕ) : O :=
  ∑ k : ι → Fin (L + 1), if (∑ i, (k i).val) ≤ L then
    (∏ i, ((n i).choose (k i).val : O)) * (∏ i, coefficient (f i) (k i).val)
  else 0

private theorem product_expansion (f : ι → ℕ → O) (L : ℕ) (n : ι → ℕ) :
    (∏ i, readout (f i) L (n i)) =
      ∑ k : ι → Fin (L + 1),
        (∏ i, ((n i).choose (k i).val : O)) * (∏ i, coefficient (f i) (k i).val) := by
  classical
  let t (i : ι) (j : Fin (L + 1)) :=
    ((n i).choose j.val : O) * coefficient (f i) j.val
  have hi (i : ι) : readout (f i) L (n i) = ∑ j : Fin (L + 1), t i j :=
    (Fin.sum_univ_eq_sum_range (fun j => ((n i).choose j : O) * coefficient (f i) j)
      (L + 1)).symm
  calc
    (∏ i, readout (f i) L (n i)) = ∏ i, ∑ j : Fin (L + 1), t i j :=
      Finset.prod_congr rfl fun i _ => hi i
    _ = ∑ k : ι → Fin (L + 1), ∏ i, t i (k i) := by
      simpa using (Finset.prod_univ_sum
        (fun _ : ι => (Finset.univ : Finset (Fin (L + 1)))) t)
    _ = _ := Finset.sum_congr rfl fun k _ => Finset.prod_mul_distrib

/-- Coordinate tails and mixed coefficients outside the total-degree simplex
vanish modulo the same ideal. -/
theorem prod_sub_totalReadout_mem (I : Ideal O) (f : ι → ℕ → O) (L : ℕ)
    (htail : ∀ i j, L < j → coefficient (f i) j ∈ I)
    (hmixed : ∀ k : ι → Fin (L + 1), L < (∑ i, (k i).val) →
      (∏ i, coefficient (f i) (k i).val) ∈ I)
    (n : ι → ℕ) : (∏ i, f i (n i)) - totalReadout f L n ∈ I := by
  classical
  let q := Ideal.Quotient.mk I
  apply Ideal.Quotient.eq.mp
  calc
    q (∏ i, f i (n i)) = ∏ i, q (f i (n i)) := map_prod q _ _
    _ = ∏ i, q (readout (f i) L (n i)) := by
      exact Finset.prod_congr rfl fun i _ =>
        Ideal.Quotient.eq.mpr (sub_readout_mem I (f i) L (htail i) (n i))
    _ = q (∏ i, readout (f i) L (n i)) := (map_prod q _ _).symm
    _ = q (totalReadout f L n) := by
      rw [product_expansion, totalReadout, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : (∑ i, (k i).val) ≤ L
      · rw [ite_eq_left hk]
      · have hz : q (∏ i, coefficient (f i) (k i).val) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (hmixed k (Nat.lt_of_not_ge hk))
        rw [ite_eq_right hk, map_zero, map_mul, hz, mul_zero]

/-- If each order-`j` coefficient is divisible by `p ^ ⌈j/2⌉`, the product
has a uniform binomial approximation of total degree `2 * (c - 1)` modulo
`p ^ c`.  The cutoff is independent of the number of coordinates. -/
theorem pow_dvd_prod_sub_totalReadout (p : O) (c : ℕ) (hc : 0 < c)
    (f : ι → ℕ → O)
    (hval : ∀ i j, p ^ ((j + 1) / 2) ∣ coefficient (f i) j)
    (n : ι → ℕ) : p ^ c ∣ (∏ i, f i (n i)) - totalReadout f (2 * (c - 1)) n := by
  classical
  apply Ideal.mem_span_singleton.mp
  apply prod_sub_totalReadout_mem
  · intro i j hj
    exact Ideal.mem_span_singleton.mpr ((pow_dvd_pow p (by omega : c ≤ (j + 1) / 2)).trans
      (hval i j))
  · intro k hk
    let w (i : ι) := ((k i).val + 1) / 2
    have hweight : (∑ i, (k i).val) ≤ 2 * ∑ i, w i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by dsimp [w]; omega
    have hc' : c ≤ ∑ i, w i := by omega
    apply Ideal.mem_span_singleton.mpr
    refine (pow_dvd_pow p hc').trans ?_
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_dvd_prod_of_dvd
    exact fun i _ => hval i (k i).val

end

end RHLean.Geometry.NativeNewtonCongruence
