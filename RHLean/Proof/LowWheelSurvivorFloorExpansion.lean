import Mathlib
import RHLean.Proof.LowWheelSurvivorInclusionExclusion

/-!
# Floor expansion of low-wheel survivor frequencies

The Boolean-cube expansion of the high-prime survivor count is now converted
into the exact arithmetic floor formula.  For each low-prime face `t`, the
number of multiples of its squarefree product `d = primeFaceProduct t` in the
interval `(R,B]` is

`floor(B/d) - floor(R/d)`.

Specializing `B = floor((R^2-1)/c)` therefore removes the prime-count function
from every transport multiplicity.  The high-prime frequency is expressed
entirely through low-prime Boolean-cube signs and the hyperbolic cutoff
`c * d * k <= R^2 - 1`.

No norm, prime-number theorem, Strong Mertens estimate, or asymptotic input is
used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Exact count of multiples of a positive integer in a half-open interval. -/
theorem card_Ioc_filter_dvd_eq_div_sub_div
    (A B d : ℕ) (hd : 0 < d) :
    ((Finset.Ioc A B).filter fun q => d ∣ q).card =
      B / d - A / d := by
  classical
  have hbij :
      (Finset.Ioc (A / d) (B / d)).card =
        ((Finset.Ioc A B).filter fun q => d ∣ q).card := by
    refine Finset.card_bij (fun k _hk => d * k) ?_ ?_ ?_
    · intro k hk
      rcases Finset.mem_Ioc.mp hk with ⟨hlow, hupp⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Ioc.mpr
        constructor
        · have h := (Nat.div_lt_iff_lt_mul hd).1 hlow
          simpa [Nat.mul_comm] using h
        · have h := (Nat.le_div_iff_mul_le hd).1 hupp
          simpa [Nat.mul_comm] using h
      · exact ⟨k, rfl⟩
    · intro a _ha b _hb hab
      exact Nat.eq_of_mul_eq_mul_left hd hab
    · intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqIoc, hdiv⟩
      rcases hdiv with ⟨k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      apply Finset.mem_Ioc.mpr
      constructor
      · apply (Nat.div_lt_iff_lt_mul hd).2
        simpa [Nat.mul_comm] using (Finset.mem_Ioc.mp hqIoc).1
      · apply (Nat.le_div_iff_mul_le hd).2
        simpa [Nat.mul_comm] using (Finset.mem_Ioc.mp hqIoc).2
  simpa using hbij.symm

/-- Every Boolean-cube prime-face product is positive. -/
theorem primeFaceProduct_pos_of_mem_powerset
    {R : ℕ} {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset) :
    0 < primeFaceProduct t := by
  unfold primeFaceProduct
  apply Finset.prod_pos
  intro p hp
  have hpR : p ∈ primesUpTo R := (Finset.mem_powerset.mp ht) hp
  exact (prime_of_mem_primesUpTo hpR).pos

/-- One face's divisibility population is the elementary floor difference. -/
theorem lowWheelFaceMultipleSet_card_eq_floorDiff
    {R B : ℕ} {t : Finset ℕ}
    (ht : t ∈ (primesUpTo R).powerset) :
    (lowWheelFaceMultipleSet R B t).card =
      B / primeFaceProduct t - R / primeFaceProduct t := by
  unfold lowWheelFaceMultipleSet
  exact card_Ioc_filter_dvd_eq_div_sub_div
    R B (primeFaceProduct t) (primeFaceProduct_pos_of_mem_powerset ht)

/-- **Boolean-cube floor expansion.**  Every high-survivor count is now an
exact finite alternating sum of floor differences indexed only by low-prime
faces. -/
theorem lowWheelHighSurvivorSet_card_eq_faceFloorDiff
    (R B : ℕ) :
    ((lowWheelHighSurvivorSet R B).card : ℤ) =
      ∑ t ∈ (primesUpTo R).powerset,
        booleanCubeSign t *
          ((B / primeFaceProduct t - R / primeFaceProduct t : ℕ) : ℤ) := by
  rw [lowWheelHighSurvivorSet_card_eq_faceMultipleCounts]
  apply Finset.sum_congr rfl
  intro t ht
  rw [lowWheelFaceMultipleSet_card_eq_floorDiff ht]

/-- The cofactor-specific high-prime multiplicity has no remaining prime-count
term: it is a signed low-wheel face sum with a reciprocal hyperbolic cutoff. -/
theorem lowWheelHighPrimeMultiplicity_eq_faceFloorDiff
    (R c : ℕ) :
    (lowWheelHighPrimeMultiplicity R c : ℤ) =
      ∑ t ∈ (primesUpTo R).powerset,
        booleanCubeSign t *
          ((squareRootEndpoint R / (c * primeFaceProduct t) -
              R / primeFaceProduct t : ℕ) : ℤ) := by
  unfold lowWheelHighPrimeMultiplicity
  rw [lowWheelHighSurvivorSet_card_eq_faceFloorDiff]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [Nat.div_div_eq_div_mul]

/-- Complex form of the exact frequency expansion, ready to substitute into
the cofactor-first transport sum without changing its signed order. -/
theorem lowWheelHighPrimeMultiplicity_cast_eq_faceFloorDiff
    (R c : ℕ) :
    (lowWheelHighPrimeMultiplicity R c : ℂ) =
      ∑ t ∈ (primesUpTo R).powerset,
        (booleanCubeSign t : ℂ) *
          ((squareRootEndpoint R / (c * primeFaceProduct t) -
              R / primeFaceProduct t : ℕ) : ℂ) := by
  have h := lowWheelHighPrimeMultiplicity_eq_faceFloorDiff R c
  exact_mod_cast h

/-- **Prime-count-free transport identity.**  The whole upper-prime transport
mass is a finite double sum over a low cofactor `c` and a low-prime Boolean face
`t`.  The high region now appears only through the floor cutoff. -/
theorem squareRootTransportCofactorFirst_eq_lowWheelFaceFloorSum
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootTransportCofactorFirst R =
      ∑ c ∈ Finset.Ico 1 R,
        ∑ t ∈ (primesUpTo R).powerset,
          canonicalMoebiusWeight c * (booleanCubeSign t : ℂ) *
            ((squareRootEndpoint R / (c * primeFaceProduct t) -
                R / primeFaceProduct t : ℕ) : ℂ) := by
  rw [squareRootTransportCofactorFirst_eq_lowWheelFrequency R hR]
  unfold squareRootTransportLowWheelFrequency
  apply Finset.sum_congr rfl
  intro c _hc
  rw [lowWheelHighPrimeMultiplicity_cast_eq_faceFloorDiff R c]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _ht
  ring

end RHLean.Proof
