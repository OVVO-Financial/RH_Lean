import Mathlib
import «research.VF_MID_DYADIC_PREFIX_OWNER»

/-!
# Complete finite square-root wheel, fractional boundary and virtual divisors

The square-root wheel carries the *full* signed divisor sum, including all
virtual divisors d > X.  Their fractional contributions equal X/d, and
cancel with the corresponding finite Euler-product terms before any norm is
taken.  There is no RH, analytic continuation, or infinite Euler product.

All main equalities are elementary and finite.  The further square-endpoint
prime-counting specialization is appended below.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

/-- Each squarefree divisor of the small-prime primorial corresponds to the
unique Boolean face containing precisely its prime factors. -/
private theorem finiteWheel_faces_sum_eq_primorial_divisors
    {β : Type*} [AddCommMonoid β] (z : ℕ) (f : ℕ → β) :
    (∑ t ∈ (primesUpTo z).powerset, f (primeFaceProduct t)) =
      ∑ d ∈ (primorial z).divisors, f d := by
  classical
  let S : Finset ℕ := primesUpTo z
  let W : ℕ := primorialWheelProduct S
  have hprime : ∀ p ∈ S, p.Prime :=
    fun p hp => prime_of_mem_primesUpTo hp
  have hW : W = primorial z := rfl
  have hW0 : W ≠ 0 := by
    dsimp [W, primorialWheelProduct]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => (hprime p hp).ne_zero)
  have hWsf : Squarefree W := by
    rw [hW]
    exact squarefree_primorial z
  change (∑ t ∈ S.powerset, f (primeFaceProduct t)) =
    ∑ d ∈ W.divisors, f d
  refine Finset.sum_bij (fun t _ht => primeFaceProduct t) ?_ ?_ ?_ ?_
  · intro t ht
    have hsub : t ⊆ S := Finset.mem_powerset.mp ht
    have hdiv : primeFaceProduct t ∣ W := by
      unfold primeFaceProduct W primorialWheelProduct
      exact Finset.prod_dvd_prod_of_subset t S id hsub
    exact Nat.mem_divisors.mpr ⟨hdiv, hW0⟩
  · intro t ht u hu htu
    have htf : (primeFaceProduct t).primeFactors = t := by
      unfold primeFaceProduct
      exact Nat.primeFactors_prod
        (fun p hp => hprime p ((Finset.mem_powerset.mp ht) hp))
    have huf : (primeFaceProduct u).primeFactors = u := by
      unfold primeFaceProduct
      exact Nat.primeFactors_prod
        (fun p hp => hprime p ((Finset.mem_powerset.mp hu) hp))
    calc
      t = (primeFaceProduct t).primeFactors := htf.symm
      _ = (primeFaceProduct u).primeFactors := by rw [htu]
      _ = u := huf
  · intro d hd
    have hdW : d ∣ W := (Nat.mem_divisors.mp hd).1
    have hdsf : Squarefree d := hWsf.squarefree_of_dvd hdW
    have hdsub : d.primeFactors ⊆ S := by
      have h := Nat.primeFactors_mono hdW hW0
      have hpf : W.primeFactors = S := by
        dsimp [W, primorialWheelProduct]
        exact Nat.primeFactors_prod hprime
      rwa [hpf] at h
    refine ⟨d.primeFactors, Finset.mem_powerset.mpr hdsub, ?_⟩
    unfold primeFaceProduct
    exact Nat.prod_primeFactors_of_squarefree hdsf
  · intro t _ht
    rfl

/-- The complete Möbius divisor reciprocal sum is precisely the finite
Euler product, with no truncation at the physical endpoint. -/
theorem finiteWheel_divisorReciprocal_eq_eulerProduct (z : ℕ) :
    (∑ d ∈ (primorial z).divisors,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      vfMidPrefixWheelDensity z := by
  classical
  calc
    (∑ d ∈ (primorial z).divisors,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      ∑ t ∈ (primesUpTo z).powerset,
        (ArithmeticFunction.moebius (primeFaceProduct t) : ℝ) /
          (primeFaceProduct t : ℝ) :=
      (finiteWheel_faces_sum_eq_primorial_divisors z _).symm
    _ = ∑ t ∈ (primesUpTo z).powerset,
          ((booleanCubeSign t : ℤ) : ℝ) /
            (primeFaceProduct t : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [moebius_primeFaceProduct_eq_booleanCubeSign t
        (fun p hp => prime_of_mem_primesUpTo
          ((Finset.mem_powerset.mp ht) hp))]
    _ = vfMidPrefixWheelDensity z :=
      (vfMidPrefixWheelDensity_eq_faceReciprocalSum z).symm

/-- Exact integer Legendre floor source before identifying the survivors as
one plus the primes above the root. -/
theorem finiteWheel_divisorFloor_eq_survivorCount (z X : ℕ) :
    (∑ d ∈ (primorial z).divisors,
        (ArithmeticFunction.moebius d : ℤ) * ((X / d : ℕ) : ℤ)) =
      (vfMidPrefixWheelCounting z X : ℤ) := by
  classical
  calc
    (∑ d ∈ (primorial z).divisors,
        (ArithmeticFunction.moebius d : ℤ) * ((X / d : ℕ) : ℤ)) =
      ∑ t ∈ (primesUpTo z).powerset,
        (ArithmeticFunction.moebius (primeFaceProduct t) : ℤ) *
          ((X / primeFaceProduct t : ℕ) : ℤ) :=
      (finiteWheel_faces_sum_eq_primorial_divisors z _).symm
    _ = ∑ t ∈ (primesUpTo z).powerset,
          booleanCubeSign t * ((X / primeFaceProduct t : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [moebius_primeFaceProduct_eq_booleanCubeSign t
        (fun p hp => prime_of_mem_primesUpTo
          ((Finset.mem_powerset.mp ht) hp))]
    _ = (vfMidPrefixWheelCounting z X : ℤ) :=
      (vfMidPrefixWheelCounting_cast_int_eq_faceFloorSum z X).symm

/-- Fractional part of a rational integer quotient is its real quotient
minus its integer floor.  Works even when d > X. -/
private theorem finiteWheel_fract_eq_div_sub_natDiv (X d : ℕ) :
    Int.fract ((X : ℝ) / (d : ℝ)) =
      (X : ℝ) / (d : ℝ) - ((X / d : ℕ) : ℝ) := by
  have hfloorcast :
      (⌊(X : ℝ) / (d : ℝ)⌋ : ℝ) = ((X / d : ℕ) : ℝ) := by
    have hz :
        ⌊(X : ℝ) / (d : ℝ)⌋ = ((X / d : ℕ) : ℤ) := by
      rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
    rw [hz]
    norm_cast
  rw [← Int.self_sub_floor, hfloorcast]

/-- Complete signed fractional boundary for the fixed prime coordinates. -/
def finiteWheelFract (z X : ℕ) : ℝ :=
  ∑ d ∈ (primorial z).divisors,
    (ArithmeticFunction.moebius d : ℝ) *
      Int.fract ((X : ℝ) / (d : ℝ))

/-- The fractional part of each *virtual divisor*, d > X, is literally X/d.
This is a pointwise identity, not a bound or a discarded error term. -/
theorem finiteWheel_virtualFract_eq_quotient
    {z X d : ℕ}
    (hd : d ∈ (primorial z).divisors)
    (hdX : X < d) :
    Int.fract ((X : ℝ) / (d : ℝ)) =
      (X : ℝ) / (d : ℝ) := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdRpos : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hXle : (0 : ℝ) ≤ X := by positivity
  have hXR : (X : ℝ) < d := by exact_mod_cast hdX
  exact Int.fract_eq_self.mpr
    ⟨div_nonneg hXle hdRpos.le, (div_lt_one hdRpos).mpr hXR⟩

/-- Retain all virtual divisors in the complete signed fractional boundary:
every term beyond X is an exactly identified reciprocal contribution. -/
theorem finiteWheelFract_eq_physical_add_virtual (z X : ℕ) :
    finiteWheelFract z X =
      (∑ d ∈ (primorial z).divisors.filter (fun d => d ≤ X),
          (ArithmeticFunction.moebius d : ℝ) *
            Int.fract ((X : ℝ) / (d : ℝ))) +
      (X : ℝ) *
        (∑ d ∈ (primorial z).divisors.filter (fun d => X < d),
          (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) := by
  classical
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (s := (primorial z).divisors) (p := fun d => d ≤ X)
    (f := fun d => (ArithmeticFunction.moebius d : ℝ) *
      Int.fract ((X : ℝ) / (d : ℝ)))
  have hfilter :
      (primorial z).divisors.filter (fun d => ¬ d ≤ X) =
      (primorial z).divisors.filter (fun d => X < d) := by
    ext d
    simp only [Finset.mem_filter, not_le]
  rw [hfilter] at hpartition
  unfold finiteWheelFract
  rw [← hpartition]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdd := (Finset.mem_filter.mp hd)
  rw [finiteWheel_virtualFract_eq_quotient hdd.1 hdd.2]
  ring

/-- The virtual d>X contributions cancel *term-by-term* against the Euler
product.  The resulting error is supported on d<=X, not a truncated copy of
the original fractional sum. -/
theorem finiteWheelFract_sub_density_eq_physical_floorError
    (z X : ℕ) :
    finiteWheelFract z X - (X : ℝ) * vfMidPrefixWheelDensity z =
      ∑ d ∈ (primorial z).divisors.filter (fun d => d ≤ X),
        (ArithmeticFunction.moebius d : ℝ) *
          (Int.fract ((X : ℝ) / (d : ℝ)) -
            (X : ℝ) / (d : ℝ)) := by
  classical
  have hwhole :
      finiteWheelFract z X - (X : ℝ) * vfMidPrefixWheelDensity z =
        ∑ d ∈ (primorial z).divisors,
          (ArithmeticFunction.moebius d : ℝ) *
            (Int.fract ((X : ℝ) / (d : ℝ)) -
              (X : ℝ) / (d : ℝ)) := by
    unfold finiteWheelFract
    rw [← finiteWheel_divisorReciprocal_eq_eulerProduct,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hwhole]
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (s := (primorial z).divisors) (p := fun d => d ≤ X)
    (f := fun d => (ArithmeticFunction.moebius d : ℝ) *
      (Int.fract ((X : ℝ) / (d : ℝ)) - (X : ℝ) / (d : ℝ)))
  have htail :
      (∑ d ∈ (primorial z).divisors.filter (fun d => ¬ d ≤ X),
        (ArithmeticFunction.moebius d : ℝ) *
          (Int.fract ((X : ℝ) / (d : ℝ)) -
            (X : ℝ) / (d : ℝ))) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hdData := Finset.mem_filter.mp hd
    have hdX : X < d := by omega
    rw [finiteWheel_virtualFract_eq_quotient hdData.1 hdX]
    ring
  rw [htail, add_zero] at hpartition
  exact hpartition.symm

-- All divisor identities above are RH-free and preserve the complete wheel.

end RHLean.Analysis
