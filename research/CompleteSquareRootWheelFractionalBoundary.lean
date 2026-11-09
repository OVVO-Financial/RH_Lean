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
  let W : ℕ := S.prod id
  have hprime : ∀ p ∈ S, p.Prime :=
    fun p hp => prime_of_mem_primesUpTo hp
  have hW : W = primorial z := rfl
  have hW0 : W ≠ 0 := by
    dsimp [W]
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
      unfold primeFaceProduct W
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


/-! ## Exact prime-counting specialization at square-prefix endpoints -/

/-- Every positive survivor below R squared is 1 or a prime above R-1. -/
private theorem finiteWheel_squareSurvivor_iff_one_or_highPrime
    {R n : ℕ} (hR : 2 ≤ R) (hnpos : 0 < n)
    (hnX : n ≤ squareRootEndpoint R) :
    lowWheelHighSurvivor (R - 1) n ↔
      n = 1 ∨ (n.Prime ∧ R - 1 < n) := by
  have hnLtSq : n < R ^ 2 := by
    unfold squareRootEndpoint at hnX
    have hsq : 0 < R ^ 2 := by positivity
    omega
  by_cases hnOne : n = 1
  · subst n
    constructor
    · intro _
      exact Or.inl rfl
    · intro _ p hp hpd
      exact (prime_of_mem_primesUpTo hp).not_dvd_one hpd
  by_cases hnPrime : n.Prime
  · constructor
    · intro hsurv
      have hlarge : R - 1 < n := by
        by_contra hnot
        have hlow : n ∈ primesUpTo (R - 1) :=
          mem_primesUpTo.mpr ⟨hnPrime, Nat.le_of_not_gt hnot⟩
        exact hsurv n hlow (dvd_refl n)
      exact Or.inr ⟨hnPrime, hlarge⟩
    · rintro (hOne | ⟨_hnP, hlarge⟩)
      · exact False.elim (hnOne hOne)
      · intro p hp hpDiv
        have hpPrime := prime_of_mem_primesUpTo hp
        have hpLe : p ≤ R - 1 := (mem_primesUpTo.mp hp).2
        have hpEq : p = n :=
          (Nat.prime_dvd_prime_iff_eq hpPrime hnPrime).mp hpDiv
        omega
  · let p := n.minFac
    have hp : p.Prime := by
      simpa [p] using Nat.minFac_prime hnOne
    have hpd : p ∣ n := by
      simpa [p] using Nat.minFac_dvd n
    have hpSq : p ^ 2 ≤ n := by
      simpa [p] using Nat.minFac_sq_le_self hnpos hnPrime
    have hpLtR : p < R := by
      by_contra hnot
      have hRp : R ≤ p := Nat.le_of_not_gt hnot
      have hpow : R ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hRp 2
      omega
    have hpMem : p ∈ primesUpTo (R - 1) :=
      mem_primesUpTo.mpr ⟨hp, by omega⟩
    constructor
    · intro hsurv
      exact False.elim (hsurv p hpMem hpd)
    · rintro (hOne | ⟨hPrime, _⟩)
      · exact False.elim (hnOne hOne)
      · exact False.elim (hnPrime hPrime)

/-- Native primeCounting agrees with the genuine finite prime filter. -/
private theorem finiteWheel_primeCount_range (N : ℕ) :
    ((Finset.range (N + 1)).filter Nat.Prime).card =
      Nat.primeCounting N := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]

/-- Actual prime counts split exactly across any ordered walls. -/
private theorem finiteWheel_primeCount_split
    (L U : ℕ) (hLU : L ≤ U) :
    ((Finset.Ioc L U).filter Nat.Prime).card +
      Nat.primeCounting L = Nat.primeCounting U := by
  let A : Finset ℕ := (Finset.range (L + 1)).filter Nat.Prime
  let B : Finset ℕ := (Finset.Ioc L U).filter Nat.Prime
  let C : Finset ℕ := (Finset.range (U + 1)).filter Nat.Prime
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpB
    have hpL : p ≤ L := by
      have hp := (Finset.mem_filter.mp hpA).1
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hp
    have hpGT : L < p :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpB).1).1
    omega
  have hUnion : A ∪ B = C := by
    ext p
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter,
      Finset.mem_range, Finset.mem_Ioc, Nat.lt_succ_iff]
    constructor
    · rintro (⟨hpL, hpPrime⟩ | ⟨⟨hpL, hpU⟩, hpPrime⟩)
      · exact ⟨hpL.trans hLU, hpPrime⟩
      · exact ⟨hpU, hpPrime⟩
    · rintro ⟨hpU, hpPrime⟩
      by_cases hpL : p ≤ L
      · exact Or.inl ⟨hpL, hpPrime⟩
      · exact Or.inr ⟨⟨by omega, hpU⟩, hpPrime⟩
  have hcard := congrArg Finset.card hUnion
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  rw [finiteWheel_primeCount_range L,
    finiteWheel_primeCount_range U] at hcard
  simpa [A, B, C, add_comm] using hcard

/-- The square-prefix survivor population is 1 plus precisely the actual
primes above the small-prime cutoff. -/
theorem finiteWheel_squareSurvivorCount_eq_primeCount
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidPrefixWheelCounting (R - 1) (squareRootEndpoint R) +
      Nat.primeCounting (R - 1) =
        Nat.primeCounting (squareRootEndpoint R) + 1 := by
  classical
  let X := squareRootEndpoint R
  let y := R - 1
  have hRsq : R ≤ R ^ 2 := by nlinarith
  have hX0 : 1 ≤ X := by
    dsimp [X, squareRootEndpoint]
    have hRsq4 : 4 ≤ R ^ 2 := by nlinarith
    omega
  have hyX : y ≤ X := by
    dsimp [X, y, squareRootEndpoint]
    omega
  have hset :
      (Finset.Ioc 0 X).filter (lowWheelHighSurvivor y) =
        insert 1 ((Finset.Ioc y X).filter Nat.Prime) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hn0, hnX⟩, hsurv⟩
      rcases (finiteWheel_squareSurvivor_iff_one_or_highPrime
        hR hn0 hnX).mp hsurv with hOne | ⟨hnPrime, hny⟩
      · exact Or.inl hOne
      · exact Or.inr ⟨⟨hny, hnX⟩, hnPrime⟩
    · rintro (hOne | ⟨⟨hny, hnX⟩, hnPrime⟩)
      · subst n
        exact ⟨⟨by omega, hX0⟩,
          (finiteWheel_squareSurvivor_iff_one_or_highPrime
            hR (by omega) hX0).mpr (Or.inl rfl)⟩
      · have hnpos : 0 < n := hnPrime.pos
        exact ⟨⟨hnpos, hnX⟩,
          (finiteWheel_squareSurvivor_iff_one_or_highPrime
            hR hnpos hnX).mpr (Or.inr ⟨hnPrime, hny⟩)⟩
  have hOneNot :
      1 ∉ ((Finset.Ioc y X).filter Nat.Prime) := by
    intro h
    have hp : Nat.Prime 1 := (Finset.mem_filter.mp h).2
    exact (by norm_num : ¬ Nat.Prime 1) hp
  have hsurv :
      vfMidPrefixWheelCounting y X =
        1 + ((Finset.Ioc y X).filter Nat.Prime).card := by
    unfold vfMidPrefixWheelCounting
    rw [hset, Finset.card_insert_of_notMem hOneNot]
    omega
  have hprime := finiteWheel_primeCount_split y X hyX
  dsimp [X, y] at hsurv hprime ⊢
  omega

/-- Legendre's exact finite square-root prime-counting identity; R>=2 keeps
the cofactor-one atom in the physical prefix. -/
theorem finiteWheel_squareLegendre_identity
    (R : ℕ) (hR : 2 ≤ R) :
    (Nat.primeCounting (squareRootEndpoint R) : ℤ) =
      (Nat.primeCounting (R - 1) : ℤ) - 1 +
        ∑ d ∈ (primorial (R - 1)).divisors,
          (ArithmeticFunction.moebius d : ℤ) *
            ((squareRootEndpoint R / d : ℕ) : ℤ) := by
  have hcount := finiteWheel_squareSurvivorCount_eq_primeCount R hR
  have hfloor :=
    finiteWheel_divisorFloor_eq_survivorCount
      (R - 1) (squareRootEndpoint R)
  have hcountZ :
      (vfMidPrefixWheelCounting (R - 1) (squareRootEndpoint R) : ℤ) +
        (Nat.primeCounting (R - 1) : ℤ) =
      (Nat.primeCounting (squareRootEndpoint R) : ℤ) + 1 := by
    exact_mod_cast hcount
  rw [hfloor]
  omega

/-- Full fractional boundary minus finite Euler bulk equals the negative
of the complete Legendre floor sum, including every virtual divisor. -/
theorem finiteWheelFract_sub_density_eq_neg_floor (z X : ℕ) :
    finiteWheelFract z X - (X : ℝ) * vfMidPrefixWheelDensity z =
      -(∑ d ∈ (primorial z).divisors,
        (ArithmeticFunction.moebius d : ℝ) * ((X / d : ℕ) : ℝ)) := by
  classical
  have hsum :
      finiteWheelFract z X - (X : ℝ) * vfMidPrefixWheelDensity z =
        ∑ d ∈ (primorial z).divisors,
          ((ArithmeticFunction.moebius d : ℝ) *
            Int.fract ((X : ℝ) / (d : ℝ)) -
            (X : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ))) := by
    unfold finiteWheelFract
    rw [← finiteWheel_divisorReciprocal_eq_eulerProduct,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsum]
  calc
    (∑ d ∈ (primorial z).divisors,
        ((ArithmeticFunction.moebius d : ℝ) *
          Int.fract ((X : ℝ) / (d : ℝ)) -
          (X : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)))) =
      ∑ d ∈ (primorial z).divisors,
        -((ArithmeticFunction.moebius d : ℝ) *
          ((X / d : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [finiteWheel_fract_eq_div_sub_natDiv X d]
      ring
    _ = _ := by rw [Finset.sum_neg_distrib]

/-- Deterministic main-term ledger for an arbitrary real reference L.
Choosing L=li(X) specializes it to the conventional prime discrepancy. -/
def finiteWheelSquareDeterministic (R : ℕ) (L : ℝ) : ℝ :=
  (squareRootEndpoint R : ℝ) *
      vfMidPrefixWheelDensity (R - 1) +
    (Nat.primeCounting (R - 1) : ℝ) - 1 - L

/-- Exact centered finite-prime discrepancy, independently of the choice of
real reference L. This theorem makes NO RH or numerical bound claim. -/
theorem finiteWheel_squareFractional_centered_eq_reference_sub_pi
    (R : ℕ) (hR : 2 ≤ R) (L : ℝ) :
    finiteWheelFract (R - 1) (squareRootEndpoint R) -
        finiteWheelSquareDeterministic R L =
      L - (Nat.primeCounting (squareRootEndpoint R) : ℝ) := by
  have hleg := finiteWheel_squareLegendre_identity R hR
  have hlegR :
      (Nat.primeCounting (squareRootEndpoint R) : ℝ) =
        (Nat.primeCounting (R - 1) : ℝ) - 1 +
          (∑ d ∈ (primorial (R - 1)).divisors,
            (ArithmeticFunction.moebius d : ℝ) *
              ((squareRootEndpoint R / d : ℕ) : ℝ)) := by
    have hcast := congrArg (fun a : ℤ => (a : ℝ)) hleg
    push_cast at hcast
    exact hcast
  have hfrac := finiteWheelFract_sub_density_eq_neg_floor
    (R - 1) (squareRootEndpoint R)
  unfold finiteWheelSquareDeterministic
  linarith

/-- The absolute RH-scale target is now literally the classical discrepancy.
This is an identity, NOT a bound. -/
theorem finiteWheel_squareFractional_centered_abs
    (R : ℕ) (hR : 2 ≤ R) (L : ℝ) :
    |finiteWheelFract (R - 1) (squareRootEndpoint R) -
        finiteWheelSquareDeterministic R L| =
      |L - (Nat.primeCounting (squareRootEndpoint R) : ℝ)| := by
  rw [finiteWheel_squareFractional_centered_eq_reference_sub_pi R hR L]

-- Exact sign and virtual-divisor compensation; no sign estimate or RH claimed.

#print axioms finiteWheel_squareFractional_centered_eq_reference_sub_pi
#print axioms finiteWheelFract_sub_density_eq_physical_floorError

end RHLean.Analysis
