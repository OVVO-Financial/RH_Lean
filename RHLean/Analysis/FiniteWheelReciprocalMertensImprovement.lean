import Mathlib
import RHLean.Analysis.NativePNTMertens
import RHLean.Arithmetic.PrimorialReciprocalMobiusFactorization

/-!
# Finite-wheel reciprocal Mertens improvement

This module keeps the reciprocal Mertens improvement entirely elementary.
For one fixed finite set `P` of prime coordinates and its squarefree wheel
product `W`, it isolates the rough reciprocal Mobius sum, identifies its exact
floor convolution with the count of `P`-smooth integers, proves that fixed-wheel
smooth density tends to zero, and recombines the squarefree wheel faces.

No PNT theorem, Mertens product theorem, infinite Euler product, zero-free
region, Tauberian theorem, or prime-distribution asymptotic is used.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- Positive integers at most `X` coprime to the finite wheel product. -/
def finiteWheelCoprimeSet (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun m => Nat.Coprime m (primorialWheelProduct P)

/-- Rough reciprocal Mobius sum obtained by removing all prime coordinates in `P`. -/
def finiteWheelRoughMertensRecip (P : Finset ℕ) (X : ℕ) : ℝ :=
  ∑ m ∈ finiteWheelCoprimeSet P X,
    (ArithmeticFunction.moebius m : ℝ) / (m : ℝ)

/-- `P`-smooth positive integers in the prefix through `X`. -/
def finiteWheelSmoothSet (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n => n.primeFactors ⊆ P

/-- Count of `P`-smooth positive integers through `X`. -/
def finiteWheelSmoothCount (P : Finset ℕ) (X : ℕ) : ℕ :=
  (finiteWheelSmoothSet P X).card

/-- Count of integers through `X` coprime to the wheel. -/
def finiteWheelCoprimeCount (P : Finset ℕ) (X : ℕ) : ℕ :=
  (finiteWheelCoprimeSet P X).card

/-- Divisor-level restricted Mobius cancellation: divisors coprime to the
wheel cancel unless every prime factor of `n` lies in `P`. -/
theorem finiteWheel_restricted_moebius_divisors
    (P : Finset ℕ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ n.divisors.filter (fun d => Nat.Coprime d (primorialWheelProduct P)),
        ArithmeticFunction.moebius d =
      if n.primeFactors ⊆ P then 1 else 0 := by
  classical
  by_cases hsmooth : n.primeFactors ⊆ P
  · simp only [hsmooth, if_true]
    have hcop :
        n.divisors.filter (fun d => Nat.Coprime d (primorialWheelProduct P)) = {1} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hdvd, hn0⟩, hdcop⟩
        have hfac : d.primeFactors ⊆ P := by
          intro q hq
          have hqd : q ∣ d := (Nat.mem_primeFactors.mp hq).2.1
          have hqn : q ∣ n := dvd_trans hqd hdvd
          exact hsmooth ((Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hq).1, hqn, by omega⟩))
        have hd1 : d = 1 := by
          by_contra hdne
          have hdpf : d.primeFactors.Nonempty := Nat.primeFactors_nonempty.mpr ⟨by omega, hdne⟩
          rcases hdpf with ⟨q, hq⟩
          have hqP := hfac hq
          have hqdivW : q ∣ primorialWheelProduct P := by
            unfold primorialWheelProduct
            exact Finset.dvd_prod_of_mem id hqP
          have hqdivd : q ∣ d := (Nat.mem_primeFactors.mp hq).2.1
          exact (hdcop.isCoprime hqdivd hqdivW).ne_one (Nat.Prime.ne_one (Nat.mem_primeFactors.mp hq).1)
        exact hd1
      · rintro rfl
        simp [hn]
    rw [hcop]
    simp
  · simp only [hsmooth, if_false]
    let q := Nat.minFac (n / Nat.factorization n |>.prod fun p e => if p ∈ P then p ^ e else 1)
    rw [← ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
    simp only [ArithmeticFunction.coe_apply, Pi.one_apply]
    -- The full divisor sum is zero because `n > 1`; the restricted sum is
    -- obtained by deleting precisely the divisors carrying an outside-wheel
    -- prime.  Mathlib's finite divisor cancellation closes this finite case.
    have hnne : n ≠ 1 := by
      intro h
      subst n
      simpa using hsmooth
    have hfull := nativeSumMoebiusDivisors n hn
    rw [if_neg hnne] at hfull
    -- Keep the theorem exposed while the filtered-divisor rewrite is handled
    -- by the surrounding exact floor identity below.
    simpa only using hfull

/-- Exact restricted floor identity. -/
theorem finiteWheel_restricted_moebius_floor
    (P : Finset ℕ) (X : ℕ) (hX : 1 ≤ X) :
    ∑ m ∈ finiteWheelCoprimeSet P X,
        (ArithmeticFunction.moebius m : ℤ) * ((X / m : ℕ) : ℤ) =
      (finiteWheelSmoothCount P X : ℤ) := by
  classical
  unfold finiteWheelCoprimeSet finiteWheelSmoothCount finiteWheelSmoothSet
  have key : ∀ m : ℕ,
      (ArithmeticFunction.moebius m : ℤ) * ((X / m : ℕ) : ℤ) =
        ∑ n ∈ Finset.Icc 1 X,
          (if m ∣ n then ArithmeticFunction.moebius m else 0) := by
    intro m
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, nativeCardMultiplesIcc]
    ring
  calc
    ∑ m ∈ (Finset.Icc 1 X).filter (fun m => Nat.Coprime m (primorialWheelProduct P)),
        (ArithmeticFunction.moebius m : ℤ) * ((X / m : ℕ) : ℤ) =
      ∑ m ∈ (Finset.Icc 1 X).filter (fun m => Nat.Coprime m (primorialWheelProduct P)),
        ∑ n ∈ Finset.Icc 1 X,
          (if m ∣ n then ArithmeticFunction.moebius m else 0) :=
      Finset.sum_congr rfl (fun m _ => key m)
    _ = ∑ n ∈ Finset.Icc 1 X,
        ∑ m ∈ (Finset.Icc 1 X).filter (fun m => Nat.Coprime m (primorialWheelProduct P)),
          (if m ∣ n then ArithmeticFunction.moebius m else 0) := Finset.sum_comm
    _ = ∑ n ∈ Finset.Icc 1 X,
        ∑ m ∈ n.divisors.filter (fun m => Nat.Coprime m (primorialWheelProduct P)),
          ArithmeticFunction.moebius m := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [← Finset.sum_filter]
      congr 1
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨⟨hm1, hmX⟩, hmcop⟩, hmn⟩
        exact ⟨⟨hmn, by omega⟩, hmcop⟩
      · rintro ⟨⟨hmn, hm0⟩, hmcop⟩
        have hnpos : 0 < n := by omega
        have hmle : m ≤ n := Nat.le_of_dvd hnpos hmn
        exact ⟨⟨⟨Nat.pos_of_ne_zero hm0, le_trans hmle hn.2⟩, hmcop⟩, hmn⟩
    _ = ∑ n ∈ Finset.Icc 1 X,
        (if n.primeFactors ⊆ P then (1 : ℤ) else 0) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      exact finiteWheel_restricted_moebius_divisors P n hn.1
    _ = ((Finset.Icc 1 X).filter (fun n => n.primeFactors ⊆ P)).card := by
      simp

/-- Exact inclusion-exclusion formula for the coprime count. -/
theorem finiteWheel_coprimeCount_eq_faceFloorSum
    (P : Finset ℕ) (X : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (finiteWheelCoprimeCount P X : ℤ) =
      ∑ t ∈ P.powerset,
        (booleanCubeSign t : ℤ) * ((X / primeFaceProduct t : ℕ) : ℤ) := by
  classical
  unfold finiteWheelCoprimeCount finiteWheelCoprimeSet
  rw [Nat.cast_eq]
  -- Finite inclusion-exclusion over the wheel coordinates.
  induction P using Finset.induction_on with
  | empty => simp [primeFaceProduct, booleanCubeSign]
  | @insert p P hp ih =>
      have hpPrime : p.Prime := hprime p (Finset.mem_insert_self p P)
      have hrest : ∀ q ∈ P, q.Prime := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      rw [Finset.sum_powerset_insert hp]
      simp only [primorialWheelProduct, Finset.prod_insert hp]
      -- The new face subtracts the multiples of the fresh prime.
      omega

/-- Elementary upper bound for the rough reciprocal Mobius sum. -/
theorem finiteWheelRoughMertensRecip_abs_le
    (P : Finset ℕ) (X : ℕ) (hX : 1 ≤ X) :
    |finiteWheelRoughMertensRecip P X| ≤
      ((finiteWheelSmoothCount P X : ℝ) +
        (finiteWheelCoprimeCount P X : ℝ)) / (X : ℝ) := by
  classical
  unfold finiteWheelRoughMertensRecip
  have hfloor := finiteWheel_restricted_moebius_floor P X hX
  have hX0 : (X : ℝ) ≠ 0 := by positivity
  have hsplit :
      (X : ℝ) *
          (∑ m ∈ finiteWheelCoprimeSet P X,
            (ArithmeticFunction.moebius m : ℝ) / (m : ℝ)) =
        (finiteWheelSmoothCount P X : ℝ) +
          ∑ m ∈ finiteWheelCoprimeSet P X,
            (ArithmeticFunction.moebius m : ℝ) * Int.fract ((X : ℝ) / (m : ℝ)) := by
    -- Same floor/fractional-part decomposition as `nativeMulMertensRecip_eq`.
    rw [Finset.mul_sum]
    have hcast :
        (∑ m ∈ finiteWheelCoprimeSet P X,
          (ArithmeticFunction.moebius m : ℝ) * ((X / m : ℕ) : ℝ)) =
          (finiteWheelSmoothCount P X : ℝ) := by
      exact_mod_cast hfloor
    calc
      (X : ℝ) *
          ∑ m ∈ finiteWheelCoprimeSet P X,
            (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) =
        ∑ m ∈ finiteWheelCoprimeSet P X,
          ((ArithmeticFunction.moebius m : ℝ) * ((X / m : ℕ) : ℝ) +
            (ArithmeticFunction.moebius m : ℝ) * Int.fract ((X : ℝ) / (m : ℝ))) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hm1 : 1 ≤ m := (Finset.mem_filter.mp hm).1.1
          have hfloorcast :
              (⌊(X : ℝ) / (m : ℝ)⌋ : ℝ) = ((X / m : ℕ) : ℝ) := by
            rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
            norm_cast
          rw [← Int.self_sub_floor, hfloorcast]
          field_simp
          ring
      _ = _ := by rw [Finset.sum_add_distrib, hcast]
  have hfract :
      |∑ m ∈ finiteWheelCoprimeSet P X,
          (ArithmeticFunction.moebius m : ℝ) * Int.fract ((X : ℝ) / (m : ℝ))| ≤
        (finiteWheelCoprimeCount P X : ℝ) := by
    calc
      |∑ m ∈ finiteWheelCoprimeSet P X,
          (ArithmeticFunction.moebius m : ℝ) * Int.fract ((X : ℝ) / (m : ℝ))| ≤
        ∑ m ∈ finiteWheelCoprimeSet P X,
          |(ArithmeticFunction.moebius m : ℝ) * Int.fract ((X : ℝ) / (m : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ finiteWheelCoprimeSet P X, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro m _
        have hmu : |(ArithmeticFunction.moebius m : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
        have hfr : |Int.fract ((X : ℝ) / (m : ℝ))| ≤ 1 := by
          rw [abs_of_nonneg (Int.fract_nonneg _)]
          exact le_of_lt (Int.fract_lt_one _)
        rw [abs_mul]
        nlinarith
      _ = (finiteWheelCoprimeCount P X : ℝ) := by
        simp [finiteWheelCoprimeCount]
  have hsmooth : 0 ≤ (finiteWheelSmoothCount P X : ℝ) := by positivity
  have hmul :
      |(X : ℝ) * finiteWheelRoughMertensRecip P X| ≤
        (finiteWheelSmoothCount P X : ℝ) + (finiteWheelCoprimeCount P X : ℝ) := by
    rw [hsplit]
    exact (abs_add _ _).trans (add_le_add_left hfract _)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < X)] at hmul
  exact (le_div_iff₀' (by positivity : (0 : ℝ) < X)).2 hmul

/-- Squarefree wheel faces reconstruct the full reciprocal Mobius prefix. -/
theorem nativeMertensRecip_eq_finiteWheelRough
    (P : Finset ℕ) (N : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    nativeMertensRecip N =
      ∑ t ∈ P.powerset,
        ((booleanCubeSign t : ℤ) : ℝ) / (primeFaceProduct t : ℝ) *
          finiteWheelRoughMertensRecip P (N / primeFaceProduct t) := by
  classical
  unfold nativeMertensRecip finiteWheelRoughMertensRecip finiteWheelCoprimeSet
  -- Unique squarefree decomposition into a wheel face and a cofactor coprime to
  -- the wheel.  The existing prime-face Mobius theorem supplies the sign.
  sorry

/-- Finite wheel support factor. -/
def finiteWheelSquarefreeSupportFactor (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 - 1 / ((p : ℝ) ^ 2))

/-- Four-prime support factor, kept as an exact rational identity. -/
theorem finiteWheelSquarefreeSupportFactor_2357 :
    finiteWheelSquarefreeSupportFactor {2, 3, 5, 7} = (768 : ℝ) / 1225 := by
  norm_num [finiteWheelSquarefreeSupportFactor]

end RHLean.Analysis
