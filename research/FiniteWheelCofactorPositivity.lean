import Mathlib
import «research.CompleteSquareRootWheelFractionalBoundary»

/-!
# A sharp elementary density invariant and positive complete cofactor fibres

Formalizes 20261109-owner-3/CF2, accepted in 20261109-referee-2/AP.
The stronger invariant 3*z*delta(z)^2 >= 1 improves the sufficient root
threshold from 64 to 47. All nonunit divisor signs and virtual terms remain.
This is a proper-source sign restriction, not a bound for the full li error.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

private theorem density_pos (z : ℕ) : 0 < vfMidPrefixWheelDensity z := by
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast (prime_of_mem_primesUpTo hp).two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hi : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ hp0]
    linarith
  linarith

private theorem density_nonprime_step {n : ℕ} (hp : ¬ n.Prime) :
    vfMidPrefixWheelDensity n = vfMidPrefixWheelDensity (n - 1) := by
  have hs : primesUpTo n = primesUpTo (n - 1) := by
    ext p
    simp only [mem_primesUpTo]
    constructor
    · rintro ⟨hp', hpn⟩
      refine ⟨hp', ?_⟩
      by_contra h
      have he : p = n := by omega
      exact hp (he ▸ hp')
    · rintro ⟨hp', hpn⟩
      exact ⟨hp', by omega⟩
  simp only [vfMidPrefixWheelDensity, hs]

private theorem density_prime_step {p : ℕ} (hp : p.Prime) :
    vfMidPrefixWheelDensity p =
      vfMidPrefixWheelDensity (p - 1) * (1 - (p : ℝ)⁻¹) := by
  have hs : primesUpTo p = insert p (primesUpTo (p - 1)) := by
    ext q
    simp only [mem_primesUpTo, Finset.mem_insert]
    constructor
    · rintro ⟨hq, hqp⟩
      by_cases he : q = p
      · exact Or.inl he
      · exact Or.inr ⟨hq, by omega⟩
    · rintro (rfl | ⟨hq, hqp⟩)
      · exact ⟨hp, le_rfl⟩
      · exact ⟨hq, by omega⟩
  have hn : p ∉ primesUpTo (p - 1) := by
    simp only [mem_primesUpTo, not_and]
    intro _
    have := hp.two_le
    omega
  simp only [vfMidPrefixWheelDensity, hs, Finset.prod_insert hn]
  ring

/-- Sharp in its coefficient: equality occurs at z=3. No PNT is used. -/
theorem finiteWheel_density_sq_lower (z : ℕ) (hz : 2 ≤ z) :
    1 ≤ 3 * (z : ℝ) * vfMidPrefixWheelDensity z ^ 2 := by
  induction z using Nat.strong_induction_on with
  | h z ih =>
    by_cases h2 : z = 2
    · subst z
      norm_num [vfMidPrefixWheelDensity, primesUpTo, Finset.range_succ]
    by_cases h3 : z = 3
    · subst z
      norm_num [vfMidPrefixWheelDensity, primesUpTo, Finset.range_succ]
    have hz4 : 4 ≤ z := by omega
    have hzR : (0 : ℝ) < z := by positivity
    by_cases hp : z.Prime
    · have hz5 : 5 ≤ z := hp.five_le_of_ne_two_of_ne_three h2 h3
      have hnp : ¬ (z - 1).Prime := by
        intro hpred
        have he : z - 1 = 2 :=
          hpred.even_iff.mp (hp.even_sub_one h2)
        omega
      have hpred : z - 1 - 1 = z - 2 := by omega
      rw [density_prime_step hp, density_nonprime_step hnp, hpred]
      have hi := ih (z - 2) (by omega) (by omega)
      have hc : ((z - 2 : ℕ) : ℝ) = (z : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hc] at hi
      have hf : 1 - (z : ℝ)⁻¹ = ((z : ℝ) - 1) / z := by
        field_simp
      calc
        1 ≤ 3 * ((z : ℝ) - 2) * vfMidPrefixWheelDensity (z - 2) ^ 2 := hi
        _ ≤ 3 * (z : ℝ) *
            (vfMidPrefixWheelDensity (z - 2) * (1 - (z : ℝ)⁻¹)) ^ 2 := by
          rw [hf, mul_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc]
          apply (le_div_iff₀ (sq_pos_of_pos hzR)).mpr
          nlinarith [mul_nonneg hzR.le (sq_nonneg (vfMidPrefixWheelDensity (z - 2)))]
    · rw [density_nonprime_step hp]
      have hi := ih (z - 1) (by omega) (by omega)
      have hc : ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hc] at hi
      nlinarith [sq_nonneg (vfMidPrefixWheelDensity (z - 1))]

/-- Real square-root form of the elementary finite-prime density bound. -/
theorem finiteWheel_density_lower (z : ℕ) (hz : 2 ≤ z) :
    1 / Real.sqrt (3 * (z : ℝ)) ≤ vfMidPrefixWheelDensity z := by
  have hzR : (0 : ℝ) < z := by positivity
  have hs : 0 < Real.sqrt (3 * (z : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have he := Real.sq_sqrt (show 0 ≤ 3 * (z : ℝ) by positivity)
  have hd := density_pos z
  have hi := finiteWheel_density_sq_lower z hz
  apply (div_le_iff₀ hs).mpr
  have hsq : (1 : ℝ) ^ 2 ≤
      (vfMidPrefixWheelDensity z * Real.sqrt (3 * (z : ℝ))) ^ 2 := by
    rw [mul_pow, he]
    nlinarith
  exact (sq_le_sq₀ (by norm_num) (mul_nonneg hd.le hs.le)).mp hsq

/-- The coefficient 3 cannot be lowered in the preceding all-z invariant. -/
theorem finiteWheel_density_coefficient_sharp {c : ℝ}
    (h : ∀ z : ℕ, 2 ≤ z → 1 ≤ c * z * vfMidPrefixWheelDensity z ^ 2) :
    3 ≤ c := by
  have h3 := h 3 (by omega)
  norm_num [vfMidPrefixWheelDensity, primesUpTo, Finset.range_succ] at h3
  linarith

/-- Complete nonunit divisor source for one cofactor mask. The mask q is not
a new wheel coordinate: its prime sign must NOT be multiplied into mu(d). -/
def finiteWheelCofactorTotal (z X q : ℕ) : ℝ :=
  ∑ d ∈ (primorial z).divisors.erase 1,
    (ArithmeticFunction.moebius d : ℝ) *
      Int.fract ((X : ℝ) / ((q : ℝ) * d))

private theorem fract_nat_quotient (X d : ℕ) :
    Int.fract ((X : ℝ) / d) = (X : ℝ) / d - ((X / d : ℕ) : ℝ) := by
  have hf : ⌊(X : ℝ) / d⌋ = ((X / d : ℕ) : ℤ) := by
    rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
  rw [← Int.self_sub_floor, hf]
  norm_cast

/-- Exact signed source bridge, with the unit face and all virtual faces.
No primality or coprimality of q is needed for this cofactor identity. -/
theorem finiteWheel_cofactor_eq_count (z X q : ℕ) :
    finiteWheelCofactorTotal z X q =
      vfMidPrefixWheelDensity z * ((X : ℝ) / q) -
        (vfMidPrefixWheelCounting z (X / q) : ℝ) - Int.fract ((X : ℝ) / q) := by
  classical
  have hfull :
      (∑ d ∈ (primorial z).divisors, (ArithmeticFunction.moebius d : ℝ) *
        Int.fract ((X : ℝ) / ((q : ℝ) * d))) =
      vfMidPrefixWheelDensity z * ((X : ℝ) / q) -
        (vfMidPrefixWheelCounting z (X / q) : ℝ) := by
    have hfloor := congrArg (fun a : ℤ => (a : ℝ))
      (finiteWheel_divisorFloor_eq_survivorCount z (X / q))
    push_cast at hfloor
    calc
      _ = ∑ d ∈ (primorial z).divisors,
          ((X : ℝ) / q) * ((ArithmeticFunction.moebius d : ℝ) / d) -
            (ArithmeticFunction.moebius d : ℝ) * (((X / q) / d : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro d _hd
        rw [← Nat.cast_mul, fract_nat_quotient, Nat.cast_mul,
          ← Nat.div_div_eq_div_mul, ← div_div]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
          finiteWheel_divisorReciprocal_eq_eulerProduct, hfloor]
        ring
  have h1 : 1 ∈ (primorial z).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, (primorial_pos z).ne'⟩
  have hsplit := Finset.sum_erase_add (s := (primorial z).divisors)
    (fun d => (ArithmeticFunction.moebius d : ℝ) *
      Int.fract ((X : ℝ) / ((q : ℝ) * d))) h1
  simp only [ArithmeticFunction.moebius_one, Int.cast_one, Nat.cast_one,
    mul_one, one_mul] at hsplit
  rw [hfull] at hsplit
  unfold finiteWheelCofactorTotal
  linarith

private theorem saturated_count {z N : ℕ} (hN : 1 ≤ N) (hNz : N ≤ z) :
    vfMidPrefixWheelCounting z N = 1 := by
  classical
  have hs : (Finset.Ioc 0 N).filter (lowWheelHighSurvivor z) = {1} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hn0, hnN⟩, hsurv⟩
      by_contra hn1
      have hp := Nat.minFac_prime hn1
      have hpd := Nat.minFac_dvd n
      exact hsurv n.minFac
        (mem_primesUpTo.mpr ⟨hp, (Nat.le_of_dvd hn0 hpd).trans (hnN.trans hNz)⟩) hpd
    · rintro rfl
      refine ⟨⟨by omega, hN⟩, ?_⟩
      intro p hp hpd
      exact (prime_of_mem_primesUpTo hp).not_dvd_one hpd
  simp only [vfMidPrefixWheelCounting, hs, Finset.card_singleton]

/-- Saturation retains precisely one surviving cofactor, the original prime
atom when q is prime. The root-prime endpoint is included. -/
theorem finiteWheel_cofactor_square_eq (R q : ℕ) (hR : 2 ≤ R)
    (hq : R ≤ q) (hq2 : q < 2 * R) :
    finiteWheelCofactorTotal (R - 1) (squareRootEndpoint R) q =
      vfMidPrefixWheelDensity (R - 1) * ((squareRootEndpoint R : ℝ) / q) -
        1 - Int.fract ((squareRootEndpoint R : ℝ) / q) := by
  have hq0 : 0 < q := by omega
  have hX : squareRootEndpoint R + 1 = R ^ 2 := by
    unfold squareRootEndpoint
    exact Nat.sub_add_cancel (by nlinarith)
  have hqX : q ≤ squareRootEndpoint R := by nlinarith
  have hN : 1 ≤ squareRootEndpoint R / q := (Nat.one_le_div_iff hq0).mpr hqX
  have hlt : squareRootEndpoint R / q < R := by
    apply (Nat.div_lt_iff_lt_mul hq0).mpr
    nlinarith
  rw [finiteWheel_cofactor_eq_count, saturated_count hN (by omega)]
  norm_num

/-- Exact two-sided interval of width one for each complete signed fibre. -/
theorem finiteWheel_cofactor_square_bounds (R q : ℕ) (hR : 2 ≤ R)
    (hq : R ≤ q) (hq2 : q < 2 * R) :
    vfMidPrefixWheelDensity (R - 1) * ((squareRootEndpoint R : ℝ) / q) - 2 <
      finiteWheelCofactorTotal (R - 1) (squareRootEndpoint R) q ∧
    finiteWheelCofactorTotal (R - 1) (squareRootEndpoint R) q ≤
      vfMidPrefixWheelDensity (R - 1) * ((squareRootEndpoint R : ℝ) / q) - 1 := by
  rw [finiteWheel_cofactor_square_eq R q hR hq hq2]
  constructor
  · linarith [Int.fract_lt_one ((squareRootEndpoint R : ℝ) / q)]
  · linarith [Int.fract_nonneg ((squareRootEndpoint R : ℝ) / q)]

/-- A stronger sufficient threshold than CF2's 64. This analytic/cofactor
statement does not require q prime; the actual-prime aggregate follows. -/
theorem finiteWheel_cofactor_pos (R q : ℕ) (hR : 47 ≤ R)
    (hq : R ≤ q) (hq2 : q < 2 * R) :
    0 < finiteWheelCofactorTotal (R - 1) (squareRootEndpoint R) q := by
  have hR' : (47 : ℝ) ≤ R := by exact_mod_cast hR
  have hq' : (q : ℝ) ≤ 2 * R - 1 := by
    have : q + 1 ≤ 2 * R := by omega
    have hc : (q : ℝ) + 1 ≤ 2 * R := by exact_mod_cast this
    linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hX : (squareRootEndpoint R : ℝ) = (R : ℝ) ^ 2 - 1 := by
    unfold squareRootEndpoint
    rw [Nat.cast_sub (by nlinarith : 1 ≤ R ^ 2), Nat.cast_pow, Nat.cast_one]
  have hx : (R : ℝ) / 2 < (squareRootEndpoint R : ℝ) / q := by
    apply (lt_div_iff₀ hq0).mpr
    rw [hX]
    nlinarith [mul_le_mul_of_nonneg_left hq' (show 0 ≤ (R : ℝ) by positivity)]
  have hd := density_pos (R - 1)
  have hi := finiteWheel_density_sq_lower (R - 1) (by omega)
  have hc : ((R - 1 : ℕ) : ℝ) = (R : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hc] at hi
  have hgap : 48 * ((R : ℝ) - 1) < (R : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (R : ℝ) - 47 by linarith)
      (show 0 ≤ (R : ℝ) - 1 by linarith)]
  have hm := mul_lt_mul_of_pos_right hgap (sq_pos_of_pos hd)
  have hfour : 4 < vfMidPrefixWheelDensity (R - 1) * (R : ℝ) := by
    have hprod : 0 ≤ vfMidPrefixWheelDensity (R - 1) * (R : ℝ) := by positivity
    have hsq : (4 : ℝ) ^ 2 < (vfMidPrefixWheelDensity (R - 1) * (R : ℝ)) ^ 2 := by
      nlinarith
    exact (sq_lt_sq₀ (by norm_num) hprod).mp hsq
  have hxmul := mul_lt_mul_of_pos_left hx hd
  have hb := (finiteWheel_cofactor_square_bounds R q (by omega) hq hq2).1
  nlinarith

/-- The original genuine-prime mask; no occurrence is counted twice. -/
theorem finiteWheel_primeFibre_sum_nonneg (R : ℕ) (hR : 47 ≤ R) :
    0 ≤ ∑ q ∈ (Finset.Ico R (2 * R)).filter Nat.Prime,
      finiteWheelCofactorTotal (R - 1) (squareRootEndpoint R) q := by
  apply Finset.sum_nonneg
  intro q hq
  have hqi := Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1
  exact (finiteWheel_cofactor_pos R q hR hqi.1 hqi.2).le

end RHLean.Analysis
