import RHLean.Geometry.NativeThetaExponentDigits
import RHLean.Geometry.NativeThetaFactorialDigitRatio
import RHLean.Geometry.NativeThetaDigitUnitApproximation
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Uniform binomial readouts for the actual factorial units

Both orientations of the factorial quotient have integral Newton coefficients
of slope one half in the rational valuation ring at a prime. This supplies
the full mixed-product divisibility on the simplex of total Newton degree.
-/

set_option autoImplicit false

open scoped BigOperators

namespace RHLean.Geometry.NativeTheta.ExponentDigits

open RHLean.Geometry.NativeNewtonCongruence

/-- The subring of rationals whose reduced denominator is prime to `p`. -/
abbrev primeLocalRationals (p : ℕ) [Fact p.Prime] : Subring ℚ :=
  (Rat.padicValuation p).valuationSubring.toSubring

/-- The actual factorial quotient as a unit in the rational valuation ring. -/
noncomputable def localFactorialDigitUnit (p g ρ : ℕ) [Fact p.Prime] (hρ : ρ < p ^ g)
    (n : ℕ) : (primeLocalRationals p)ˣ := by
  let x := factorialDigitUnit (p ^ g) ρ n
  have hx : x ≠ 0 := (factorial_digit_unit p g ρ n hρ).1
  have hxv : padicValRat p x = 0 := (factorial_digit_unit p g ρ n hρ).2
  have hval : Rat.padicValuation p x = 1 := by simp [Rat.padicValuation, hx, hxv]
  refine { val := ⟨x, ?_⟩, inv := ⟨x⁻¹, ?_⟩, val_inv := ?_, inv_val := ?_ }
  · exact hval.le
  · change Rat.padicValuation p x⁻¹ ≤ 1
    simp only [map_inv₀, hval, inv_one, le_refl]
  · exact Subtype.ext (mul_inv_cancel₀ hx)
  · exact Subtype.ext (inv_mul_cancel₀ hx)

/-- Select the factorial unit or its reciprocal in its integral ring. -/
noncomputable def signedLocalFactorialDigitUnit (p g ρ : ℕ) [Fact p.Prime]
    (hρ : ρ < p ^ g) (reciprocal : Bool) (n : ℕ) : primeLocalRationals p :=
  if reciprocal then ↑((localFactorialDigitUnit p g ρ hρ n)⁻¹)
  else ↑(localFactorialDigitUnit p g ρ hρ n)

/-- Newton divisibility for every prime power, residue, order, and orientation. -/
theorem pow_dvd_coefficient_factorialDigitUnit (p g ρ : ℕ) [Fact p.Prime] (hρ : ρ < p ^ g)
    (reciprocal : Bool) (j : ℕ) :
    (p : primeLocalRationals p) ^ ((j + 1) / 2) ∣
      coefficient (signedLocalFactorialDigitUnit p g ρ hρ reciprocal) j := by
  let R := primeLocalRationals p
  let φ : R →+* ℚ := R.subtype
  let f (n : ℕ) : R := (localFactorialDigitUnit p g ρ hρ n).val
  let S := Finset.Ico 1 (p ^ g)
  let c (u : ℕ) : R :=
    if hu : u ∈ S then
      ⟨(p : ℚ) ^ g / ((p : ℚ) * u), by
        change Rat.padicValuation p _ ≤ 1
        apply Rat.padicValuation_le_one_iff.mpr
        have hm : 1 ≤ u ∧ u < p ^ g := Finset.mem_Ico.mp hu
        exact (factorialDigitUnit_slope_local p g u (by omega) hm.2).2⟩
    else 0
  let d (u : ℕ) : R := if u ≤ ρ then 1 else 0
  have hs (n : ℕ) : f (n + 1) = f n * ∏ u ∈ S, (1 + (p : R) * c u * ((n : R) + d u)) := by
    apply Subtype.ext
    change factorialDigitUnit (p ^ g) ρ (n + 1) = φ (f n * ∏ u ∈ S, (1 + (p : R) * c u * ((n : R) + d u)))
    rw [map_mul, map_prod]
    have hnon : factorialDigitUnit (p ^ g) ρ n ≠ 0 := (factorial_digit_unit p g ρ n hρ).1
    have hstep := (div_eq_iff hnon).mp (factorialDigitUnit_succ_ratio (p ^ g) ρ n hρ)
    calc
      _ = factorialDigitUnit (p ^ g) ρ n * ∏ u ∈ S,
            (1 + ((p ^ g : ℕ) : ℚ) / u * ((n : ℚ) + if u ≤ ρ then 1 else 0)) :=
        hstep.trans (mul_comm _ _)
      _ = _ := by
        apply congrArg (fun z : ℚ => factorialDigitUnit (p ^ g) ρ n * z)
        apply Finset.prod_congr rfl
        intro u hu
        have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
        have hc : φ (c u) = (p : ℚ) ^ g / ((p : ℚ) * u) := by simp [φ, c, hu]
        have hd : φ (d u) = if u ≤ ρ then 1 else 0 := by
          by_cases h : u ≤ ρ <;> simp [d, h]
        have hslope : (p : ℚ) * ((p : ℚ) ^ g / ((p : ℚ) * u)) = (p : ℚ) ^ g / u := by
          rw [← mul_div_assoc, mul_div_mul_left _ _ hp0]
        simp only [map_add, map_one, map_mul, map_natCast, hc, hd, Nat.cast_pow, hslope]
  have hf : ∀ k, (p : R) ^ ((k + 1) / 2) ∣ coefficient f k :=
    pow_dvd_coefficient_of_affine_product_rec (p : R) S c d f hs
  cases reciprocal with
  | false => exact hf j
  | true =>
    have hf0 : f 0 = 1 := by
      apply Subtype.ext
      change factorialDigitUnit (p ^ g) ρ 0 = 1
      have hfac : (ρ.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero ρ)
      simp [factorialDigitUnit, hfac]
    exact pow_dvd_coefficient_inverse (p : R) f
      (fun n => ((localFactorialDigitUnit p g ρ hρ n)⁻¹).val) hf0 hf
      (fun n => (localFactorialDigitUnit p g ρ hρ n).val_inv) j

/-- The product of the actual signed factorial units has a single total-degree
`2 * (c - 1)` Newton approximation modulo `p ^ c`, independently of the
number of coarse coordinates and their exponents. -/
theorem factorialDigitUnit_pow_dvd_sub_totalReadout {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [Fact p.Prime] (g ρ : ι → ℕ) (hρ : ∀ i, ρ i < p ^ g i)
    (reciprocal : ι → Bool) (c : ℕ) (hc : 0 < c) (n : ι → ℕ) :
    let f (i : ι) := signedLocalFactorialDigitUnit p (g i) (ρ i) (hρ i) (reciprocal i)
    (p : primeLocalRationals p) ^ c ∣ (∏ i, f i (n i)) - totalReadout f (2 * (c - 1)) n := by
  exact pow_dvd_prod_sub_totalReadout (p : primeLocalRationals p) c hc _
    (fun i j => pow_dvd_coefficient_factorialDigitUnit p (g i) (ρ i) (hρ i) (reciprocal i) j) n

/-- A degree 2D readout has enough precision for a depth-D primitive
pairing, after base change and summation with arbitrary integral coefficients.
The residue and coarse exponent data may vary independently at every term. -/
theorem factorialDigitUnit_sum_readout_precision {ι J O : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing O] (p : ℕ) [Fact p.Prime]
    (φ : primeLocalRationals p →+* O) (π : O) (hπ : π ∣ (p : O))
    (D : ℕ) (S : Finset J) (coeff : J → O) (g ρ n : J → ι → ℕ)
    (hρ : ∀ j i, ρ j i < p ^ g j i) (reciprocal : J → ι → Bool) :
    let f (j : J) (i : ι) :=
      signedLocalFactorialDigitUnit p (g j i) (ρ j i) (hρ j i) (reciprocal j i)
    (p : O) ^ D * π ∣
      (∑ j ∈ S, coeff j * φ (∏ i, f j i (n j i))) -
      (∑ j ∈ S, coeff j * φ (totalReadout (f j) (2 * D) (n j))) := by
  dsimp only
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro j _
  rw [← mul_sub]
  apply dvd_mul_of_dvd_right
  have hdepth : (p : O) ^ D * π ∣ (p : O) ^ (D + 1) := by
    rw [pow_succ]
    exact mul_dvd_mul_left _ hπ
  apply hdepth.trans
  obtain ⟨z, hz⟩ := factorialDigitUnit_pow_dvd_sub_totalReadout
    p (g j) (ρ j) (hρ j) (reciprocal j) (D + 1) (Nat.succ_pos D) (n j)
  refine ⟨φ z, ?_⟩
  simpa only [map_sub, map_mul, map_pow, map_natCast, Nat.add_sub_cancel] using
    congrArg φ hz

end RHLean.Geometry.NativeTheta.ExponentDigits
