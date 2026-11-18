import «research.NYMAN_FLAT_TAPER_RETURN_20261104»

/-!
Finite complete-covariance core of 20261118-analytic-0909-EST/PV2,
independently accepted with scope in 20261118-referee-1203-EST/FC.
The original ordered gcd kernel is retained before any positivity argument.
This is not a bound on the location-weighted infinite Nyman norm. The
period-average interpretation of this kernel is not a theorem of this file.
-/

set_option autoImplicit false

noncomputable section
open Finset
open scoped BigOperators ArithmeticFunction.zeta

namespace RHLean.Analysis

def nymanJordanTwo : ArithmeticFunction Real :=
  ArithmeticFunction.pmul (ArithmeticFunction.pow 2 : ArithmeticFunction Real)
    (ArithmeticFunction.prodPrimeFactors (fun p => 1 - 1 / (p : Real)^2))

def nymanCovariance (N : Nat) (a : Nat -> Real) : Real :=
  (1 / 12 : Real) * ∑ k ∈ Icc 2 N, ∑ l ∈ Icc 2 N,
    (a k / k) * (a l / l) * ((Nat.gcd k l : Real)^2 - 1)

private theorem jordan_formula (n : Nat) (hn : n ≠ 0) :
    nymanJordanTwo n = (n : Real)^2 *
      ∏ p ∈ n.primeFactors, (1 - 1 / (p : Real)^2) := by
  simp [nymanJordanTwo, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.prodPrimeFactors_apply hn, ArithmeticFunction.pow_apply]

private theorem jordan_one : nymanJordanTwo 1 = 1 := by
  norm_num [jordan_formula 1 (by decide)]

private theorem jordan_prime_power (p i : Nat) (hp : p.Prime) :
    nymanJordanTwo (p^(i+1)) =
      (p : Real)^(2*(i+1)) - (p : Real)^(2*i) := by
  rw [jordan_formula _ (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow (by omega : i+1 ≠ 0) hp]
  simp only [Finset.prod_singleton, Nat.cast_pow]
  have hp0 : (p : Real) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [show 2*(i+1) = (i+1)*2 by omega, show 2*i = i*2 by omega]
  simp only [pow_mul, pow_succ]
  field_simp [hp0]

/-- The exact arithmetic divisor identity, with the unit divisor retained. -/
theorem nyman_jordan_two_divisor_sum (n : Nat) :
    ∑ d ∈ n.divisors, nymanJordanTwo d = (n : Real)^2 := by
  have hj : nymanJordanTwo.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_pow.natCast.pmul
      (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _)
  have hz : (ArithmeticFunction.zeta : ArithmeticFunction Real).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast
  have he : (ArithmeticFunction.zeta : ArithmeticFunction Real) * nymanJordanTwo =
      (ArithmeticFunction.pow 2 : ArithmeticFunction Real) := by
    apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
      _ (hz.mul hj) _ ArithmeticFunction.isMultiplicative_pow.natCast).mpr
    intro p i hp
    simp only [ArithmeticFunction.coe_zeta_mul_apply,
      ArithmeticFunction.natCoe_apply, ArithmeticFunction.pow_apply]
    simp only [show ¬ (2 = 0 ∧ p^i = 0) by omega, ite_false, Nat.cast_pow]
    rw [Nat.sum_divisors_prime_pow hp]
    induction i with
    | zero => simp [jordan_one]
    | succ i ih =>
        rw [Finset.sum_range_succ, ih, jordan_prime_power p i hp]
        rw [← pow_mul, ← pow_mul]
        rw [show i*2 = 2*i by omega, show (i+1)*2 = 2*(i+1) by omega]
        ring
  have hh := congrArg (fun f : ArithmeticFunction Real => f n) he
  change ((ArithmeticFunction.zeta : ArithmeticFunction Real) * nymanJordanTwo) n =
    (ArithmeticFunction.pow 2 : ArithmeticFunction Real) n at hh
  rw [ArithmeticFunction.coe_zeta_mul_apply] at hh
  simpa [ArithmeticFunction.pow_apply] using hh

private theorem factor_bounds (k : Nat) (hk : 2 <= k) :
    0 <= 1 - 1 / (k : Real)^2 ∧ 1 - 1 / (k : Real)^2 <= 1 := by
  have hkr : (2 : Real) <= k := by exact_mod_cast hk
  have hsq : (1 : Real) <= (k : Real)^2 := by nlinarith
  have hinv : 1 / (k : Real)^2 <= 1 := (div_le_one (by positivity)).mpr hsq
  constructor
  · linarith
  · have : 0 <= 1 / (k : Real)^2 := by positivity
    linarith

private theorem product_interval (n : Nat) (hn : 1 <= n) :
    ∏ k ∈ Icc 2 n, (1 - 1 / (k : Real)^2) =
      ((n : Real) + 1) / (2 * n) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      have hn0 : (n : Real) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hs0 : (n : Real) + 1 ≠ 0 := by positivity
      push_cast
      field_simp [hn0, hs0]
      ring

/-- A telescoping finite product proves the uniform half bound without zeta. -/
theorem nyman_jordan_two_lower (n : Nat) :
    (n : Real)^2 / 2 <= nymanJordanTwo n := by
  by_cases hn : n = 0
  · simp [hn]
  have hn1 : 1 <= n := by omega
  have hs : n.primeFactors ⊆ Icc 2 n := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
      Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)⟩
  have hprod := Finset.prod_le_prod_of_subset_of_le_one₀ hs
    (fun k hk => (factor_bounds k (Finset.mem_Icc.mp hk).1).1)
    (fun k hk _ => (factor_bounds k (Finset.mem_Icc.mp hk).1).2)
  rw [product_interval n hn1] at hprod
  have hhalf : (1 / 2 : Real) <= ((n : Real)+1)/(2*n) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  rw [jordan_formula n hn]
  have hh := mul_le_mul_of_nonneg_left (hhalf.trans hprod) (sq_nonneg (n : Real))
  nlinarith

private theorem jordan_nonneg (n : Nat) : 0 <= nymanJordanTwo n :=
  (by positivity : (0 : Real) <= (n : Real)^2/2).trans (nyman_jordan_two_lower n)

private theorem kernel_divisor_sum (N k l : Nat)
    (hk : k ∈ Icc 2 N) :
    ∑ d ∈ Icc 2 N, (if d ∣ k ∧ d ∣ l then nymanJordanTwo d else 0) =
      (Nat.gcd k l : Real)^2 - 1 := by
  have hk0 : 0 < k := by have := (Finset.mem_Icc.mp hk).1; omega
  have hg0 : Nat.gcd k l ≠ 0 := (Nat.gcd_pos_of_pos_left l hk0).ne'
  have hset : (Icc 1 N).filter (fun d => d ∣ k ∧ d ∣ l) = (Nat.gcd k l).divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · exact fun h => ⟨h.2, hg0⟩
    · intro h
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos h.1.1 hk0
      exact ⟨⟨hd0, (Nat.le_of_dvd hk0 h.1.1).trans (Finset.mem_Icc.mp hk).2⟩, h.1⟩
  have hall : (∑ d ∈ Icc 1 N,
      if d ∣ k ∧ d ∣ l then nymanJordanTwo d else 0) = (Nat.gcd k l : Real)^2 := by
    rw [← Finset.sum_filter, hset, nyman_jordan_two_divisor_sum]
  rw [nyman_sum_one_split N (by have := (Finset.mem_Icc.mp hk).2; omega)] at hall
  simp only [one_dvd, and_self, ite_true, jordan_one] at hall
  linarith

/-- Positive coordinates of the complete ordered covariance, not a diagonal truncation. -/
theorem nyman_covariance_divisor_squares (N : Nat) (a : Nat -> Real) :
    12 * nymanCovariance N a =
      ∑ d ∈ Icc 2 N, nymanJordanTwo d *
        (∑ k ∈ Icc 2 N, if d ∣ k then a k / k else 0)^2 := by
  unfold nymanCovariance
  rw [show (12 : Real) * ((1/12) *
      (∑ k ∈ Icc 2 N, ∑ l ∈ Icc 2 N,
        (a k/k)*(a l/l)*((Nat.gcd k l : Real)^2-1))) =
      ∑ k ∈ Icc 2 N, ∑ l ∈ Icc 2 N,
        (a k/k)*(a l/l)*((Nat.gcd k l : Real)^2-1) by ring]
  trans ∑ k ∈ Icc 2 N, ∑ l ∈ Icc 2 N, ∑ d ∈ Icc 2 N,
    nymanJordanTwo d * (if d ∣ k then a k/k else 0) *
      (if d ∣ l then a l/l else 0)
  · apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l _
    rw [← kernel_divisor_sum N k l hk, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hdk : d ∣ k <;> by_cases hdl : d ∣ l <;> simp [hdk, hdl]
    ring
  · trans ∑ k ∈ Icc 2 N, ∑ d ∈ Icc 2 N, ∑ l ∈ Icc 2 N,
      nymanJordanTwo d * (if d ∣ k then a k/k else 0) *
        (if d ∣ l then a l/l else 0)
    · apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

private theorem singleton_sum (N q : Nat) (a : Nat -> Real)
    (hq : q ∈ Icc 2 N) (htop : N < 2*q) :
    (∑ k ∈ Icc 2 N, if q ∣ k then a k/k else 0) = a q/q := by
  rw [Finset.sum_eq_single q]
  · simp
  · intro k hk hkq
    have hn : ¬q ∣ k := by
      intro hdiv
      obtain ⟨t, ht⟩ := hdiv
      have hq0 : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
      have ht2 : 2 <= t := by
        by_contra hn
        have : t=0 ∨ t=1 := by omega
        rcases this with rfl | rfl <;> simp_all
      have hkN := (Finset.mem_Icc.mp hk).2
      nlinarith
    simp [hn]
  · exact fun hn => (hn hq).elim

/-- Every final-support upper-half coefficient is visible, regardless of other coefficients. -/
theorem nyman_covariance_singleton_lower (N : Nat) (a : Nat -> Real) (s : Finset Nat)
    (hs : s ⊆ Icc 2 N) (htop : ∀ q ∈ s, N < 2*q) :
    ∑ q ∈ s, (a q)^2 <= 24 * nymanCovariance N a := by
  have hlocal : (∑ q ∈ s, (a q)^2/2) <=
      ∑ q ∈ s, nymanJordanTwo q *
        (∑ k ∈ Icc 2 N, if q ∣ k then a k/k else 0)^2 := by
    apply Finset.sum_le_sum
    intro q hq
    rw [singleton_sum N q a (hs hq) (htop q hq)]
    have hq0 : (q : Real) ≠ 0 := by
      exact_mod_cast (show q ≠ 0 by have := (Finset.mem_Icc.mp (hs hq)).1; omega)
    have hh := mul_le_mul_of_nonneg_right (nyman_jordan_two_lower q)
      (sq_nonneg (a q / q))
    have he : (q : Real)^2/2 * (a q/q)^2 = (a q)^2/2 := by
      field_simp [hq0]
    rwa [he] at hh
  have hglobal : (∑ q ∈ s, nymanJordanTwo q *
      (∑ k ∈ Icc 2 N, if q ∣ k then a k/k else 0)^2) <=
      ∑ q ∈ Icc 2 N, nymanJordanTwo q *
        (∑ k ∈ Icc 2 N, if q ∣ k then a k/k else 0)^2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hs
    intro q _ _
    exact mul_nonneg (jordan_nonneg q) (sq_nonneg _)
  rw [← nyman_covariance_divisor_squares] at hglobal
  rw [← Finset.sum_div] at hlocal
  linarith

/-- PV2's finite repair restriction on the literal original two-band coefficient.
No moment condition is needed, and H <= 4K suffices for this finite statement. -/
theorem nyman_flat_same_support_repair (K H : Nat)
    (hK : 1 <= K) (hH : 1 <= H) (hHK : H <= 4*K)
    (A Z : Real) (e : Nat -> Real) :
    (∑ q ∈ Ioc (4*K) (5*K),
      (e q - (ArithmeticFunction.moebius q : Real) *
        Real.log ((6*K : Nat) / (q : Real)) / nymanFlatScale (6*K) H)^2) <=
      24 * nymanCovariance (6*K) (fun k =>
        nymanFlatCoefficient (6*K) H
          (fun j => if j ∈ Ioc (3*K) (4*K) then A
            else if j ∈ Ioc (5*K) (6*K) then Z else 0) k + e k) := by
  have hs : Ioc (4*K) (5*K) ⊆ Icc 2 (6*K) := by
    intro q hq
    have := Finset.mem_Ioc.mp hq
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hh := nyman_covariance_singleton_lower (6*K)
    (fun k => nymanFlatCoefficient (6*K) H
      (fun j => if j ∈ Ioc (3*K) (4*K) then A
        else if j ∈ Ioc (5*K) (6*K) then Z else 0) k + e k)
    (Ioc (4*K) (5*K)) hs (by intro q hq; have := Finset.mem_Ioc.mp hq; omega)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro q hq
  have hqi := Finset.mem_Ioc.mp hq
  have h1 : q ∉ Ioc (3*K) (4*K) := by simp only [Finset.mem_Ioc]; omega
  have h2 : q ∉ Ioc (5*K) (6*K) := by simp only [Finset.mem_Ioc]; omega
  rw [nymanFlatCoefficient, nymanFlatKernel_eq_original (6*K) H q
    (by omega) hH (by omega), max_eq_right (by omega : H <= q)]
  simp only [h1, h2, ite_false]
  ring

end RHLean.Analysis
