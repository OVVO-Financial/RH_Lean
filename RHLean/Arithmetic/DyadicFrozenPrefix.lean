import Mathlib

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Arithmetic

/-- The finite dyadic block `(N,2N]`. -/
def dyadicBlock (N : ℕ) : Finset ℕ := Finset.Icc (N + 1) (2 * N)

/-- The number of multiples of `d` in `(N,2N]`. -/
def dyadicDivisorWeight (N d : ℕ) : ℕ :=
  ((dyadicBlock N).filter fun n => d ∣ n).card

/-- Every proper divisor of an integer in `(N,2N]` lies in the frozen prefix. -/
theorem properDivisor_le_base {N n d : ℕ}
    (hnN : N < n) (hn2 : n ≤ 2 * N) (hd : d ∣ n) (hdn : d < n) : d ≤ N := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp_all
  nlinarith

/-- The proper divisors of `n` that lie in the frozen prefix. -/
def frozenProperDivisors (N n : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun d => d ∣ n ∧ d < n

/-- Möbius is reconstructed from its proper-divisor values. -/
theorem moebius_eq_neg_sum_properDivisors {n : ℕ} (hn : 1 < n) :
    μ n = -∑ d ∈ n.divisors.erase n, μ d := by
  have hconv :
      ((ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n) =
        (1 : ArithmeticFunction ℤ) n :=
    congrArg (fun f : ArithmeticFunction ℤ => f n)
      ArithmeticFunction.moebius_mul_coe_zeta
  have hsum : ∑ d ∈ n.divisors, μ d = 0 := by
    rw [ArithmeticFunction.coe_mul_zeta_apply] at hconv
    rw [ArithmeticFunction.one_apply, if_neg hn.ne'] at hconv
    exact hconv
  have hnmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have hsplit : (∑ d ∈ n.divisors.erase n, μ d) + μ n = 0 := by
    rw [Finset.sum_erase_add (s := n.divisors) (f := fun d => μ d) hnmem]
    exact hsum
  linarith

/-- On `(N,2N]`, the frozen proper-divisor set is the full proper-divisor set. -/
theorem frozenProperDivisors_eq {N n : ℕ}
    (hnN : N < n) (hn2 : n ≤ 2 * N) :
    frozenProperDivisors N n = n.divisors.erase n := by
  have hn : 1 < n := by omega
  ext d
  simp only [frozenProperDivisors, Finset.mem_filter, Finset.mem_range,
    Finset.mem_erase, Nat.mem_divisors]
  constructor
  · rintro ⟨hdN, hdvd, hdn⟩
    exact ⟨Nat.ne_of_lt hdn, hdvd, by omega⟩
  · rintro ⟨hdn, hdvd, _⟩
    have hle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hlt : d < n := lt_of_le_of_ne hle hdn
    exact ⟨Nat.lt_succ_iff.mpr (properDivisor_le_base hnN hn2 hdvd hlt), hdvd, hlt⟩

/-- Pointwise frozen-prefix reconstruction on the next dyadic block. -/
theorem moebius_eq_neg_frozenPrefixSum {N n : ℕ}
    (hnN : N < n) (hn2 : n ≤ 2 * N) :
    μ n = -∑ d ∈ frozenProperDivisors N n, μ d := by
  have hn : 1 < n := by omega
  rw [frozenProperDivisors_eq hnN hn2]
  exact moebius_eq_neg_sum_properDivisors hn

/-- Exact finite divisor-incidence form of the dyadic increment. -/
theorem dyadic_moebius_increment_eq_frozen_weighted_sum (N : ℕ) :
    (∑ n ∈ dyadicBlock N, μ n) =
      -∑ d ∈ Finset.range (N + 1), (dyadicDivisorWeight N d : ℤ) * μ d := by
  classical
  calc
    (∑ n ∈ dyadicBlock N, μ n) =
        ∑ n ∈ dyadicBlock N, -∑ d ∈ frozenProperDivisors N n, μ d := by
          apply Finset.sum_congr rfl
          intro n hn
          simp only [dyadicBlock, Finset.mem_Icc] at hn
          exact moebius_eq_neg_frozenPrefixSum hn.1 hn.2
    _ = -∑ d ∈ Finset.range (N + 1),
          ∑ n ∈ dyadicBlock N, if d ∣ n then μ d else 0 := by
          simp only [frozenProperDivisors, Finset.sum_neg_distrib, Finset.sum_filter]
          rw [Finset.sum_comm]
          apply congrArg Neg.neg
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro n hn
          have hdN : d ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
          have hNn : N < n := by
            exact (Finset.mem_Icc.mp hn).1
          have hdn : d < n := lt_of_le_of_lt hdN hNn
          simp [hdn]
    _ = -∑ d ∈ Finset.range (N + 1), (dyadicDivisorWeight N d : ℤ) * μ d := by
          apply congrArg Neg.neg
          apply Finset.sum_congr rfl
          intro d hd
          change (∑ n ∈ dyadicBlock N, if d ∣ n then μ d else 0) =
            (((dyadicBlock N).filter fun n => d ∣ n).card : ℤ) * μ d
          rw [← Finset.sum_filter]
          simp

/-- The finite prime contribution in the new dyadic block. -/
def dyadicPrimeBirths (N : ℕ) : ℕ :=
  ((dyadicBlock N).filter Nat.Prime).card

/-- The inherited composite Möbius mass in the new dyadic block. -/
def dyadicInheritedCompositeMass (N : ℕ) : ℤ :=
  ∑ n ∈ (dyadicBlock N).filter (fun n => ¬ Nat.Prime n), μ n

/-- Exact prime-birth versus inherited-composite decomposition. -/
theorem dyadic_increment_eq_inherited_sub_primeBirths (N : ℕ) :
    (∑ n ∈ dyadicBlock N, μ n) =
      dyadicInheritedCompositeMass N - dyadicPrimeBirths N := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (s := dyadicBlock N) (p := Nat.Prime)]
  have hprime :
      (∑ n ∈ (dyadicBlock N).filter Nat.Prime, μ n) =
        -(dyadicPrimeBirths N : ℤ) := by
    calc
      (∑ n ∈ (dyadicBlock N).filter Nat.Prime, μ n) =
          ∑ _n ∈ (dyadicBlock N).filter Nat.Prime, (-1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact ArithmeticFunction.moebius_apply_prime (Finset.mem_filter.mp hn).2
      _ = -(dyadicPrimeBirths N : ℤ) := by
            simp [dyadicPrimeBirths]
  rw [hprime]
  change -(dyadicPrimeBirths N : ℤ) + dyadicInheritedCompositeMass N =
    dyadicInheritedCompositeMass N - dyadicPrimeBirths N
  abel

/-- The increment of an integer-valued prefix function across one doubling. -/
def dyadicIncrement (F : ℕ → ℤ) (N : ℕ) : ℤ := F (2 * N) - F N

/-- Exact finite partial-sum identity underlying the infinite dyadic series. -/
theorem dyadic_telescoping_series (F : ℕ → ℤ) (N K : ℕ) :
    F (2 ^ K * N) =
      F N + ∑ j ∈ Finset.range K, dyadicIncrement F (2 ^ j * N) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      calc
        F (2 ^ (K + 1) * N) = F (2 * (2 ^ K * N)) := by
          congr 1
          simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm]
        _ = F (2 ^ K * N) + dyadicIncrement F (2 ^ K * N) := by
          simp [dyadicIncrement]
        _ = (F N + ∑ j ∈ Finset.range K, dyadicIncrement F (2 ^ j * N)) +
              dyadicIncrement F (2 ^ K * N) := by rw [ih]
        _ = F N +
              (∑ j ∈ Finset.range K, dyadicIncrement F (2 ^ j * N) +
                dyadicIncrement F (2 ^ K * N)) := by
          exact add_assoc _ _ _

/-- The Möbius prefix, including `0`; the zero term contributes nothing. -/
def moebiusPrefix (N : ℕ) : ℤ := ∑ n ∈ Finset.range (N + 1), μ n

/-- Möbius prefixes are exact partial sums of their permanent dyadic increments. -/
theorem moebiusPrefix_dyadic_series (N K : ℕ) :
    moebiusPrefix (2 ^ K * N) =
      moebiusPrefix N +
        ∑ j ∈ Finset.range K, dyadicIncrement moebiusPrefix (2 ^ j * N) :=
  dyadic_telescoping_series moebiusPrefix N K

/-- A typed finite cancellation premise for the dyadic frozen-prefix operator. -/
def DyadicFrozenPrefixCancellation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |((∑ n ∈ dyadicBlock N, μ n : ℤ) : ℝ)| ≤ ε * N

/-! ## Arbitrary frozen subdoubling runs -/

/-- A half-open physical run `[N,L)`.  When `L ≤ 2N`, every proper divisor of
every site in this run lies strictly below the initial cutoff `N`. -/
def frozenRunBlock (N L : ℕ) : Finset ℕ := Finset.Ico N L

/-- Number of sites in `[N,L)` hit by the old divisor coordinate `d`. -/
def frozenRunDivisorWeight (N L d : ℕ) : ℕ :=
  ((frozenRunBlock N L).filter fun n => d ∣ n).card

/-- Proper divisors of one site read only from the prefix strictly below `N`. -/
def frozenRunProperDivisors (N n : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun d => d ∣ n

/-- In a subdoubling run, every proper divisor lies strictly below the run's
left endpoint.  This is the strict version needed for a genuinely frozen
prefix: no divisor coordinate created during the run can be consulted later in
the same run. -/
theorem properDivisor_lt_frozenRunBase {N L n d : ℕ}
    (hL : L ≤ 2 * N)
    (hn : n ∈ frozenRunBlock N L)
    (hd : d ∣ n) (hdn : d < n) : d < N := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp_all [frozenRunBlock]
  have hnlt : d * k < 2 * N := by
    exact lt_of_lt_of_le (Finset.mem_Ico.mp hn).2 hL
  nlinarith

/-- On a subdoubling run the strict frozen prefix is exactly the complete set of
proper divisors of every visited site. -/
theorem frozenRunProperDivisors_eq {N L n : ℕ}
    (hL : L ≤ 2 * N)
    (hn : n ∈ frozenRunBlock N L) :
    frozenRunProperDivisors N n = n.divisors.erase n := by
  have hnLower : N ≤ n := (Finset.mem_Ico.mp hn).1
  have hnpos : 0 < n := by omega
  ext d
  simp only [frozenRunProperDivisors, Finset.mem_filter, Finset.mem_range,
    Finset.mem_erase, Nat.mem_divisors]
  constructor
  · rintro ⟨hdN, hdvd⟩
    have hdn : d < n := lt_of_lt_of_le hdN hnLower
    exact ⟨Nat.ne_of_lt hdn, hdvd, hnpos.ne'⟩
  · rintro ⟨hdne, hdvd, _⟩
    have hle : d ≤ n := Nat.le_of_dvd hnpos hdvd
    have hlt : d < n := lt_of_le_of_ne hle hdne
    exact ⟨properDivisor_lt_frozenRunBase hL hn hdvd hlt, hdvd⟩

/-- Pointwise frozen-prefix reconstruction on an arbitrary subdoubling run. -/
theorem moebius_eq_neg_frozenRunPrefixSum {N L n : ℕ}
    (hN : 2 ≤ N) (hL : L ≤ 2 * N)
    (hn : n ∈ frozenRunBlock N L) :
    μ n = -∑ d ∈ frozenRunProperDivisors N n, μ d := by
  have hnLower : N ≤ n := (Finset.mem_Ico.mp hn).1
  have hn1 : 1 < n := by omega
  rw [frozenRunProperDivisors_eq hL hn]
  exact moebius_eq_neg_sum_properDivisors hn1

/-- **Frozen-run identity.**  On every half-open run `[N,L)` with `L ≤ 2N`, the
entire new Möbius mass is one static linear functional of the prefix strictly
below `N`.  No Möbius value created inside the run appears on the right-hand
side. -/
theorem frozenRun_moebius_increment_eq_frozen_weighted_sum
    (N L : ℕ) (hN : 2 ≤ N) (hL : L ≤ 2 * N) :
    (∑ n ∈ frozenRunBlock N L, μ n) =
      -∑ d ∈ Finset.range N, (frozenRunDivisorWeight N L d : ℤ) * μ d := by
  classical
  calc
    (∑ n ∈ frozenRunBlock N L, μ n) =
        ∑ n ∈ frozenRunBlock N L,
          -∑ d ∈ frozenRunProperDivisors N n, μ d := by
            apply Finset.sum_congr rfl
            intro n hn
            exact moebius_eq_neg_frozenRunPrefixSum hN hL hn
    _ = -∑ d ∈ Finset.range N,
          ∑ n ∈ frozenRunBlock N L, if d ∣ n then μ d else 0 := by
            simp only [frozenRunProperDivisors, Finset.sum_neg_distrib,
              Finset.sum_filter]
            rw [Finset.sum_comm]
    _ = -∑ d ∈ Finset.range N,
          (frozenRunDivisorWeight N L d : ℤ) * μ d := by
            apply congrArg Neg.neg
            apply Finset.sum_congr rfl
            intro d _hd
            change (∑ n ∈ frozenRunBlock N L, if d ∣ n then μ d else 0) =
              (((frozenRunBlock N L).filter fun n => d ∣ n).card : ℤ) * μ d
            rw [← Finset.sum_filter]
            simp

/-! ## Static square-run correlation -/

/-- Integer Möbius mass of the repository's half-open complete-square run
`[a^2,(b+1)^2)`. -/
def squareFrozenRunMass (a b : ℕ) : ℤ :=
  ∑ n ∈ frozenRunBlock (a ^ 2) ((b + 1) ^ 2), μ n

/-- Static divisor-incidence correlation of the prefix below `a^2` against the
whole square-run kernel.  This is the exact finite object that the frozen-run
identity exposes. -/
def squareFrozenRunCorrelation (a b : ℕ) : ℤ :=
  ∑ d ∈ Finset.range (a ^ 2),
    (frozenRunDivisorWeight (a ^ 2) ((b + 1) ^ 2) d : ℤ) * μ d

/-- **Square frozen-run identity.**  As long as the entire square run remains
inside the first doubling of its left endpoint, its complete signed mass is the
negative of one static correlation against the Möbius prefix that existed
before the run began. -/
theorem squareFrozenRunMass_eq_neg_staticCorrelation
    (a b : ℕ) (ha : 2 ≤ a)
    (hsub : (b + 1) ^ 2 ≤ 2 * (a ^ 2)) :
    squareFrozenRunMass a b = -squareFrozenRunCorrelation a b := by
  unfold squareFrozenRunMass squareFrozenRunCorrelation
  have hbase : 2 ≤ a ^ 2 := by nlinarith
  exact frozenRun_moebius_increment_eq_frozen_weighted_sum
    (a ^ 2) ((b + 1) ^ 2) hbase hsub

/-- Absolute-value form: on a frozen square run, bounding the static correlation
is literally the same as bounding the run mass; no triangle inequality or
covariance relaxation is used. -/
theorem abs_squareFrozenRunMass_eq_abs_staticCorrelation
    (a b : ℕ) (ha : 2 ≤ a)
    (hsub : (b + 1) ^ 2 ≤ 2 * (a ^ 2)) :
    |((squareFrozenRunMass a b : ℤ) : ℝ)| =
      |((squareFrozenRunCorrelation a b : ℤ) : ℝ)| := by
  rw [squareFrozenRunMass_eq_neg_staticCorrelation a b ha hsub]
  simp

/-- **Static correlation bound.**  This is the cancellation statement suggested
by the frozen-run geometry.  Uniformly over every nonempty complete-square run
whose physical window stays below the first doubling of its left endpoint, the
single frozen-prefix divisor-incidence correlation has RH-scale size
`O_epsilon(a^(1+epsilon))`.

This is a named open analytic premise only.  The exact identities above show
that it is neither an independence assumption nor a new random-sign model: the
right-hand side uses the actual completed Möbius prefix below `a^2` and a fully
deterministic incidence kernel. -/
def SquareFrozenRunStaticCorrelationBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ,
        2 ≤ a →
        a ≤ b →
        (b + 1) ^ 2 ≤ 2 * (a ^ 2) →
        |((squareFrozenRunCorrelation a b : ℤ) : ℝ)| ≤
          C * Real.rpow (a : ℝ) (1 + ε)

end RHLean.Arithmetic