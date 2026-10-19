import «research.VF_QUOTIENT_VARIATION_FIRSTBAD_ATTACK»

/-!
# General-`X` high-quotient isolation and the excluded-norm mass bound

Scheduled Prime Census claim `20261017-census-2` states, for every natural `X`,
with `r = floor(sqrt X)` and `N = floor(X / (r + 1))`,

`V_high(X) = sum_(r < t <= X) |B_X(t) - B_X(t+1)|
           = 2 * sum_(1 <= n <= N) |a6(n)| - |B_X(r+1)|  <=  2 * sqrt X`.

The 2026-10-17 manual-cycle Referee pass audited that paper proof and forwarded
it for formalization.  This module proves it for the constructed #919
coefficients `vf919ExcludedNormCoefficients` and the literal quotient buckets
`vf919QuotientBucket`.  Every bucket is kept, including buckets on which the
period-36 kernel vanishes, and the subtractive boundary bucket `B_X(r+1)` is
retained exactly (it is nonzero, for example, at `X = 380`).

The bound uses the coefficient domination `|a6(n)| <= d_chi(n)`, where
`d_chi(n) = sum_(d | n) chi_-3(d)`, together with `sum_(n <= N) d_chi(n) <= N`.
Both are proved here from the constructed Dirichlet convolution, by
multiplicativity and an exact prime-power evaluation.  They close the
short-norm mass left open by
`vfVarSquareMertens_norm_le_four_lowVariation_add_two_shortMass`.

Section 10 adds the finite face of the manual-cycle result H-L: telescoping
the low return gives

`|sum_(X/2 < m <= X) a6(m)| <= V_low(X) + |B_X(r+1)| <= V_low(X) + sqrt X`,

so every upper bound on `V_low` is also an upper bound on the half-interval
coefficient sums `C6(X) - C6(floor(X/2))`.  The analytic consequence drawn in
the cycle report (a bound `V_low = O(X^theta)` forces `zeta(s) L(s, chi_-3)` to
be zero-free on `Re s > theta`) is a paper argument and is not formalized here.

Scope: these are unconditional statements about the high-quotient sector, the
coefficient mass and the lower side of the low variation.  Nothing here gives
an upper bound for the low-quotient variation, the Mertens function at any
power saving, the canonical VF endpoint or the #915 source.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-! ## 1. Support of the excluded-six coefficients -/

theorem vf919ExcludedNorm_apply (n : ℕ) :
    vf919ExcludedNormCoefficients n =
      vf919PrimeToSixMask n * vf919EisensteinNormCoefficients n := rfl

theorem vf919ExcludedNorm_eq_zero_of_two_dvd {n : ℕ} (h : 2 ∣ n) :
    vf919ExcludedNormCoefficients n = 0 := by
  rw [vf919ExcludedNorm_apply]
  unfold vf919PrimeToSixMask
  rw [ite_eq_left (Or.inl h : 2 ∣ n ∨ 3 ∣ n), zero_mul]

/-- A norm carrying a nonzero excluded-six coefficient is odd. -/
theorem vf919ExcludedNorm_odd_of_ne_zero {n : ℕ}
    (h : vf919ExcludedNormCoefficients n ≠ 0) : n % 2 = 1 := by
  by_contra hodd
  exact h (vf919ExcludedNorm_eq_zero_of_two_dvd (by omega))

/-! ## 2. Quotient gaps in the high range -/

/-- If `n + d = m` and `n <= floor(X/m)`, then `floor(X/n)` exceeds
`floor(X/m)` by at least `d`. -/
theorem vf919Quotient_gap {X n m d : ℕ} (hn : 0 < n) (hnm : n + d = m)
    (hq : n ≤ X / m) : X / m + d ≤ X / n := by
  rw [Nat.le_div_iff_mul_le hn]
  have h1 : X / m * m ≤ X := Nat.div_mul_le_self X m
  have h2 : d * n ≤ d * (X / m) := Nat.mul_le_mul_left d hq
  calc (X / m + d) * n = X / m * n + d * n := by ring
    _ ≤ X / m * n + d * (X / m) := Nat.add_le_add_left h2 _
    _ = X / m * (n + d) := by ring
    _ = X / m * m := by rw [hnm]
    _ ≤ X := h1

/-- `N = floor(X/(r+1))` never exceeds `r = floor(sqrt X)`. -/
theorem vf919HighNorm_le_root (X : ℕ) : X / (Nat.sqrt X + 1) ≤ Nat.sqrt X := by
  have h : X < (Nat.sqrt X + 1) * (Nat.sqrt X + 1) := Nat.lt_succ_sqrt X
  have hlt : X / (Nat.sqrt X + 1) < Nat.sqrt X + 1 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < Nat.sqrt X + 1)).mpr h
  omega

/-- For a positive norm, the quotient is high exactly when the norm is at
most `N`. -/
theorem vf919HighQuotient_iff (X m : ℕ) (hm : 0 < m) :
    Nat.sqrt X + 1 ≤ X / m ↔ m ≤ X / (Nat.sqrt X + 1) := by
  rw [Nat.le_div_iff_mul_le hm, Nat.le_div_iff_mul_le (by omega : 0 < Nat.sqrt X + 1),
    Nat.mul_comm]

/-- Distinct high norms have distinct quotients. -/
theorem vf919HighQuotient_injective {X m m' : ℕ}
    (hm : 0 < m) (hmN : m ≤ X / (Nat.sqrt X + 1))
    (hm' : 0 < m') (hm'N : m' ≤ X / (Nat.sqrt X + 1))
    (heq : X / m = X / m') : m = m' := by
  have hNr := vf919HighNorm_le_root X
  have hqm : Nat.sqrt X + 1 ≤ X / m := (vf919HighQuotient_iff X m hm).mpr hmN
  have hqm' : Nat.sqrt X + 1 ≤ X / m' := (vf919HighQuotient_iff X m' hm').mpr hm'N
  rcases Nat.lt_trichotomy m m' with hlt | heq' | hgt
  · have hgap := vf919Quotient_gap (X := X) (n := m) (m := m') (d := m' - m) hm
      (by omega) (by omega)
    omega
  · exact heq'
  · have hgap := vf919Quotient_gap (X := X) (n := m') (m := m) (d := m - m') hm'
      (by omega) (by omega)
    omega

/-! ## 3. High buckets are singletons and are isolated by zero buckets -/

/-- A high bucket is either empty or the single coefficient of its unique
norm; its norm is the corresponding sum of coefficient norms. -/
theorem vf919HighBucket_norm (X t : ℕ) (ht : Nat.sqrt X + 1 ≤ t) :
    ‖vf919QuotientBucket X t‖ =
      ∑ m ∈ Finset.Icc 1 (X / (Nat.sqrt X + 1)),
        if X / m = t then ‖vf919ExcludedNormCoefficients m‖ else 0 := by
  have hNX : X / (Nat.sqrt X + 1) ≤ X := Nat.div_le_self X _
  have hhigh : ∀ m, 1 ≤ m → X / m = t → m ≤ X / (Nat.sqrt X + 1) := by
    intro m hm hq
    exact (vf919HighQuotient_iff X m (by omega)).mp (by omega)
  by_cases hex : ∃ m0 ∈ Finset.Icc 1 (X / (Nat.sqrt X + 1)), X / m0 = t
  · obtain ⟨m0, hm0, hq0⟩ := hex
    have hm0' := Finset.mem_Icc.mp hm0
    have huniq : ∀ m, 1 ≤ m → X / m = t → m = m0 := by
      intro m hm hq
      exact vf919HighQuotient_injective (by omega) (hhigh m hm hq) (by omega) hm0'.2
        (by rw [hq, hq0])
    have hB : vf919QuotientBucket X t = vf919ExcludedNormCoefficients m0 := by
      unfold vf919QuotientBucket
      rw [Finset.sum_eq_single m0]
      · rw [ite_eq_left hq0]
      · intro m hm hne
        have hm' := Finset.mem_Icc.mp hm
        have hq : X / m ≠ t := fun hq => hne (huniq m hm'.1 hq)
        rw [ite_eq_right hq]
      · intro hnot
        exact (hnot (Finset.mem_Icc.mpr ⟨hm0'.1, hm0'.2.trans hNX⟩)).elim
    rw [hB, Finset.sum_eq_single m0]
    · rw [ite_eq_left hq0]
    · intro m hm hne
      have hm' := Finset.mem_Icc.mp hm
      have hq : X / m ≠ t := fun hq => hne (huniq m hm'.1 hq)
      rw [ite_eq_right hq]
    · intro hnot
      exact (hnot hm0).elim
  · push Not at hex
    have hB : vf919QuotientBucket X t = 0 := by
      unfold vf919QuotientBucket
      apply Finset.sum_eq_zero
      intro m hm
      have hm' := Finset.mem_Icc.mp hm
      have hq : X / m ≠ t := by
        intro hq
        exact hex m (Finset.mem_Icc.mpr ⟨hm'.1, hhigh m hm'.1 hq⟩) hq
      rw [ite_eq_right hq]
    rw [hB, norm_zero]
    symm
    apply Finset.sum_eq_zero
    intro m hm
    rw [ite_eq_right (hex m hm)]

/-- Census-2 isolation: two consecutive high buckets are never both nonzero.
Supported norms are odd, so their quotients differ by at least two. -/
theorem vf919HighBucket_isolated (X t : ℕ) (ht : Nat.sqrt X + 1 ≤ t) :
    vf919QuotientBucket X t = 0 ∨ vf919QuotientBucket X (t + 1) = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1⟩ := hcon
  unfold vf919QuotientBucket at h0 h1
  obtain ⟨m, hm, hmne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
  obtain ⟨m', hm', hm'ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have hq : X / m = t := by
    by_contra hne
    exact hmne (ite_eq_right hne)
  have hq' : X / m' = t + 1 := by
    by_contra hne
    exact hm'ne (ite_eq_right hne)
  have ha : vf919ExcludedNormCoefficients m ≠ 0 := by
    intro hz
    exact hmne (by rw [ite_eq_left hq, hz])
  have ha' : vf919ExcludedNormCoefficients m' ≠ 0 := by
    intro hz
    exact hm'ne (by rw [ite_eq_left hq', hz])
  have hmpos : 0 < m := by
    have := (Finset.mem_Icc.mp hm).1
    omega
  have hm'pos : 0 < m' := by
    have := (Finset.mem_Icc.mp hm').1
    omega
  have hodd := vf919ExcludedNorm_odd_of_ne_zero ha
  have hodd' := vf919ExcludedNorm_odd_of_ne_zero ha'
  have hNr := vf919HighNorm_le_root X
  have hm'N : m' ≤ X / (Nat.sqrt X + 1) :=
    (vf919HighQuotient_iff X m' hm'pos).mp (by omega)
  have hlt : m' < m := by
    by_contra hle
    push Not at hle
    have hdiv := Nat.div_le_div_left (a := X) hle hmpos
    omega
  have hgap := vf919Quotient_gap (X := X) (n := m') (m := m) (d := m - m')
    hm'pos (by omega) (by omega)
  omega

/-- On the high range every adjacent difference has norm equal to the sum of
the two bucket norms. -/
theorem vf919HighVariation_term (X t : ℕ) (ht : Nat.sqrt X + 1 ≤ t) :
    ‖vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)‖ =
      ‖vf919QuotientBucket X t‖ + ‖vf919QuotientBucket X (t + 1)‖ := by
  rcases vf919HighBucket_isolated X t ht with h | h
  · rw [h, zero_sub, norm_neg, norm_zero, zero_add]
  · rw [h, sub_zero, norm_zero, add_zero]

/-- Index shift for the bucket-norm sum over `(a, b]`. -/
theorem vf919BucketNorm_sum_shift (X : ℕ) {a b : ℕ} (hab : a ≤ b) :
    (∑ t ∈ Finset.Ioc a b, ‖vf919QuotientBucket X (t + 1)‖) =
      (∑ t ∈ Finset.Ioc a b, ‖vf919QuotientBucket X t‖) -
        ‖vf919QuotientBucket X (a + 1)‖ + ‖vf919QuotientBucket X (b + 1)‖ := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, Finset.sum_Ioc_succ_top hab, ih]
    ring

/-! ## 4. Census `20261017-census-2`: the exact general-`X` identity -/

/-- **Exact general-`X` high-quotient variation.**  With `r = floor(sqrt X)`
and `N = floor(X/(r+1))`,
`sum_(r<t<=X) |B_X(t)-B_X(t+1)| = 2 sum_(n<=N) |a6(n)| - |B_X(r+1)|`.
The boundary bucket `B_X(r+1)` is subtracted because its lower transition
belongs to the low range. -/
theorem vf919HighQuotientVariation_eq (X : ℕ) :
    (∑ t ∈ Finset.Ioc (Nat.sqrt X) X,
        ‖vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)‖) =
      2 * (∑ m ∈ Finset.Icc 1 (X / (Nat.sqrt X + 1)),
          ‖vf919ExcludedNormCoefficients m‖) -
        ‖vf919QuotientBucket X (Nat.sqrt X + 1)‖ := by
  have hrX : Nat.sqrt X ≤ X := Nat.sqrt_le_self X
  have hterm : ∀ t ∈ Finset.Ioc (Nat.sqrt X) X,
      ‖vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)‖ =
        ‖vf919QuotientBucket X t‖ + ‖vf919QuotientBucket X (t + 1)‖ := by
    intro t ht
    have := (Finset.mem_Ioc.mp ht).1
    exact vf919HighVariation_term X t (by omega)
  have hpt : ∀ t ∈ Finset.Ioc (Nat.sqrt X) X, ‖vf919QuotientBucket X t‖ =
      ∑ m ∈ Finset.Icc 1 (X / (Nat.sqrt X + 1)),
        if X / m = t then ‖vf919ExcludedNormCoefficients m‖ else 0 := by
    intro t ht
    have := (Finset.mem_Ioc.mp ht).1
    exact vf919HighBucket_norm X t (by omega)
  have hmass : (∑ t ∈ Finset.Ioc (Nat.sqrt X) X, ‖vf919QuotientBucket X t‖) =
      ∑ m ∈ Finset.Icc 1 (X / (Nat.sqrt X + 1)), ‖vf919ExcludedNormCoefficients m‖ := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    have hq : X / m ∈ Finset.Ioc (Nat.sqrt X) X := by
      apply Finset.mem_Ioc.mpr
      constructor
      · have := (vf919HighQuotient_iff X m (by omega)).mpr hm'.2
        omega
      · exact Nat.div_le_self X m
    rw [Finset.sum_ite_eq, ite_eq_left hq]
  have htop : vf919QuotientBucket X (X + 1) = 0 :=
    vf919QuotientBucket_above X (X + 1) (by omega)
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    vf919BucketNorm_sum_shift X hrX, htop, norm_zero, hmass]
  ring

/-! ## 5. The `chi_-3` divisor majorant -/

/-- Real-valued `chi_-3`. -/
def vf919ChiReal (n : ℕ) : ℝ :=
  if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1

theorem vf919ChiReal_mul (m n : ℕ) :
    vf919ChiReal (m * n) = vf919ChiReal m * vf919ChiReal n := by
  have hm := Nat.mod_lt m (by decide : 0 < 3)
  have hn := Nat.mod_lt n (by decide : 0 < 3)
  interval_cases h₁ : m % 3 <;> interval_cases h₂ : n % 3 <;>
    norm_num [vf919ChiReal, Nat.mul_mod, h₁, h₂]

theorem vf919ChiReal_pow (n i : ℕ) : vf919ChiReal (n ^ i) = vf919ChiReal n ^ i := by
  induction i with
  | zero => norm_num [vf919ChiReal]
  | succ i ih => rw [pow_succ n i, vf919ChiReal_mul, ih, pow_succ (vf919ChiReal n) i]

theorem vf919ChiMinusThree_eq_ofReal (n : ℕ) :
    vf919ChiMinusThree n = ((vf919ChiReal n : ℝ) : ℂ) := by
  unfold vf919ChiMinusThree vf919ChiReal
  split_ifs <;> simp

/-- `chi_-3` as a real arithmetic function. -/
def vf919ChiRealArith : ArithmeticFunction ℝ :=
  ⟨vf919ChiReal, by simp [vf919ChiReal]⟩

theorem vf919ChiRealArith_apply (n : ℕ) : vf919ChiRealArith n = vf919ChiReal n := rfl

theorem vf919ChiRealArith_isMultiplicative : vf919ChiRealArith.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · show vf919ChiReal 1 = 1
    norm_num [vf919ChiReal]
  · intro m n _
    show vf919ChiReal (m * n) = vf919ChiReal m * vf919ChiReal n
    exact vf919ChiReal_mul m n

/-- The divisor majorant `d_chi = 1 * chi_-3`. -/
def vf919ChiDivisor : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vf919ChiRealArith

theorem vf919ChiDivisor_apply (n : ℕ) :
    vf919ChiDivisor n = ∑ d ∈ n.divisors, vf919ChiReal d := by
  rw [vf919ChiDivisor, ArithmeticFunction.coe_zeta_mul_apply]
  exact Finset.sum_congr rfl (fun d _ => vf919ChiRealArith_apply d)

theorem vf919ChiDivisor_isMultiplicative : vf919ChiDivisor.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_zeta.natCast.mul vf919ChiRealArith_isMultiplicative

/-- A geometric sum of a sign or zero is nonnegative. -/
theorem vf919_geom_sum_nonneg (c : ℝ) (hc : c = 1 ∨ c = 0 ∨ c = -1) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (k + 1), c ^ i := by
  rcases hc with rfl | rfl | rfl
  · exact Finset.sum_nonneg (fun i _ => by rw [one_pow]; exact zero_le_one)
  · exact Finset.sum_nonneg (fun i _ => pow_nonneg (le_refl 0) i)
  · rw [geom_sum_eq (by norm_num : (-1 : ℝ) ≠ 1) (k + 1)]
    rcases neg_one_pow_eq_or ℝ (k + 1) with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num

/-! ## 6. Multiplicativity and prime-power values of the coefficients -/

theorem vf919ArithmeticTwist_isMultiplicative (g : ℕ → ℂ) (hg1 : g 1 = 1)
    (hg : ∀ m n, g (m * n) = g m * g n) {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) : (vf919ArithmeticTwist g f).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · show g 1 * f 1 = 1
    rw [hg1, hf.map_one, one_mul]
  · intro m n hmn
    show g (m * n) * f (m * n) = g m * f m * (g n * f n)
    rw [hg m n, hf.2 hmn]
    ring

theorem vf919RationalMobius_isMultiplicative : vf919RationalMobius.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast

theorem vf919ChiMinusThree_one : vf919ChiMinusThree 1 = 1 := by
  norm_num [vf919ChiMinusThree]

theorem vf919ExcludedNorm_isMultiplicative :
    vf919ExcludedNormCoefficients.IsMultiplicative := by
  have hmask1 : vf919PrimeToSixMask 1 = 1 := by norm_num [vf919PrimeToSixMask]
  have hinv : vf919QuadraticInverse.IsMultiplicative :=
    vf919ArithmeticTwist_isMultiplicative vf919ChiMinusThree vf919ChiMinusThree_one
      vf919ChiMinusThree_mul vf919RationalMobius_isMultiplicative
  have hnorm : vf919EisensteinNormCoefficients.IsMultiplicative :=
    vf919RationalMobius_isMultiplicative.mul hinv
  exact vf919ArithmeticTwist_isMultiplicative vf919PrimeToSixMask hmask1
    vf919PrimeToSixMask_mul hnorm

theorem vf919QuadraticInverse_apply (n : ℕ) :
    vf919QuadraticInverse n = vf919ChiMinusThree n * vf919RationalMobius n := rfl

theorem vf919RationalMobius_one : vf919RationalMobius 1 = 1 :=
  vf919RationalMobius_isMultiplicative.map_one

theorem vf919RationalMobius_prime {p : ℕ} (hp : p.Prime) : vf919RationalMobius p = -1 := by
  show ((ArithmeticFunction.moebius p : ℤ) : ℂ) = -1
  rw [ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg, Int.cast_one]

theorem vf919RationalMobius_prime_pow_eq_zero {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) :
    vf919RationalMobius (p ^ j) = 0 := by
  have h := ArithmeticFunction.moebius_apply_prime_pow hp (show j ≠ 0 by omega)
  rw [ite_eq_right (show j ≠ 1 by omega)] at h
  show ((ArithmeticFunction.moebius (p ^ j) : ℤ) : ℂ) = 0
  rw [h, Int.cast_zero]

/-- Dirichlet convolution at a prime power. -/
theorem vf919_dirichlet_apply_prime_pow (f g : ArithmeticFunction ℂ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hik : i ≤ k := by
    have := Finset.mem_range.mp hi
    omega
  rw [Nat.pow_div hik hp.pos]

theorem vf919EisensteinNorm_prime {p : ℕ} (hp : p.Prime) :
    vf919EisensteinNormCoefficients p = -vf919ChiMinusThree p - 1 := by
  have h := vf919_dirichlet_apply_prime_pow vf919RationalMobius vf919QuadraticInverse hp 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, Nat.sub_zero, Nat.sub_self] at h
  have hE : vf919EisensteinNormCoefficients p =
      (vf919RationalMobius * vf919QuadraticInverse) p := rfl
  rw [hE, h, vf919QuadraticInverse_apply, vf919QuadraticInverse_apply, vf919RationalMobius_one,
    vf919RationalMobius_prime hp, vf919ChiMinusThree_one]
  ring

theorem vf919EisensteinNorm_prime_sq {p : ℕ} (hp : p.Prime) :
    vf919EisensteinNormCoefficients (p ^ 2) = vf919ChiMinusThree p := by
  have h := vf919_dirichlet_apply_prime_pow vf919RationalMobius vf919QuadraticInverse hp 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, Nat.sub_zero, Nat.sub_self, show (2 : ℕ) - 1 = 1 from rfl] at h
  have hE : vf919EisensteinNormCoefficients (p ^ 2) =
      (vf919RationalMobius * vf919QuadraticInverse) (p ^ 2) := rfl
  rw [hE, h, vf919QuadraticInverse_apply, vf919QuadraticInverse_apply,
    vf919QuadraticInverse_apply, vf919RationalMobius_one, vf919RationalMobius_prime hp,
    vf919RationalMobius_prime_pow_eq_zero hp (le_refl 2)]
  ring

theorem vf919EisensteinNorm_prime_pow_eq_zero {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k) :
    vf919EisensteinNormCoefficients (p ^ k) = 0 := by
  have hE : vf919EisensteinNormCoefficients (p ^ k) =
      (vf919RationalMobius * vf919QuadraticInverse) (p ^ k) := rfl
  rw [hE, vf919_dirichlet_apply_prime_pow _ _ hp k]
  apply Finset.sum_eq_zero
  intro i _
  by_cases h2 : 2 ≤ i
  · rw [vf919RationalMobius_prime_pow_eq_zero hp h2, zero_mul]
  · rw [vf919QuadraticInverse_apply,
      vf919RationalMobius_prime_pow_eq_zero hp (show 2 ≤ k - i by omega), mul_zero, mul_zero]

/-! ## 7. Pointwise domination `|a6(n)| <= d_chi(n)` -/

theorem vf919ExcludedNorm_prime_pow_le {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ‖vf919ExcludedNormCoefficients (p ^ k)‖ ≤ vf919ChiDivisor (p ^ k) := by
  have hd : vf919ChiDivisor (p ^ k) = ∑ i ∈ Finset.range (k + 1), vf919ChiReal p ^ i := by
    rw [vf919ChiDivisor_apply, Nat.sum_divisors_prime_pow hp]
    exact Finset.sum_congr rfl (fun i _ => vf919ChiReal_pow p i)
  have hc3 : vf919ChiReal p = 1 ∨ vf919ChiReal p = 0 ∨ vf919ChiReal p = -1 := by
    unfold vf919ChiReal
    split_ifs <;> simp
  have hdnn : 0 ≤ vf919ChiDivisor (p ^ k) := by
    rw [hd]
    exact vf919_geom_sum_nonneg _ hc3 k
  by_cases h23 : p = 2 ∨ p = 3
  · have hdvd : 2 ∣ p ^ k ∨ 3 ∣ p ^ k := by
      rcases h23 with rfl | rfl
      · exact Or.inl (dvd_pow_self 2 hk.ne')
      · exact Or.inr (dvd_pow_self 3 hk.ne')
    have hz : vf919ExcludedNormCoefficients (p ^ k) = 0 := by
      rw [vf919ExcludedNorm_apply]
      unfold vf919PrimeToSixMask
      rw [ite_eq_left hdvd, zero_mul]
    rw [hz, norm_zero]
    exact hdnn
  · push Not at h23
    obtain ⟨hp2, hp3⟩ := h23
    have hn2 : ¬ 2 ∣ p ^ k := fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.prime_two.dvd_of_dvd_pow h)).symm
    have hn3 : ¬ 3 ∣ p ^ k := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    have hmask : vf919PrimeToSixMask (p ^ k) = 1 := by
      unfold vf919PrimeToSixMask
      rw [ite_eq_right (not_or.mpr ⟨hn2, hn3⟩)]
    have hmod : p % 3 ≠ 0 := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.dvd_of_mod_eq_zero h)).symm
    have hc : vf919ChiReal p = 1 ∨ vf919ChiReal p = -1 := by
      unfold vf919ChiReal
      rw [ite_eq_right hmod]
      split_ifs <;> simp
    rw [vf919ExcludedNorm_apply, hmask, one_mul]
    rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | hk3
    · rw [hd, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, pow_one,
        vf919EisensteinNorm_prime hp, vf919ChiMinusThree_eq_ofReal]
      have hcast : -((vf919ChiReal p : ℝ) : ℂ) - 1 = ((-vf919ChiReal p - 1 : ℝ) : ℂ) := by
        rw [Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_one]
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
      rcases hc with h | h <;> rw [h] <;> norm_num
    · rw [hd, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_zero,
        pow_one, vf919EisensteinNorm_prime_sq hp, vf919ChiMinusThree_eq_ofReal,
        Complex.norm_real, Real.norm_eq_abs, abs_le]
      rcases hc with h | h <;> rw [h] <;> norm_num
    · rw [vf919EisensteinNorm_prime_pow_eq_zero hp hk3, norm_zero]
      exact hdnn

/-- **Coefficient domination.**  `|a6(n)| <= d_chi(n) = sum_(d|n) chi_-3(d)`
for every `n`. -/
theorem vf919ExcludedNorm_norm_le_chiDivisor (n : ℕ) :
    ‖vf919ExcludedNormCoefficients n‖ ≤ vf919ChiDivisor n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk => exact vf919ExcludedNorm_prime_pow_le hp hk
  | zero => simp
  | one =>
    have h1 : vf919ExcludedNormCoefficients 1 = 1 :=
      vf919ExcludedNorm_isMultiplicative.map_one
    have h2 : vf919ChiDivisor 1 = 1 := vf919ChiDivisor_isMultiplicative.map_one
    norm_num [h1, h2]
  | coprime a b _ha _hb hab iha ihb =>
    rw [vf919ExcludedNorm_isMultiplicative.map_mul_of_coprime hab,
      vf919ChiDivisor_isMultiplicative.map_mul_of_coprime hab, norm_mul]
    exact mul_le_mul iha ihb (norm_nonneg _) ((norm_nonneg _).trans iha)

/-! ## 8. Summatory bound `sum_(n<=N) d_chi(n) <= N` and the mass bound -/

theorem vf919ChiReal_partial_sum (u : ℕ) :
    (∑ d ∈ Finset.Ioc 0 u, vf919ChiReal d) = if u % 3 = 1 then 1 else 0 := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le u), ih]
    unfold vf919ChiReal
    rcases (show u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 by omega) with h0 | h0 | h0
    · have h1 : (u + 1) % 3 = 1 := by omega
      norm_num [h0, h1]
    · have h1 : (u + 1) % 3 = 2 := by omega
      norm_num [h0, h1]
    · have h1 : (u + 1) % 3 = 0 := by omega
      norm_num [h0, h1]

theorem vf919ChiReal_partial_sum_le_one (u : ℕ) :
    (∑ d ∈ Finset.Ioc 0 u, vf919ChiReal d) ≤ 1 := by
  rw [vf919ChiReal_partial_sum]
  split_ifs <;> norm_num

/-- `sum_(n<=N) d_chi(n) = sum_(e<=N) C_chi(floor(N/e)) <= N`. -/
theorem vf919ChiDivisor_sum_le (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, vf919ChiDivisor n) ≤ N := by
  have step1 : (∑ n ∈ Finset.Ioc 0 N, vf919ChiDivisor n) =
      ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, vf919ChiReal d :=
    Finset.sum_congr rfl (fun n _ => vf919ChiDivisor_apply n)
  have step2 : (∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, vf919ChiReal d) =
      ∑ d ∈ Finset.Ioc 0 N,
        ∑ _n ∈ (Finset.Ioc 0 N).filter (fun n => d ∣ n), vf919ChiReal d := by
    apply Finset.sum_comm'
    intro n d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn0, hnN⟩, hdn, -⟩
      exact ⟨⟨⟨hn0, hnN⟩, hdn⟩, Nat.pos_of_dvd_of_pos hdn hn0,
        le_trans (Nat.le_of_dvd hn0 hdn) hnN⟩
    · rintro ⟨⟨⟨hn0, hnN⟩, hdn⟩, -, -⟩
      exact ⟨⟨hn0, hnN⟩, hdn, by omega⟩
  have step3 : ∀ d ∈ Finset.Ioc 0 N,
      (∑ _n ∈ (Finset.Ioc 0 N).filter (fun n => d ∣ n), vf919ChiReal d) =
        ∑ _e ∈ Finset.Ioc 0 (N / d), vf919ChiReal d := by
    intro d _
    rw [Finset.sum_const, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, Nat.card_Ioc,
      Nat.sub_zero]
  have step4 : (∑ d ∈ Finset.Ioc 0 N, ∑ _e ∈ Finset.Ioc 0 (N / d), vf919ChiReal d) =
      ∑ e ∈ Finset.Ioc 0 N, ∑ d ∈ Finset.Ioc 0 (N / e), vf919ChiReal d := by
    apply Finset.sum_comm'
    intro d e
    simp only [Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hd0, -⟩, he0, heN⟩
      have h1 : e * d ≤ N := (Nat.le_div_iff_mul_le hd0).mp heN
      refine ⟨⟨hd0, (Nat.le_div_iff_mul_le he0).mpr ?_⟩, he0, ?_⟩
      · rw [Nat.mul_comm]
        exact h1
      · exact le_trans (Nat.le_mul_of_pos_right e hd0) h1
    · rintro ⟨⟨hd0, hdN⟩, he0, -⟩
      have h1 : d * e ≤ N := (Nat.le_div_iff_mul_le he0).mp hdN
      refine ⟨⟨hd0, le_trans (Nat.le_mul_of_pos_right d he0) h1⟩, he0, ?_⟩
      apply (Nat.le_div_iff_mul_le hd0).mpr
      rw [Nat.mul_comm]
      exact h1
  calc (∑ n ∈ Finset.Ioc 0 N, vf919ChiDivisor n)
      = ∑ e ∈ Finset.Ioc 0 N, ∑ d ∈ Finset.Ioc 0 (N / e), vf919ChiReal d := by
        rw [step1, step2, Finset.sum_congr rfl step3, step4]
    _ ≤ ∑ _e ∈ Finset.Ioc 0 N, (1 : ℝ) :=
        Finset.sum_le_sum (fun e _ => vf919ChiReal_partial_sum_le_one (N / e))
    _ = N := by simp

/-- **Excluded-norm mass bound.**  `sum_(1<=n<=N) |a6(n)| <= N`. -/
theorem vf919ExcludedNorm_mass_le (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ‖vf919ExcludedNormCoefficients m‖) ≤ N := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc]
  exact (Finset.sum_le_sum (fun m _ => vf919ExcludedNorm_norm_le_chiDivisor m)).trans
    (vf919ChiDivisor_sum_le N)

/-! ## 9. Consumers -/

/-- Census-2 bound with the boundary bucket retained. -/
theorem vf919HighQuotientVariation_le (X : ℕ) :
    (∑ t ∈ Finset.Ioc (Nat.sqrt X) X,
        ‖vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)‖) ≤
      2 * ((X / (Nat.sqrt X + 1) : ℕ) : ℝ) - ‖vf919QuotientBucket X (Nat.sqrt X + 1)‖ := by
  rw [vf919HighQuotientVariation_eq]
  have := vf919ExcludedNorm_mass_le (X / (Nat.sqrt X + 1))
  linarith

/-- **The complete high-quotient variation is at most `2 sqrt X`, for every
`X`.** -/
theorem vf919HighQuotientVariation_le_two_sqrt (X : ℕ) :
    (∑ t ∈ Finset.Ioc (Nat.sqrt X) X,
        ‖vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)‖) ≤
      2 * Real.sqrt X := by
  have h1 := vf919HighQuotientVariation_le X
  have hN : X / (Nat.sqrt X + 1) ≤ Nat.sqrt X := vf919HighNorm_le_root X
  have hNr : ((X / (Nat.sqrt X + 1) : ℕ) : ℝ) ≤ (Nat.sqrt X : ℝ) := Nat.cast_le.mpr hN
  have h2 : ((X / (Nat.sqrt X + 1) : ℕ) : ℝ) ≤ Real.sqrt X :=
    hNr.trans Real.nat_sqrt_le_real_sqrt
  have h3 := norm_nonneg (vf919QuotientBucket X (Nat.sqrt X + 1))
  linarith

/-- Square-endpoint closure of the short-norm mass:
`|M(R^2-1)| <= 4 * V_low(R^2-1) + 2(R-1)`.  The low-quotient variation remains
the only unbounded quantity. -/
theorem vfVarSquareMertens_norm_le_four_lowVariation_add_two_root
    (R : ℕ) (hR : 4 ≤ R) :
    ‖(∑ n ∈ Finset.Icc 1 (R ^ 2 - 1), (ArithmeticFunction.moebius n : ℂ))‖ ≤
      4 * (∑ t ∈ Finset.Icc 1 (R - 1),
        ‖vf919QuotientBucket (R ^ 2 - 1) t - vf919QuotientBucket (R ^ 2 - 1) (t + 1)‖) +
      2 * ((R - 1 : ℕ) : ℝ) := by
  have h := vfVarSquareMertens_norm_le_four_lowVariation_add_two_shortMass R hR
  have hm := vf919ExcludedNorm_mass_le (R - 1)
  linarith

/-! ## 10. The lower side of the low variation (finite face of H-L) -/

/-- The quotient `floor(X/m)` equals `1` exactly on the upper half
`X/2 < m <= X`. -/
theorem vf919QuotientOne_iff (X m : ℕ) (hm : 0 < m) :
    X / m = 1 ↔ m ≤ X ∧ X / 2 < m := by
  constructor
  · intro h
    have h1 : 1 ≤ X / m := by omega
    have h2 : X / m < 2 := by omega
    rw [Nat.le_div_iff_mul_le hm] at h1
    rw [Nat.div_lt_iff_lt_mul hm] at h2
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    have h1' : 1 ≤ X / m := (Nat.le_div_iff_mul_le hm).mpr (by omega)
    have h2' : X / m < 2 := (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
    omega

/-- The first quotient bucket is the upper-half coefficient sum
`B_X(1) = C6(X) - C6(floor(X/2))`. -/
theorem vf919QuotientBucket_one (X : ℕ) :
    vf919QuotientBucket X 1 =
      ∑ m ∈ Finset.Ioc (X / 2) X, vf919ExcludedNormCoefficients m := by
  unfold vf919QuotientBucket
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hm1, hmX⟩, hq⟩
    exact ⟨((vf919QuotientOne_iff X m (by omega)).mp hq).2, hmX⟩
  · rintro ⟨hlo, hmX⟩
    exact ⟨⟨by omega, hmX⟩, (vf919QuotientOne_iff X m (by omega)).mpr ⟨hmX, hlo⟩⟩

/-- Telescoping of the unweighted signed low return:
`sum_(1<=t<=r) (B_X(t) - B_X(t+1)) = B_X(1) - B_X(r+1)`. -/
theorem vf919LowReturn_telescope (X r : ℕ) :
    (∑ t ∈ Finset.Icc 1 r,
        (vf919QuotientBucket X t - vf919QuotientBucket X (t + 1))) =
      vf919QuotientBucket X 1 - vf919QuotientBucket X (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ r + 1), ih]
    ring

/-- **Finite face of H-L.**  The upper-half coefficient sum is at most the
low variation plus the single boundary bucket:
`|C6(X) - C6(floor(X/2))| <= V_low(X) + |B_X(r+1)|`, `r = floor(sqrt X)`.
Every bucket is kept, including those on which the period-36 kernel
vanishes. -/
theorem vf919HalfIncrement_norm_le_lowVariation_add_boundary (X : ℕ) :
    ‖∑ m ∈ Finset.Ioc (X / 2) X, vf919ExcludedNormCoefficients m‖ ≤
      (∑ t ∈ Finset.Icc 1 (Nat.sqrt X),
          ‖vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)‖) +
        ‖vf919QuotientBucket X (Nat.sqrt X + 1)‖ := by
  have htel := vf919LowReturn_telescope X (Nat.sqrt X)
  have h1 : vf919QuotientBucket X 1 =
      (∑ t ∈ Finset.Icc 1 (Nat.sqrt X),
          (vf919QuotientBucket X t - vf919QuotientBucket X (t + 1))) +
        vf919QuotientBucket X (Nat.sqrt X + 1) := by
    rw [htel]
    ring
  calc ‖∑ m ∈ Finset.Ioc (X / 2) X, vf919ExcludedNormCoefficients m‖
      = ‖vf919QuotientBucket X 1‖ := by rw [vf919QuotientBucket_one]
    _ = ‖(∑ t ∈ Finset.Icc 1 (Nat.sqrt X),
            (vf919QuotientBucket X t - vf919QuotientBucket X (t + 1))) +
          vf919QuotientBucket X (Nat.sqrt X + 1)‖ := by rw [← h1]
    _ ≤ ‖∑ t ∈ Finset.Icc 1 (Nat.sqrt X),
            (vf919QuotientBucket X t - vf919QuotientBucket X (t + 1))‖ +
          ‖vf919QuotientBucket X (Nat.sqrt X + 1)‖ := norm_add_le _ _
    _ ≤ (∑ t ∈ Finset.Icc 1 (Nat.sqrt X),
            ‖vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)‖) +
          ‖vf919QuotientBucket X (Nat.sqrt X + 1)‖ :=
      add_le_add_left (norm_sum_le _ _) _

/-- The boundary bucket `B_X(r+1)` holds at most one norm, and its size is at
most `sqrt X`. -/
theorem vf919BoundaryBucket_norm_le_sqrt (X : ℕ) :
    ‖vf919QuotientBucket X (Nat.sqrt X + 1)‖ ≤ Real.sqrt X := by
  rw [vf919HighBucket_norm X (Nat.sqrt X + 1) le_rfl]
  have hle : (∑ m ∈ Finset.Icc 1 (X / (Nat.sqrt X + 1)),
        if X / m = Nat.sqrt X + 1 then ‖vf919ExcludedNormCoefficients m‖ else 0) ≤
      ∑ m ∈ Finset.Icc 1 (X / (Nat.sqrt X + 1)), ‖vf919ExcludedNormCoefficients m‖ := by
    apply Finset.sum_le_sum
    intro m _
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _
  have hmass := vf919ExcludedNorm_mass_le (X / (Nat.sqrt X + 1))
  have hN : X / (Nat.sqrt X + 1) ≤ Nat.sqrt X := vf919HighNorm_le_root X
  have hNr : ((X / (Nat.sqrt X + 1) : ℕ) : ℝ) ≤ (Nat.sqrt X : ℝ) := Nat.cast_le.mpr hN
  have h2 : ((X / (Nat.sqrt X + 1) : ℕ) : ℝ) ≤ Real.sqrt X :=
    hNr.trans Real.nat_sqrt_le_real_sqrt
  linarith

/-- **Two-sided role of the low variation.**  Together with
`vfVarSquareMertens_norm_le_four_lowVariation_add_two_root`, any upper bound
on `V_low` bounds the Mertens function from above and the upper-half
coefficient sums `C6(X) - C6(floor(X/2))` as well:
`|C6(X) - C6(floor(X/2))| <= V_low(X) + sqrt X`. -/
theorem vf919HalfIncrement_norm_le_lowVariation_add_sqrt (X : ℕ) :
    ‖∑ m ∈ Finset.Ioc (X / 2) X, vf919ExcludedNormCoefficients m‖ ≤
      (∑ t ∈ Finset.Icc 1 (Nat.sqrt X),
          ‖vf919QuotientBucket X t - vf919QuotientBucket X (t + 1)‖) +
        Real.sqrt X := by
  have h := vf919HalfIncrement_norm_le_lowVariation_add_boundary X
  have hb := vf919BoundaryBucket_norm_le_sqrt X
  linarith

end RHLean.Analysis
