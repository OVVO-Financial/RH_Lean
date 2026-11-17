import «research.NATIVE_OWNER_PREFIX_MERTENS_20261021»
import RHLean.Proof.SquareRootAmplificationLogGrowth
import RHLean.Analysis.PrimeSieveCollapseIdentity

/-!
# Uniform capacity of the complete high-prime owner diagonal

Below `R^2`, two distinct primes greater than `R` cannot own the same integer.
The resulting finite injection pays the whole owner diagonal without a
harmonic or positive-power loss.  All definitions retain the original
strict prime cutoff, actual Mertens coefficients, and full prefix `x < R^2`.

The complete signed compensation is retained.  Its quantitative upper bound
is an explicit hypothesis of the final preservation consumer, not a conclusion.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Analysis.OwnerPrefix

open RHLean.Proof RHLean.Proof.NativeOwnerSwapRenewal

/-- Original strict high-prime owner set at an arbitrary prefix endpoint. -/
def primeOwnersUpTo (R x : ℕ) : Finset ℕ :=
  (Finset.Ioc R x).filter Nat.Prime

/-- Every cofactor of an original owner is in the strict historical prefix. -/
theorem owner_cofactor_bounds_upTo {R x p : ℕ}
    (_hR : 2 ≤ R) (hx : x < R ^ 2) (hp : p ∈ primeOwnersUpTo R x) :
    1 ≤ x / p ∧ x / p < R := by
  obtain ⟨hpI, hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hRp, hpx⟩ := Finset.mem_Ioc.mp hpI
  constructor
  · exact Nat.div_pos hpx hprime.pos
  · apply (Nat.div_lt_iff_lt_mul hprime.pos).mpr
    have hmul : R ^ 2 ≤ R * p := by
      simpa only [pow_two] using Nat.mul_le_mul_left R hRp.le
    exact hx.trans_le hmul

private def ownerPairs (R x : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (primeOwnersUpTo R x).sigma fun p => Finset.Icc 1 (x / p)

private theorem ownerPair_mul_injective {R x : ℕ}
    (hR : 2 ≤ R) (hx : x < R ^ 2) :
    Set.InjOn (fun a : Σ _ : ℕ, ℕ => a.1 * a.2) (ownerPairs R x) := by
  intro a ha b hb hab
  rcases a with ⟨p, m⟩
  rcases b with ⟨q, n⟩
  obtain ⟨hp, hm⟩ := Finset.mem_sigma.mp ha
  obtain ⟨hq, hn⟩ := Finset.mem_sigma.mp hb
  obtain ⟨hm1, hmle⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hn1, hnle⟩ := Finset.mem_Icc.mp hn
  change 1 ≤ n at hn1
  obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqI, hqP⟩ := Finset.mem_filter.mp hq
  have hRp : R < p := (Finset.mem_Ioc.mp hpI).1
  have hnR : n < R := hnle.trans_lt (owner_cofactor_bounds_upTo hR hx hq).2
  have hprod : p * m = q * n := hab
  have hdiv : p ∣ q * n := ⟨m, hprod.symm⟩
  have hpq : p = q := by
    rcases hpP.dvd_mul.mp hdiv with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hpP hqP).mp h
    · have hpn : p ≤ n := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hn1) h
      omega
  subst q
  have hmn : m = n := Nat.eq_of_mul_eq_mul_left hpP.pos hprod
  subst n
  rfl

/-- The sum of full owner-family sizes fits in the actual integer interval.
No prime-distribution estimate or replacement coefficient is used. -/
theorem owner_quotient_sum_le_interval (R x : ℕ)
    (hR : 2 ≤ R) (hx : x < R ^ 2) :
    (∑ p ∈ primeOwnersUpTo R x, x / p) ≤ x - R := by
  have hmap : Set.MapsTo (fun a : Σ _ : ℕ, ℕ => a.1 * a.2)
      (ownerPairs R x) (Finset.Ioc R x) := by
    intro a ha
    obtain ⟨hp, hm⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hpI, _hpP⟩ := Finset.mem_filter.mp hp
    obtain ⟨hRp, _hpx⟩ := Finset.mem_Ioc.mp hpI
    obtain ⟨hm1, hmle⟩ := Finset.mem_Icc.mp hm
    apply Finset.mem_Ioc.mpr
    constructor
    · have hp_le : a.1 ≤ a.1 * a.2 := by
        simpa only [mul_one] using Nat.mul_le_mul_left a.1 hm1
      exact hRp.trans_le hp_le
    · calc
        a.1 * a.2 ≤ a.1 * (x / a.1) := Nat.mul_le_mul_left a.1 hmle
        _ ≤ x := by simpa only [mul_comm] using Nat.div_mul_le_self x a.1
  have hcard := Finset.card_le_card_of_injOn (s := ownerPairs R x) (t := Finset.Ioc R x)
    (fun a : Σ _ : ℕ, ℕ => a.1 * a.2) hmap
    (ownerPair_mul_injective hR hx)
  simpa [ownerPairs, Finset.card_sigma, Nat.card_Icc, Nat.card_Ioc] using hcard

/-- The unchanged owner diagonal on a full prefix. -/
def diagonalUpTo (M : ℕ → ℝ) (R x : ℕ) : ℝ :=
  ∑ p ∈ primeOwnersUpTo R x, M (x / p) ^ 2

/-- Uniform capacity bound in the existing generic historical norm. -/
theorem diagonal_upTo_le_capacity (M : ℕ → ℝ) (R x : ℕ)
    (hR : 2 ≤ R) (hRx : R ≤ x) (hx : x < R ^ 2) :
    diagonalUpTo M R x ≤ ((x : ℝ) - R) * prefixAmplitude M R ^ 2 := by
  have hterm : ∀ p ∈ primeOwnersUpTo R x,
      M (x / p) ^ 2 ≤ prefixAmplitude M R ^ 2 * (x / p : ℕ) := by
    intro p hp
    obtain ⟨hc1, hcR⟩ := owner_cofactor_bounds_upTo hR hx hp
    have hm := abs_le_prefixAmplitude_mul_sqrt M hc1 hcR
    have hsq := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (prefixAmplitude_nonneg M R) (Real.sqrt_nonneg _))).mpr hm
    simpa only [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] using hsq
  have hcount : (∑ p ∈ primeOwnersUpTo R x, (x / p : ℕ) : ℝ) ≤
      (x : ℝ) - R := by
    have h := owner_quotient_sum_le_interval R x hR hx
    have hc : ((∑ p ∈ primeOwnersUpTo R x, x / p : ℕ) : ℝ) ≤
        ((x - R : ℕ) : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_sum, Nat.cast_sub hRx] using hc
  calc
    diagonalUpTo M R x ≤ ∑ p ∈ primeOwnersUpTo R x,
        prefixAmplitude M R ^ 2 * (x / p : ℕ) := Finset.sum_le_sum hterm
    _ = prefixAmplitude M R ^ 2 *
        (∑ p ∈ primeOwnersUpTo R x, (x / p : ℕ) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ prefixAmplitude M R ^ 2 * ((x : ℝ) - R) :=
      mul_le_mul_of_nonneg_left hcount (sq_nonneg _)
    _ = _ := mul_comm _ _

/-- Endpoint specialization is literally the existing generic owner diagonal. -/
theorem diagonalUpTo_endpoint (M : ℕ → ℝ) (R : ℕ) :
    diagonalUpTo M R (endpoint R) = diagonal M R := rfl

private theorem nativeM_eq_int_cast (n : ℕ) :
    nativeM n = (mertensSummatoryInt n : ℝ) := by
  unfold nativeM
  rw [← mertensSummatoryInt_cast n]
  simp only [Complex.intCast_re]

/-- The actual uncentered historical square costs at most three times K. -/
theorem nativeM_sq_le_three_historical {R y : ℕ}
    (hR : 2 ≤ R) (hy : 1 ≤ y) (hyR : y < R) :
    nativeM y ^ 2 ≤ 3 * squareRootHistoricalK R * y := by
  have hK1 : 1 ≤ squareRootHistoricalK R :=
    squareRootHistoricalK_one_le (by omega)
  by_cases hy1 : y = 1
  · subst y
    simp only [nativeM_one, one_pow, Nat.cast_one, mul_one]
    linarith
  by_cases hy2 : y = 2
  · subst y
    have hM2 : nativeM 2 = 0 := by
      have h2 : μ 2 = (-1 : ℤ) := ArithmeticFunction.moebius_apply_prime Nat.prime_two
      norm_num [nativeM, mertensSummatory, Finset.sum_range_succ,
        ArithmeticFunction.moebius_apply_one, h2]
    rw [hM2]
    nlinarith
  have hy3 : (3 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (show 3 ≤ y by omega)
  have hshift : (nativeM y - 1) ^ 2 ≤
      squareRootHistoricalK R * ((y : ℝ) + 1) := by
    have h := (squareRootHistoricalK_envelope R).2 y hyR
    simpa only [nativeM_eq_int_cast, Int.cast_sub, Int.cast_one,
      Nat.cast_add, Nat.cast_one] using h
  have hpos : 0 ≤ squareRootHistoricalK R * ((y : ℝ) - 3) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [sq_nonneg (nativeM y - 3)]

/-- Comparison in the original generic prefix-amplitude API. -/
theorem native_prefixAmplitude_sq_le_three_historical (R : ℕ) (hR : 2 ≤ R) :
    prefixAmplitude nativeM R ^ 2 ≤ 3 * squareRootHistoricalK R := by
  have hK1 : 1 ≤ squareRootHistoricalK R := squareRootHistoricalK_one_le (by omega)
  have hK0 : 0 ≤ 3 * squareRootHistoricalK R := by linarith
  have hroot1 : 1 ≤ Real.sqrt (3 * squareRootHistoricalK R) := by
    exact (Real.one_le_sqrt).mpr (by linarith)
  have hE : prefixAmplitude nativeM R ≤ Real.sqrt (3 * squareRootHistoricalK R) := by
    apply prefixAmplitude_le nativeM hroot1
    intro y hy hyR
    apply (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt (Nat.cast_nonneg y)]
    exact nativeM_sq_le_three_historical hR hy hyR
  have hs := (sq_le_sq₀ (prefixAmplitude_nonneg nativeM R) (Real.sqrt_nonneg _)).mpr hE
  simpa only [Real.sq_sqrt hK0] using hs

/-- The complete actual diagonal is paid uniformly by strict centered history. -/
theorem native_diagonal_upTo_le_historical (R x : ℕ)
    (hR : 2 ≤ R) (hRx : R ≤ x) (hx : x < R ^ 2) :
    diagonalUpTo nativeM R x ≤ 3 * ((x : ℝ) - R) * squareRootHistoricalK R := by
  have hdiff : 0 ≤ (x : ℝ) - R := sub_nonneg.mpr (by exact_mod_cast hRx)
  calc
    diagonalUpTo nativeM R x ≤ ((x : ℝ) - R) * prefixAmplitude nativeM R ^ 2 :=
      diagonal_upTo_le_capacity nativeM R x hR hRx hx
    _ ≤ ((x : ℝ) - R) * (3 * squareRootHistoricalK R) :=
      mul_le_mul_of_nonneg_left (native_prefixAmplitude_sq_le_three_historical R hR) hdiff
    _ = _ := by ring

/-- The improved endpoint is the existing original complex-norm diagonal. -/
theorem native_owner_diagonal_le_capacity (R : ℕ) (hR : 2 ≤ R) :
    ownerDiagonal R ≤
      3 * ((squareRootEndpoint R : ℝ) - R) * squareRootHistoricalK R := by
  have hRx : R ≤ endpoint R := by
    unfold endpoint
    apply Nat.le_sub_of_add_le
    nlinarith
  have hx : endpoint R < R ^ 2 := by
    unfold endpoint
    exact Nat.sub_lt (by positivity) (by norm_num)
  have h := native_diagonal_upTo_le_historical R (endpoint R) hR hRx hx
  rw [diagonalUpTo_endpoint, native_diagonal_eq_ownerDiagonal] at h
  exact h

/-- The original high-prime transport at an arbitrary endpoint. -/
def transportUpTo (M : ℕ → ℝ) (R x : ℕ) : ℝ :=
  ∑ p ∈ primeOwnersUpTo R x, M (x / p)

/-- Actual smooth population, with the pre-existing canonical smoothness mask. -/
def nativeSmoothUpTo (R x : ℕ) : ℝ :=
  (primeSieveSmoothMobiusMass R x).re

/-- Complete sharp signed decomposition at every prefix in the square horizon. -/
theorem native_decomposition_upTo (R x : ℕ) (hR : 2 ≤ R) (hx : x < R ^ 2) :
    nativeM x = nativeSmoothUpTo R x - transportUpTo nativeM R x := by
  have hroot : Nat.sqrt x ≤ R := (Nat.sqrt_lt'.mpr hx).le
  have h := mertensSummatory_eq_neg_signedSum_add_smoothMass_of_sqrt_le
    R x (by omega) hroot
  rw [primeSieveReciprocalMertensSignedSum_eq_mertensPrimeTail] at h
  simpa [nativeM, nativeSmoothUpTo, transportUpTo, primeOwnersUpTo,
    primeSieveMertensPrimeTail, Finset.sum_filter, apply_ite Complex.re,
    sub_eq_add_neg, add_comm] using congrArg Complex.re h

theorem transportUpTo_endpoint (M : ℕ → ℝ) (R : ℕ) :
    transportUpTo M R (endpoint R) = transport M R := rfl

/-- Exact bridge to the previously compiled native smooth source. -/
theorem nativeSmoothUpTo_endpoint (R : ℕ) (hR : 2 ≤ R) :
    nativeSmoothUpTo R (endpoint R) = nativeA R := by
  have hx : endpoint R < R ^ 2 := by
    unfold endpoint
    exact Nat.sub_lt (by positivity) (by norm_num)
  have hfull := native_decomposition_upTo R (endpoint R) hR hx
  rw [transportUpTo_endpoint] at hfull
  linarith [native_decomposition R hR]

/-- Both mixed orientations and every distinct-owner interaction remain here. -/
def nativeGammaUpTo (R x : ℕ) : ℝ :=
  nativeSmoothUpTo R x ^ 2 -
    2 * nativeSmoothUpTo R x * transportUpTo nativeM R x +
    transportUpTo nativeM R x ^ 2 - diagonalUpTo nativeM R x

/-- Exact complete energy, with no sign or size premise on the cross term. -/
theorem native_energy_upTo (R x : ℕ) (hR : 2 ≤ R) (hx : x < R ^ 2) :
    nativeM x ^ 2 = diagonalUpTo nativeM R x + nativeGammaUpTo R x := by
  rw [native_decomposition_upTo R x hR hx]
  unfold nativeGammaUpTo
  ring

/-- The new full-prefix cross term specializes to the original full owner Gram. -/
theorem nativeGammaUpTo_endpoint (R : ℕ) (hR : 2 ≤ R) :
    nativeGammaUpTo R (endpoint R) = fullOwnerGamma R := by
  simp only [nativeGammaUpTo, nativeSmoothUpTo_endpoint R hR,
    transportUpTo_endpoint, diagonalUpTo_endpoint]
  exact native_compensation_eq_fullOwnerGamma R hR

private theorem centered_energy_le_uncentered (m x : ℝ) (hx : 0 < x) :
    (m - 1) ^ 2 / (x + 1) ≤ m ^ 2 / x + 1 := by
  have he : m ^ 2 / x + 1 = (m ^ 2 + x) / x := by
    field_simp [ne_of_gt hx]
  rw [he]
  apply (div_le_div_iff₀ (by linarith : 0 < x + 1) hx).mpr
  nlinarith [sq_nonneg (m + x)]

/-- Full-prefix preservation with the complete signed estimate left explicit.
`L` can be any independently supplied upper bound on the historical K. -/
theorem native_historical_preservation_of_compensation
    (R : ℕ) (hR : 2 ≤ R) (L C : ℝ)
    (hKL : squareRootHistoricalK R ≤ L) (hC : 0 ≤ C)
    (hgamma : ∀ x : ℕ, R ≤ x → x < R ^ 2 →
      nativeGammaUpTo R x ≤ C * (x : ℝ) * L) :
    squareRootHistoricalK (R ^ 2) ≤ (4 + C) * L := by
  have hK1 : 1 ≤ squareRootHistoricalK R := squareRootHistoricalK_one_le (by omega)
  have hL1 : 1 ≤ L := hK1.trans hKL
  have hL0 : 0 ≤ L := by linarith
  have htarget : L ≤ (4 + C) * L := by nlinarith [mul_nonneg hC hL0]
  apply (squareRootHistoricalK_le_iff (R ^ 2) _).mpr
  refine ⟨by positivity, ?_⟩
  intro x hx
  by_cases hxR : x < R
  · have hh := (squareRootHistoricalK_envelope R).2 x hxR
    exact hh.trans (mul_le_mul_of_nonneg_right (hKL.trans htarget) (by positivity))
  have hRx : R ≤ x := by omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hD : diagonalUpTo nativeM R x ≤ 3 * (x : ℝ) * L := by
    have hbase := native_diagonal_upTo_le_historical R x hR hRx hx
    have hdiff : 0 ≤ (x : ℝ) - R := sub_nonneg.mpr (by exact_mod_cast hRx)
    have hreplace := mul_le_mul_of_nonneg_left hKL (by positivity : 0 ≤ 3 * ((x : ℝ) - R))
    have hR0 : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
    have hRL : 0 ≤ (R : ℝ) * L := mul_nonneg hR0 hL0
    nlinarith only [hbase, hreplace, hRL]
  have hM : nativeM x ^ 2 ≤ (3 + C) * (x : ℝ) * L := by
    rw [native_energy_upTo R x hR hx]
    nlinarith [hgamma x hRx hx]
  have hdiv : nativeM x ^ 2 / (x : ℝ) ≤ (3 + C) * L := by
    apply (div_le_iff₀ hxpos).mpr
    nlinarith only [hM]
  have he : (nativeM x - 1) ^ 2 / ((x : ℝ) + 1) ≤ (4 + C) * L := by
    have hc := centered_energy_le_uncentered (nativeM x) (x : ℝ) hxpos
    nlinarith
  have hs := (div_le_iff₀ (by positivity : 0 < (x : ℝ) + 1)).mp he
  simpa only [nativeM_eq_int_cast, Int.cast_sub, Int.cast_one,
    Nat.cast_add, Nat.cast_one] using hs

/-- The direct historical form has the fixed multiplier `4 + B`. -/
theorem native_historical_preservation_of_relative_compensation
    (R : ℕ) (hR : 2 ≤ R) (B : ℝ) (hB : 0 ≤ B)
    (hgamma : ∀ x : ℕ, R ≤ x → x < R ^ 2 →
      nativeGammaUpTo R x ≤ B * (x : ℝ) * squareRootHistoricalK R) :
    squareRootHistoricalK (R ^ 2) ≤ (4 + B) * squareRootHistoricalK R :=
  native_historical_preservation_of_compensation R hR
    (squareRootHistoricalK R) B le_rfl hB hgamma

end RHLean.Analysis.OwnerPrefix
