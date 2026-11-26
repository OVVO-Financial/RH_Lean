import RHLean.Analysis.AlpogeThin.NativeDyadicInertPrimeRange
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import RHLean.Geometry.NativeThetaIntegralGrid
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The rational Newton denominator at the selected inert primes

The degree sum measures the full product of coordinate factorials. The selected
window pair removes small primes from the unramified inert census.
-/

set_option autoImplicit false
open scoped BigOperators

namespace RHLean.Analysis.AlpogeThin

private theorem census_prime {e q d N p : ℕ} (hp : p ∈ nativeDyadicInertPrimes e q d N) :
    p.Prime :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2

private theorem val_prod_factorial {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι)
    (deg : ι → ℕ) :
    padicValNat p (∏ j ∈ s, (deg j).factorial) =
      ∑ j ∈ s, padicValNat p (deg j).factorial := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hn : (∏ k ∈ s, (deg k).factorial) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => Nat.factorial_ne_zero (deg k)
    rw [Finset.prod_insert hj, Finset.sum_insert hj, padicValNat.mul (Nat.factorial_ne_zero _) hn, ih]

/-- On the full outer interval the rational p-adic valuation of the original
    product of factorials costs at most twice the degree sum divided by x^(eps/10). -/
theorem nativeDyadicInertPrime_gridFactorial_cost {ι : Type*} {eps Y x : ℝ} {q d : ℕ}
    (hpair : UpperTheory.Top.WinPair eps Y q d) (heps : 0 ≤ eps) (hY : 0 ≤ Y) (hx : 0 ≤ x)
    (hcap : x ≤ Y ^ (2 : ℝ)) (e N p : ℕ) (hp : p ∈ nativeDyadicInertPrimes e q d N)
    (s : Finset ι) (deg : ι → ℕ) :
    x ^ (eps / 10) * (padicValNat p (∏ j ∈ s, (deg j).factorial) : ℝ) ≤
      2 * (∑ j ∈ s, (deg j : ℝ)) := by
  let : Fact p.Prime := ⟨census_prime hp⟩
  have hleg :
      (p - 1) * padicValNat p (∏ j ∈ s, (deg j).factorial) ≤ ∑ j ∈ s, deg j := by
    rw [val_prod_factorial, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [sub_one_mul_padicValNat_factorial (p := p) (deg j)]
    exact Nat.sub_le _ _
  have hscale : x ^ (eps / 10) ≤ 2 * ((p : ℝ) - 1) := by
    have hgap := nativeDyadicInertPrime_gt_winPair hpair e N p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (census_prime hp).two_le
    calc
      _ ≤ (Y ^ (2 : ℝ)) ^ (eps / 10) := Real.rpow_le_rpow hx hcap (by positivity)
      _ = Y ^ (eps / 5) := by rw [← Real.rpow_mul hY]; congr 1; ring
      _ ≤ _ := by linarith
  let v := padicValNat p (∏ j ∈ s, (deg j).factorial)
  change x ^ (eps / 10) * (v : ℝ) ≤ _
  calc
    _ ≤ (2 * ((p : ℝ) - 1)) * (v : ℝ) :=
      mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg v)
    _ = 2 * (((p - 1 : ℕ) : ℝ) * (v : ℝ)) := by
      rw [Nat.cast_sub (census_prime hp).one_le, Nat.cast_one]
      ring
    _ ≤ 2 * ((∑ j ∈ s, deg j : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hleg) (by norm_num)
    _ = _ := by rw [Nat.cast_sum]

/-- Every factorial in a box lying below the small-prime threshold is a unit
    at each remaining rational inert prime. -/
theorem nativeDyadicInertPrime_gridFactorial_val_eq_zero {ι : Type*} {eps Y : ℝ} {q d : ℕ}
    (hpair : UpperTheory.Top.WinPair eps Y q d) (e N p : ℕ)
    (hp : p ∈ nativeDyadicInertPrimes e q d N) (s : Finset ι) (deg : ι → ℕ)
    (hdeg : ∀ j ∈ s, (deg j : ℝ) ≤ Y ^ (eps / 5)) :
    padicValNat p (∏ j ∈ s, (deg j).factorial) = 0 := by
  let : Fact p.Prime := ⟨census_prime hp⟩
  rw [val_prod_factorial]
  apply Finset.sum_eq_zero
  intro j hj
  have hsmall : deg j < p := by
    exact_mod_cast (hdeg j hj).trans_lt (nativeDyadicInertPrime_gt_winPair hpair e N p hp)
  have hval := padicValNat_mul_div_factorial (p := p) (deg j)
  rw [Nat.div_eq_of_lt hsmall, Nat.mul_zero, Nat.factorial_zero] at hval
  simpa using hval.symm

end RHLean.Analysis.AlpogeThin

/-!
# The local depth of the native grid at a selected prime

The depth of a rational integer in the local DVR retains the full factor
v_O(p). In particular, a unit coefficient is detected by a unit grid value
when all coordinate degrees lie below the selected pair's small-prime cutoff.
-/

set_option autoImplicit false
open scoped BigOperators
namespace RHLean.Analysis.AlpogeThin

theorem nativeDyadicDvr_addVal_natCast (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField O) p] (n : ℕ) (hn : n ≠ 0) :
    IsDiscreteValuationRing.addVal O (n : O) =
      padicValNat p n • IsDiscreteValuationRing.addVal O (p : O) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨a, u, hunit, hn'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hunit (dvd_zero p)
  have hres : IsLocalRing.residue O (u : O) ≠ 0 := by
    rw [map_natCast]
    exact (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField O) p u).not.mpr hunit
  have hu := (IsLocalRing.residue_ne_zero_iff_isUnit (u : O)).mp hres
  have hval : padicValNat p n = a := by
    rw [hn', padicValNat.mul (pow_ne_zero _ hp.ne_zero) hu0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hunit, add_zero]
  rw [hval, hn', Nat.cast_mul, Nat.cast_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu, add_zero]

/-- A primitive coefficient at an actual inert prime supplies a full-grid
    value whose DVR depth is bounded by the rational budget times v_O(p). -/
theorem nativeDyadicInertPrime_exists_grid_eval_at_rationalDepth
    {O σ : Type*} [CommRing O] [IsDomain O] [CharZero O] [IsDiscreteValuationRing O] [Fintype σ]
    (e q d N p : ℕ) (hp : p ∈ nativeDyadicInertPrimes e q d N)
    [CharP (IsLocalRing.ResidueField O) p] (deg : σ → ℕ) (P : MvPolynomial σ O)
    (hdeg : ∀ i, P.degreeOf i ≤ deg i) (m : σ →₀ ℕ) (hm : IsUnit (P.coeff m)) :
    ∃ j : (i : σ) → Fin (deg i + 1), IsDiscreteValuationRing.addVal O
        (MvPolynomial.eval (fun i => ((j i : ℕ) : O)) P) ≤
      padicValNat p (∏ i, (deg i).factorial) • IsDiscreteValuationRing.addVal O (p : O) := by
  let : Fact p.Prime := ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2⟩
  obtain ⟨j, hj⟩ := RHLean.Geometry.NativeTheta.GridInterpolation.exists_grid_eval_addVal_le_factorial
    deg P hdeg m hm
  refine ⟨j, hj.trans_eq ?_⟩
  have hn : (∏ i, (deg i).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (deg i)
  simpa only [Nat.cast_prod] using nativeDyadicDvr_addVal_natCast O p (∏ i, (deg i).factorial) hn

/-- At every selected inert prime all primitive polynomials in the small
    coordinate box have a unit integral grid evaluation. -/
theorem nativeDyadicInertPrime_exists_grid_unit_of_winPair
    {O σ : Type*} [CommRing O] [IsDomain O] [CharZero O] [IsDiscreteValuationRing O] [Fintype σ]
    {eps Y : ℝ} {q d : ℕ} (hpair : UpperTheory.Top.WinPair eps Y q d) (e N p : ℕ)
    (hp : p ∈ nativeDyadicInertPrimes e q d N) [CharP (IsLocalRing.ResidueField O) p]
    (deg : σ → ℕ) (hsmall : ∀ i, (deg i : ℝ) ≤ Y ^ (eps / 5))
    (P : MvPolynomial σ O) (hdeg : ∀ i, P.degreeOf i ≤ deg i)
    (m : σ →₀ ℕ) (hm : IsUnit (P.coeff m)) :
    ∃ j : (i : σ) → Fin (deg i + 1), IsUnit (MvPolynomial.eval (fun i => ((j i : ℕ) : O)) P) := by
  obtain ⟨j, hj⟩ := nativeDyadicInertPrime_exists_grid_eval_at_rationalDepth
    e q d N p hp deg P hdeg m hm
  have hv := nativeDyadicInertPrime_gridFactorial_val_eq_zero hpair e N p hp Finset.univ deg
    (fun j _ => hsmall j)
  rw [hv, zero_nsmul] at hj
  exact ⟨j, IsDiscreteValuationRing.addVal_eq_zero_iff.mp (le_antisymm hj zero_le)⟩

end RHLean.Analysis.AlpogeThin
