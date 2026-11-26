import RHLean.Analysis.AlpogeThin.NativeDyadicPrimePowerIncidence
import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Bounds for a genuine return of the dyadic Frobenius displacement
of an odd prime. The logarithmic length of the original thin cutoff can
be much smaller than the first return exponent of a square-prefix prime. -/

noncomputable section

namespace RHLean.Analysis.AlpogeThin

/-- A positive dyadic return forces the full dyadic modulus to divide
a linear function of the exponent. Odd conductor primes are allowed. -/
theorem nativeDyadic_modulus_dvd_of_return (e q d p k : ℕ)
    [Fact q.Prime] [Fact d.Prime] (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k)
    (hret : k • ((alpogeNativeHostData e q d).frob p).2 = 0) :
    2 ^ (e + 2) ∣ (p ^ 2 - 1) * k := by
  let u := ZMod.unitsMap (alpogeNativeTwo_dvd_hostN e q d)
    (alpogeNativeFrobUnit (alpogeNativeHostN e q d) p)
  let π := QuotientGroup.mk' (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
  have hcompl : 2 ^ (e + 2) ∣ ordCompl[p] (alpogeNativeHostN e q d) :=
    Nat.dvd_ordCompl_of_dvd_not_dvd (alpogeNativeTwo_dvd_hostN e q d) fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hup : ((u : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = p := by
    dsimp only [u]
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      ((alpogeNativeFrobUnit_modEq (N := alpogeNativeHostN e q d) hp).1.of_dvd hcompl)
  change π u ^ k = 1 at hret
  have hm : π (u ^ k) = 1 := by rwa [map_pow]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ((QuotientGroup.eq_one_iff (u ^ k)).mp hm)
  have hsq : (u ^ k) ^ 2 = 1 := by
    rw [← hj]
    rcases Int.even_or_odd j with he | ho
    · rw [he.neg_one_zpow, one_pow]
    · rw [ho.neg_one_zpow]
      apply Units.ext
      simp only [Units.val_one, neg_one_sq]
  have hres : ((p ^ (2 * k) : ℕ) : ZMod (2 ^ (e + 2))) = 1 := by
    simpa only [Nat.cast_pow, mul_comm 2 k, pow_mul, Units.val_pow_eq_pow_val,
      Units.val_one, hup] using congrArg Units.val hsq
  have hp2k : 1 < p ^ (2 * k) := one_lt_pow₀ hp.one_lt (by positivity)
  have hmod : 1 ≡ p ^ (2 * k) [MOD 2 ^ (e + 2)] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa only [Nat.cast_one] using hres.symm)
  have hdiv := (Nat.modEq_iff_dvd' hp2k.le).mp hmod
  have hodd : ¬ 2 ∣ p := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  have hs : 0 < p ^ 2 - 1 := Nat.sub_pos_of_lt (one_lt_pow₀ hp.one_lt (by decide))
  have hval : padicValNat 2 (p ^ (2 * k) - 1) = padicValNat 2 ((p ^ 2 - 1) * k) := by
    have hlong := padicValNat.pow_two_sub_one hp.one_lt hodd
      (by positivity : 2 * k ≠ 0) (even_two_mul k)
    have hshort := padicValNat.pow_two_sub_one hp.one_lt hodd
      (by decide : (2 : ℕ) ≠ 0) (by decide : Even (2 : ℕ))
    rw [padicValNat.mul (p := 2) (by decide : (2 : ℕ) ≠ 0) hk.ne'] at hlong
    rw [padicValNat.mul (p := 2) hs.ne' hk.ne']
    omega
  apply (padicValNat_dvd_iff_le (mul_pos hs hk).ne').mpr
  rw [← hval]
  exact (padicValNat_dvd_iff_le (Nat.sub_pos_of_lt hp2k).ne').mp hdiv

/-- Even very large powers of a small base cannot return before this
exponent bound. The decisive quantity is the exponent, not the power. -/
theorem nativeDyadic_exp_lt_order_of_quadratic_bound (e q d p i : ℕ)
    [Fact q.Prime] [Fact d.Prime] (hp : p.Prime) (hp2 : p ≠ 2)
    (hi : (p ^ 2 - 1) * i < 2 ^ (e + 2)) :
    i < addOrderOf ((alpogeNativeHostData e q d).frob p).2 := by
  let g := ((alpogeNativeHostData e q d).frob p).2
  change i < addOrderOf g
  by_contra! hle
  have hk := addOrderOf_pos g
  have hs : 0 < p ^ 2 - 1 := Nat.sub_pos_of_lt (one_lt_pow₀ hp.one_lt (by decide))
  have hdiv := nativeDyadic_modulus_dvd_of_return e q d p (addOrderOf g) hp hp2 hk
    (addOrderOf_nsmul_eq_zero g)
  exact hi.not_ge ((Nat.le_of_dvd (mul_pos hs hk) hdiv).trans (Nat.mul_le_mul_left _ hle))

open Filter in
/-- Every exponent of every odd prime base up to the square anchor is
strictly before its first return throughout the full native scalar
cutoff bound (4x^4\exp(x^{\varepsilon/3})). The small bases and
exponents may vary across the entire window. -/
theorem nativeDyadicPageN_small_bases_before_return_full_cutoff
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (e q d p i : ℕ) [Fact q.Prime] [Fact d.Prime],
      UpperTheory.Top.PageN ε x e → p.Prime → p ≠ 2 → (p : ℝ) ≤ x →
      (p : ℝ) ^ i ≤ 4 * x ^ (4 : ℕ) * Real.exp (x ^ (ε / 3)) →
      i < addOrderOf ((alpogeNativeHostData e q d).frob p).2 := by
  have hlog := (isLittleO_log_rpow_atTop (by positivity : 0 < 8 * ε)).bound
    (by norm_num : 0 < (1 / 16 : ℝ))
  have hgrowth : ∀ᶠ x : ℝ in atTop, 8 ≤ x ^ (8 * ε) :=
    (tendsto_rpow_atTop (by positivity : 0 < 8 * ε)).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlog, hgrowth] with x hx hxlog hxgrow
  intro e q d p i _ _ hPage hp hp2 hpx hpow
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlogp : 1 / 2 < Real.log p :=
    lt_of_lt_of_le (show (1 / 2 : ℝ) < Real.log 2 by linarith only [Real.log_two_gt_d9])
      (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hp2')
  have hilog : (i : ℝ) * Real.log p ≤ Real.log 4 + 4 * Real.log x + x ^ (ε / 3) := by
    have h := Real.log_le_log (pow_pos hp0 i) hpow
    simpa only [Real.log_mul (by positivity : (4 : ℝ) * x ^ (4 : ℕ) ≠ 0)
        (Real.exp_ne_zero _), Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (pow_ne_zero 4 hx0.ne'), Real.log_exp, Real.log_pow, Nat.cast_ofNat] using h
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
    Real.norm_of_nonneg (Real.log_nonneg hx)] at hxlog
  have hsmall : x ^ (ε / 3) ≤ x ^ (8 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hi : (i : ℝ) < 4 * x ^ (8 * ε) := by
    linarith only [mul_le_mul_of_nonneg_left hlogp.le (Nat.cast_nonneg (α := ℝ) i),
      hilog, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4),
      hxlog, hxgrow, hsmall]
  apply nativeDyadic_exp_lt_order_of_quadratic_bound e q d p i hp hp2
  suffices h : (p : ℝ) ^ (2 : ℕ) * (i : ℝ) < (2 : ℝ) ^ (e + 2) by
    have hnat : p ^ 2 * i < 2 ^ (e + 2) := by exact_mod_cast h
    exact (Nat.mul_le_mul_right _ (Nat.sub_le (p ^ 2) 1)).trans_lt hnat
  calc
    (p : ℝ) ^ (2 : ℕ) * (i : ℝ) ≤ x ^ (2 : ℕ) * (i : ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp0.le hpx _) (Nat.cast_nonneg _)
    _ < x ^ (2 : ℕ) * (4 * x ^ (8 * ε)) := mul_lt_mul_of_pos_left hi (pow_pos hx0 _)
    _ = 4 * x ^ (2 + 8 * ε) := by rw [Real.rpow_add hx0, Real.rpow_two]; ring
    _ ≤ 4 * (2 : ℝ) ^ e := mul_le_mul_of_nonneg_left hPage.1 (by norm_num)
    _ = (2 : ℝ) ^ (e + 2) := by rw [pow_add]; ring

end RHLean.Analysis.AlpogeThin

end
