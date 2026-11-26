import RHLean.Analysis.AlpogeThin.NativeDyadicCostWindows
import RHLean.Analysis.AlpogeThin.NativeGeometricCostWindows
import RHLean.Analysis.AlpogeNativeLocalGainSource
import RHLean.Analysis.AlpogeNativeSquareMultiplicity

/-!
# Pay concrete remaining scalar costs on the original native source

The local shift price includes all active inert prime powers and the actual
TT and lift multiplicities. The existing Chebyshev bound and the original
thin-width lower bound pay this price uniformly by 1/x. The cutoff is
literally ceil(Amax/beta), not a smaller frozen cutoff.

The native unit-interval Gz movement estimate also extends to arbitrary
distances on [1,infinity). Thus the scalar recovery needs only the mean
absolute displacement of the actual heights, not a pointwise unit window.
Use the spare factor four in the existing geometric-size theorem, without
changing its exponent. At square endpoints the existing PageN construction
and m=R, k=x*R supply the scalar multiplicity windows.

These are arithmetic and scalar supplier reductions, not a construction of
the missing geometric gain or a proof of RH. Every physical parameter and
its compatibility hypothesis remains explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open Filter
open scoped BigOperators Classical Topology

namespace RHLean.Analysis.AlpogeThin

/-- The full cutoff shift bill is eventually paid at the original
thin-width scale, uniformly over the remaining physical parameters. -/
theorem nativeDyadicLocalShiftCost_scalar_eventually
    (eps : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ (n b beta c Amax Delta : ℝ),
      1 ≤ n → n ≤ x ^ (3 : ℕ) →
      0 < beta → 0 ≤ c → 0 ≤ Amax →
      Real.exp (x ^ eps) ≤ b →
      b / (n * Real.exp (x ^ (eps / 3))) ≤ beta →
      c ≤ 4 * Real.exp (x ^ (eps / 4)) →
      Amax / b ≤ x + 1 → x ^ (-eps) ≤ Delta →
      12 * (Real.log 4 + 2) * c * (Nat.ceil (Amax / beta) : ℝ) /
        (b * Delta) ≤ 1 / x := by
  have hp := dyadic_rpow_le_exp_eventually (6 + eps) (eps / 3) (by positivity)
  have hg : ∀ᶠ x : ℝ in atTop, (3 : ℝ) ≤ x ^ (2 * eps / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  filter_upwards [hp, hg, eventually_ge_atTop (768 : ℝ)] with x hpoly hgrow hx
  intro n b beta c Amax Delta hn1 hn hbeta hc hAmax hb hmin hcup hmax hDelta
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hn0 : 0 < n := by linarith
  have hb0 : 0 < b := (Real.exp_pos _).trans_le hb
  let E := Real.exp (x ^ (eps / 3))
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hnE : 1 ≤ n * E := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hE1)]
  have hbeta' : b ≤ beta * (n * E) :=
    (div_le_iff₀ (mul_pos hn0 hE0)).mp hmin
  have hratio : Amax / beta ≤ (x + 1) * (n * E) := by
    apply (div_le_iff₀ hbeta).mpr
    calc
      Amax ≤ (x + 1) * b := (div_le_iff₀ hb0).mp hmax
      _ ≤ (x + 1) * (beta * (n * E)) :=
        mul_le_mul_of_nonneg_left hbeta' (by positivity)
      _ = _ := by ring
  have hN : (Nat.ceil (Amax / beta) : ℝ) ≤ 4 * x ^ (4 : ℕ) * E := by
    calc
      _ ≤ Amax / beta + 1 := (Nat.ceil_lt_add_one (div_nonneg hAmax hbeta.le)).le
      _ ≤ (x + 1) * (n * E) + 1 := by linarith only [hratio]
      _ ≤ (x + 2) * (n * E) := by nlinarith only [hnE]
      _ ≤ (4 * x) * (n * E) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (4 * x) * (x ^ (3 : ℕ) * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn hE0.le) (by positivity)
      _ = _ := by ring
  have hcE : c ≤ 4 * E := hcup.trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)))
      (by norm_num))
  have hlog : Real.log (4 : ℝ) + 2 ≤ 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9]
  let F := 12 * (Real.log 4 + 2) * c * (Nat.ceil (Amax / beta) : ℝ)
  have hnum : F ≤ 768 * x ^ (4 : ℕ) * E ^ (2 : ℕ) := by
    dsimp only [F]
    calc
      _ ≤ (12 * 4) * c * (Nat.ceil (Amax / beta) : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog (by norm_num)) hc) (Nat.cast_nonneg _)
      _ ≤ (12 * 4) * (4 * E) * (Nat.ceil (Amax / beta) : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcE (by norm_num))
          (Nat.cast_nonneg _)
      _ ≤ (12 * 4) * (4 * E) * (4 * x ^ (4 : ℕ) * E) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      _ = _ := by ring
  have hpE : 768 * x ^ (4 : ℕ) * x * x ^ eps ≤ E := by
    calc
      _ ≤ x * x ^ (4 : ℕ) * x * x ^ eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hx (by positivity)) hx0.le)
          (Real.rpow_nonneg hx0.le _)
      _ = x ^ (6 : ℕ) * x ^ eps := by ring
      _ = x ^ (6 + eps) := by
        rw [Real.rpow_add hx0, show x ^ (6 : ℝ) = x ^ (6 : ℕ) from
          Real.rpow_natCast x 6]
      _ ≤ E := hpoly
  have hExp : x ^ eps = x ^ (2 * eps / 3) * x ^ (eps / 3) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hEcube : E ^ (3 : ℕ) ≤ b := by
    calc
      _ = E * E * E := by ring
      _ = Real.exp (x ^ (eps / 3) + x ^ (eps / 3) + x ^ (eps / 3)) := by
        dsimp only [E]
        rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (x ^ eps) := by
        apply Real.exp_le_exp.mpr
        rw [hExp]
        nlinarith only [mul_le_mul_of_nonneg_right hgrow (Real.rpow_nonneg hx0.le (eps / 3))]
      _ ≤ b := hb
  have hpaid : F * x * x ^ eps ≤ b := by
    calc
      _ ≤ (768 * x ^ (4 : ℕ) * E ^ (2 : ℕ)) * x * x ^ eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnum hx0.le) (Real.rpow_nonneg hx0.le _)
      _ = (768 * x ^ (4 : ℕ) * x * x ^ eps) * E ^ (2 : ℕ) := by ring
      _ ≤ E * E ^ (2 : ℕ) := mul_le_mul_of_nonneg_right hpE (by positivity)
      _ = E ^ (3 : ℕ) := by ring
      _ ≤ b := hEcube
  have hDelta0 : 0 < Delta := (Real.rpow_pos_of_pos hx0 _).trans_le hDelta
  have hDeltaMul : 1 ≤ Delta * x ^ eps := by
    have h := mul_le_mul_of_nonneg_right hDelta (Real.rpow_nonneg hx0.le eps)
    rw [← Real.rpow_add hx0, neg_add_cancel, Real.rpow_zero] at h
    exact h
  have hpaid' : F * x * x ^ eps ≤ b * Delta * x ^ eps := hpaid.trans (calc
    b = b * 1 := by ring
    _ ≤ b * (Delta * x ^ eps) := mul_le_mul_of_nonneg_left hDeltaMul hb0.le
    _ = _ := by ring)
  have hfinal : F * x ≤ b * Delta := by
    by_contra! hgt
    exact (not_lt_of_ge hpaid')
      (mul_lt_mul_of_pos_right hgt (Real.rpow_pos_of_pos hx0 eps))
  exact (div_le_div_iff₀ (mul_pos hb0 hDelta0) hx0).mpr
    (by simpa only [one_mul] using hfinal)

/-- The actual prime-power price at the same constructed cutoff is paid.
No distribution theorem about the surviving low-central source is used. -/
theorem nativeDyadicLocalLogShiftPrice_eventually
    (eps : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, ∀ (e q d m : ℕ) (TT T2 : Finset (AlpogeNativeDyadicH e)),
      TT.Nonempty → T2.Nonempty → 0 < m →
      (Fintype.card (AlpogeNativeDyadicH e) : ℝ) ≤ x ^ (3 : ℕ) →
      ∀ (b beta c Amax : ℝ), 0 < beta → 0 ≤ c → 0 ≤ Amax →
      Real.exp (x ^ eps) ≤ b →
      b / ((Fintype.card (AlpogeNativeDyadicH e) : ℝ) *
        Real.exp (x ^ (eps / 3))) ≤ beta →
      c ≤ 4 * Real.exp (x ^ (eps / 4)) →
      Amax / b ≤ x + 1 → x ^ (-eps) ≤ alpogeNativeProjectionDensity T2 →
      (∑ _t ∈ TT, ∑ _j : Fin m,
        ∑ p ∈ nativeDyadicInertPrimes e q d (Nat.ceil (Amax / beta)),
          (2 * Real.log p) * (3 * c * (Nat.log p (Nat.ceil (Amax / beta)) : ℝ))) /
        alpogeNativeProjectionDivisor TT T2 m b ≤ 1 / x := by
  filter_upwards [nativeDyadicLocalShiftCost_scalar_eventually eps he] with x hx
  intro e q d m TT T2 hTT hT2 hm hn b beta c Amax hbeta hc hAmax hb hmin hcup hmax hd
  have hn1 : (1 : ℝ) ≤ Fintype.card (AlpogeNativeDyadicH e) := by
    exact_mod_cast (show 1 ≤ Fintype.card (AlpogeNativeDyadicH e) from Fintype.card_pos)
  have hb0 : 0 < b := (Real.exp_pos _).trans_le hb
  exact (nativeDyadicLocalLogShiftPrice_normalized_le e q d
    (Nat.ceil (Amax / beta)) m TT T2 hTT hT2 hm b c hb0 hc).trans
    (hx _ b beta c Amax _ hn1 hn hbeta hc hAmax hb hmin hcup hmax hd)

end RHLean.Analysis.AlpogeThin

namespace RHLean.Analysis

private theorem nativeGz_ordered_move (y z : ℝ) (hz : 1 ≤ z) (hzy : z ≤ y) :
    |alpogeNativeGzArithmetic y - alpogeNativeGzArithmetic z| ≤
      alpogeNativeMoveConstant * (y - z) := by
  have aux : ∀ n : ℕ, ∀ u v : ℝ, 1 ≤ v → v ≤ u → u ≤ v + (n : ℝ) →
      |alpogeNativeGzArithmetic u - alpogeNativeGzArithmetic v| ≤
        alpogeNativeMoveConstant * (u - v) := by
    intro n
    induction n with
    | zero =>
      intro u v _hv hvu huv
      have e : u = v := le_antisymm (by simpa using huv) hvu
      simp [e]
    | succ n ih =>
      intro u v hv hvu huv
      by_cases hsmall : u ≤ v + 1
      · exact alpogeNativeGzArithmetic_sub_abs_le_of_le u v hv hvu hsmall
      · have hmid : v + 1 ≤ u := (lt_of_not_ge hsmall).le
        have hu' : u ≤ v + 1 + (n : ℝ) := by
          push_cast at huv
          linarith
        have h1 := ih u (v + 1) (by linarith) hmid hu'
        have h2 := alpogeNativeGzArithmetic_sub_abs_le_of_le (v + 1) v hv
          (by linarith) le_rfl
        calc
          _ = |(alpogeNativeGzArithmetic u - alpogeNativeGzArithmetic (v + 1)) +
              (alpogeNativeGzArithmetic (v + 1) - alpogeNativeGzArithmetic v)| := by
            congr 1
            ring
          _ ≤ |alpogeNativeGzArithmetic u - alpogeNativeGzArithmetic (v + 1)| +
              |alpogeNativeGzArithmetic (v + 1) - alpogeNativeGzArithmetic v| :=
            abs_add_le _ _
          _ ≤ alpogeNativeMoveConstant * (u - (v + 1)) +
              alpogeNativeMoveConstant * (v + 1 - v) := add_le_add h1 h2
          _ = _ := by ring
  exact aux (Nat.ceil (y - z)) y z hz hzy (by linarith [Nat.le_ceil (y - z)])

/-- Global arithmetic movement, with the same constant as on one cell. -/
theorem alpogeNativeGzArithmetic_sub_abs_le_global (y z : ℝ) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    |alpogeNativeGzArithmetic y - alpogeNativeGzArithmetic z| ≤
      alpogeNativeMoveConstant * |y - z| := by
  rcases le_total z y with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact nativeGz_ordered_move y z hz h
  · rw [abs_sub_comm (alpogeNativeGzArithmetic y) (alpogeNativeGzArithmetic z),
      abs_sub_comm y z, abs_of_nonneg (sub_nonneg.mpr h)]
    exact nativeGz_ordered_move z y hy h

/-- Recover a point from the actual mean, with only the mean absolute
displacement charged. A pointwise unit-cell hypothesis is unnecessary. -/
theorem alpogeNativeGzArithmetic_le_mean_add_move
    {ι : Type*} (TT : Finset ι) (hTT : TT.Nonempty)
    (x : ℝ) (v : ι → ℝ) (hx : 1 ≤ x) (hv : ∀ t ∈ TT, 1 ≤ v t) :
    alpogeNativeGzArithmetic x ≤
      (1 / (TT.card : ℝ)) * ∑ t ∈ TT, alpogeNativeGzArithmetic (v t) +
      alpogeNativeMoveConstant * ((1 / (TT.card : ℝ)) * ∑ t ∈ TT, |x - v t|) := by
  have hcard : (0 : ℝ) < TT.card := by exact_mod_cast hTT.card_pos
  have hpt : ∀ t ∈ TT, alpogeNativeGzArithmetic x ≤
      alpogeNativeGzArithmetic (v t) + alpogeNativeMoveConstant * |x - v t| := by
    intro t ht
    linarith only [(le_abs_self (alpogeNativeGzArithmetic x -
      alpogeNativeGzArithmetic (v t))).trans
      (alpogeNativeGzArithmetic_sub_abs_le_global x (v t) hx (hv t ht))]
  have hs : (TT.card : ℝ) * alpogeNativeGzArithmetic x ≤
      (∑ t ∈ TT, alpogeNativeGzArithmetic (v t)) +
        alpogeNativeMoveConstant * ∑ t ∈ TT, |x - v t| := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      using (Finset.sum_le_sum (s := TT) hpt)
  calc
    _ = (1 / (TT.card : ℝ)) * ((TT.card : ℝ) * alpogeNativeGzArithmetic x) := by
      field_simp [hcard.ne']
    _ ≤ (1 / (TT.card : ℝ)) * ((∑ t ∈ TT, alpogeNativeGzArithmetic (v t)) +
        alpogeNativeMoveConstant * ∑ t ∈ TT, |x - v t|) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end RHLean.Analysis

namespace RHLean.Analysis.AlpogeThin

open NativeGeometricCostWindows

/-- On the original PageN host at x=R^2-1, the actual geometric size
windows require the top/thick counts and aE bound, not a fresh multiplicity
or lattice-size inequality. The physical k-identification is still needed. -/
theorem geometricSizeWindows_of_squareClock_pageN
    (R : ℕ) (hR : 2 ≤ R) (eps C : ℝ) (he52 : eps < 1 / 52)
    (hLarge : alpogeNativeLargeX eps C ((R ^ 2 - 1 : ℕ) : ℝ))
    (e : ℕ) (hPage : UpperTheory.Top.PageN eps ((R ^ 2 - 1 : ℕ) : ℝ) e)
    (TT T2 : Finset (AlpogeNativeDyadicH e)) (b aE : ℝ)
    (hb : 0 < b) (haE0 : 0 ≤ aE)
    (haE : aE ≤ 2 * ((R ^ 2 - 1 : ℕ) : ℝ) * b)
    (hTop : ((R ^ 2 - 1 : ℕ) : ℝ) ^ (-(eps / 8)) *
        Fintype.card (AlpogeNativeDyadicH e) / 2 ≤ TT.card)
    (hThick : ((R ^ 2 - 1 : ℕ) : ℝ) ^ (-eps) ≤
        (T2.card : ℝ) / Fintype.card (AlpogeNativeDyadicH e)) :
    GeometricSizeWindows C eps ((R ^ 2 - 1 : ℕ) : ℝ)
      (Fintype.card (AlpogeNativeDyadicH e)) TT.card T2.card R b
      (((R ^ 2 - 1 : ℕ) : ℝ) * R) aE := by
  have hS := alpogeNativeSquareMultiplicity_pageN_of_largeX R hR eps C he52 hLarge
    e hPage TT.card T2.card b aE hb haE hTop hThick
  obtain ⟨he, hC, hx3, h26, _hmove⟩ := hLarge
  exact ⟨hx3, he, hC, Fintype.card_pos, hb, haE0, haE, hTop, hThick,
    Finset.card_le_univ T2, hS.mult_lower, hS.mult_upper, hS.k_lower, hS.k_upper, h26⟩

/-- The existing normalized geometric cost plus the analytic remainder
and a paid mean height displacement yield the original scalar exponent.
The hypothesis is the actual mean Gz from the constructed signed-slope
payment; no pointwise critical Gz inequality is used. -/
theorem nativeGz_le_of_mean_normalizedCosts
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (C eps x : ℝ) (TT T2 : Finset H) (m : ℕ) (b k aE : ℝ) (v : H → ℝ)
    (hW : GeometricSizeWindows C eps x (Fintype.card H) TT.card T2.card m b k aE)
    (hv : ∀ t ∈ TT, 1 ≤ v t)
    (hMean : (1 / (TT.card : ℝ)) * ∑ t ∈ TT, alpogeNativeGzArithmetic (v t) ≤
      x ^ (C * eps) * alpogeNativeNormalizedGeometricCosts TT.card
        (alpogeNativeProjectionDensity T2) (Fintype.card H) m b k aE (x ^ eps) +
        x ^ ((1 : ℝ) / 2 + eps))
    (hMove : alpogeNativeMoveConstant * ((1 / (TT.card : ℝ)) *
      ∑ t ∈ TT, |x - v t|) ≤ 3 * x ^ ((1 : ℝ) / 2 + eps)) :
    alpogeNativeGzArithmetic x ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * eps) := by
  have hx : 1 ≤ x := by linarith [hW.1]
  have hx0 : 0 < x := by linarith
  have hT : (0 : ℝ) < TT.card := by
    have hp := Real.rpow_pos_of_pos hx0 (-(eps / 8))
    exact lt_of_lt_of_le (by positivity) hW.2.2.2.2.2.2.2.1
  have hTT : TT.Nonempty := Finset.card_pos.mp (by exact_mod_cast hT)
  have hpoint := alpogeNativeGzArithmetic_le_mean_add_move TT hTT x v hx hv
  apply le_trans _ (normalizedCosts_add_remainder_le C eps x TT T2 m b k aE
    (4 * x ^ ((1 : ℝ) / 2 + eps)) hW le_rfl)
  linarith only [hpoint, hMean, hMove]

end RHLean.Analysis.AlpogeThin

end
