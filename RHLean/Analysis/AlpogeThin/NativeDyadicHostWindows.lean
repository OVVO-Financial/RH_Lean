import RHLean.Analysis.AlpogeNativeDyadicHostSize
import RHLean.Analysis.AlpogeThin.Development.AutomorphicArithmetic.CharacterBoxes.PairGood

/-!
# The constructed dyadic host satisfies its original size and conductor windows

The native source theorem `UpperTheory.Top.exists_pageN` chooses the dyadic
exponent at every real scale. This file applies that SAME chooser to the actual
quotient host: its cardinality satisfies the original `SizeN` exponents, and
the actual conductor `2^(e+2)qd` satisfies the thin theorem's logarithmic bound
for every selected `WinPair` with `1 ≤ Y ≤ x`.

Sources: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`CharacterBoxes/ExistsPageN.lean`, `Formalism/SharpRestriction/ElevenLe.lean`,
and the logarithmic argument in
`CMFieldExponentialBounds/LogConductorMulHeightLeOfPageN.lean`.

These are constructed arithmetic witnesses. The map group of geometric
descent is not identified with this arithmetic host, and no theta/cover
datum, section lattice or physical top-excess bound is supplied here.
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace RHLean.Analysis.AlpogeThin

/-- The actual host satisfies the original `SizeN` interval, with the source's
slack `eps / 100`. The exponent is the existing constructed `PageN` exponent. -/
theorem nativePageN_sizeN_eventually (eps : ℝ) (he : 0 < eps) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ e : ℕ,
      UpperTheory.Top.PageN eps x e →
      x ^ (2 + 8 * eps - eps / 100) ≤
          (Fintype.card (AlpogeNativeDyadicH e) : ℝ) ∧
        (Fintype.card (AlpogeNativeDyadicH e) : ℝ) ≤
          x ^ (2 + 8 * eps + eps / 100) := by
  have hg := (tendsto_rpow_atTop (by positivity : 0 < eps / 100)).eventually_ge_atTop 2
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (hg.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨x₀, fun x hx e hP => ?_⟩
  obtain ⟨hmargin, hx1⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  rw [alpogeNativeDyadicH_card, Nat.cast_pow, Nat.cast_ofNat]
  constructor
  · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans hP.1
  · calc
      (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * eps) := hP.2
      _ ≤ x ^ (eps / 100) * x ^ (2 + 8 * eps) :=
        mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hx0.le _)
      _ = x ^ (2 + 8 * eps + eps / 100) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring

/-- The same dyadic host is uniformly polynomial in the source scale. -/
theorem nativePageN_host_size_eventually
    (eps : ℝ) (he52 : eps < 1 / 52) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ e : ℕ,
      UpperTheory.Top.PageN eps x e →
        (Fintype.card (AlpogeNativeDyadicH e) : ℝ) ≤ x ^ (3 : ℝ) := by
  have hg := (tendsto_rpow_atTop (by linarith : 0 < 1 - 8 * eps)).eventually_ge_atTop 2
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (hg.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨x₀, fun x hx e hP => ?_⟩
  obtain ⟨hmargin, hx1⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  rw [alpogeNativeDyadicH_card, Nat.cast_pow, Nat.cast_ofNat]
  calc
    (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * eps) := hP.2
    _ ≤ x ^ (1 - 8 * eps) * x ^ (2 + 8 * eps) :=
      mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hx0.le _)
    _ = x ^ (3 : ℝ) := by rw [← Real.rpow_add hx0]; congr 1; ring

/-- The conductor bound is derived from the SAME selected prime pair and
dyadic exponent. It is uniform over all `1 ≤ Y ≤ x`, as the source needs. -/
theorem nativePageN_conductor_eventually
    (eps : ℝ) (he : 0 < eps) (he52 : eps < 1 / 52) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (Y : ℝ) (q d e : ℕ),
      1 ≤ Y → Y ≤ x → UpperTheory.Top.WinPair eps Y q d →
      UpperTheory.Top.PageN eps x e →
        Real.log (alpogeNativeHostN e q d : ℝ) ≤
          2 * x ^ (eps / 5) * Real.log x ^ 2 := by
  have hr : 0 < eps / 5 := by positivity
  have hs := (isLittleO_log_rpow_atTop hr).bound (by norm_num : (0 : ℝ) < 1 / 6)
  have hg := (tendsto_rpow_atTop hr).eventually_ge_atTop (6 * Real.log 2)
  have hl := Real.tendsto_log_atTop.eventually_ge_atTop 2
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1
    (((hs.and hg).and hl).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨x₀, fun x hx Y q d e hY1 hYx hpair hP => ?_⟩
  obtain ⟨⟨⟨hsmall, hlarge⟩, hloglarge⟩, hx1⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hY0 : 0 < Y := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hX : 0 < x ^ (eps / 5) := Real.rpow_pos_of_pos hx0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hlogx, abs_of_pos hX] at hsmall
  have hsmall' : 3 * Real.log 2 + 3 * Real.log x ≤ x ^ (eps / 5) := by
    linarith
  have hE : (e : ℝ) * Real.log 2 ≤
      Real.log 2 + (2 + 8 * eps) * Real.log x := by
    have h := Real.log_le_log (by positivity) hP.2
    rw [Real.log_pow, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 _).ne',
      Real.log_rpow hx0] at h
    exact h
  have hcoef : (2 + 8 * eps) * Real.log x ≤ 3 * Real.log x :=
    mul_le_mul_of_nonneg_right (by linarith) hlogx
  have hdyadic : ((e : ℝ) + 2) * Real.log 2 ≤ x ^ (eps / 5) := by
    linarith
  have hYpow : Y ^ (eps / 5) ≤ x ^ (eps / 5) :=
    Real.rpow_le_rpow hY0.le hYx hr.le
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY1
  have hlogYx : Real.log Y ≤ Real.log x := Real.log_le_log hY0 hYx
  have hsq : Real.log Y ^ 2 ≤ Real.log x ^ 2 := by nlinarith
  have hq : Real.log q ≤ x ^ (eps / 5) := hpair.q_up.trans hYpow
  have hd : Real.log d ≤ x ^ (eps / 5) * Real.log x ^ 2 :=
    hpair.d_up.trans (mul_le_mul hYpow hsq (sq_nonneg _) hX.le)
  have hroom : 2 * x ^ (eps / 5) ≤ x ^ (eps / 5) * Real.log x ^ 2 := by
    have hsq2 : (2 : ℝ) ≤ Real.log x ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq2 hX.le]
  rw [alpogeNativeHostN_log e q d hpair.q_prime.pos hpair.d_prime.pos]
  linarith

/-- Construct the arithmetic host at every scale, together with its source
`SizeN`, polynomial and actual-conductor windows. The prime pair is not
reselected when passing from its character window to its conductor bound. -/
theorem nativeDyadicHost_windows
    (eps : ℝ) (he : 0 < eps) (he52 : eps < 1 / 52) :
    ∃ exponent : ℝ → ℕ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      UpperTheory.Top.PageN eps x (exponent x) ∧
      x ^ (2 + 8 * eps - eps / 100) ≤
          (Fintype.card (AlpogeNativeDyadicH (exponent x)) : ℝ) ∧
      (Fintype.card (AlpogeNativeDyadicH (exponent x)) : ℝ) ≤
          x ^ (2 + 8 * eps + eps / 100) ∧
      (Fintype.card (AlpogeNativeDyadicH (exponent x)) : ℝ) ≤ x ^ (3 : ℝ) ∧
      ∀ (Y : ℝ) (q d : ℕ), 1 ≤ Y → Y ≤ x →
        UpperTheory.Top.WinPair eps Y q d →
        Real.log (alpogeNativeHostN (exponent x) q d : ℝ) ≤
          2 * x ^ (eps / 5) * Real.log x ^ 2 := by
  obtain ⟨exponent, hpage⟩ := UpperTheory.Top.exists_pageN eps he
  obtain ⟨xS, hS⟩ := nativePageN_sizeN_eventually eps he
  obtain ⟨xN, hN⟩ := nativePageN_host_size_eventually eps he52
  obtain ⟨xL, hL⟩ := nativePageN_conductor_eventually eps he he52
  refine ⟨exponent, max (max xS xN) (max xL 1), fun x hx => ?_⟩
  have hxS : xS ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxN : xN ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxL : xL ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hP := hpage x hx1
  have hsize := hS x hxS (exponent x) hP
  exact ⟨hP, hsize.1, hsize.2, hN x hxN (exponent x) hP,
    fun Y q d hY1 hYx hp => hL x hxL Y q d (exponent x) hY1 hYx hp hP⟩

end RHLean.Analysis.AlpogeThin

end
