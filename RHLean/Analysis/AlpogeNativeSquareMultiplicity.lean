import RHLean.Analysis.AlpogeNativeZetaWindowWitness
import RHLean.Analysis.AlpogeThin.NativeDyadicHostWindows

/-!
# Square-clock integer parameters and compatible scalar sizes

At the native endpoint `x = R^2 - 1`, choose the integer multiplicity `m = R`
and the real lattice parameter `k = x * R`.  This file proves, uniformly at
large scales, that these choices satisfy the multiplicity and lattice-size
fields of `AlpogeNativeRestSize` on the already constructed dyadic host.
The dyadic exponent is not reselected: the result applies to every exponent
satisfying the original `PageN` condition.

This is scalar feasibility, not construction of recovered sections or their
geometric gain.  The top/thick sets, their density, the bound on the actual
`aE`, and the physical realization of `k` retain their original meanings and
must still be proved for the same recovery/cost family.  No `top` estimate,
`DIV`, slope bound, or `AlpogeNativeZetaWindowWitness` is constructed here.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Analysis

/-- The size regime itself forces a nontrivial host: `x <= n^2`.  Thus a
fixed small host cannot realize it at arbitrarily large source scales. -/
theorem AlpogeNativeRestSize.source_scale_le_host_sq
    {ε x : ℝ} {n nT nT2 m : ℕ} {b k aE : ℝ}
    (hS : AlpogeNativeRestSize ε x n nT nT2 m b k aE) (hx : 0 < x) :
    x ≤ (n : ℝ) ^ 2 := by
  have hp : 0 < x ^ ((1 : ℝ) / 2 - ε) := Real.rpow_pos_of_pos hx _
  have h : x * x ^ ((1 : ℝ) / 2 - ε) ≤
      (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) :=
    (mul_le_mul_of_nonneg_left hS.mult_lower hx.le).trans
      (hS.k_lower.trans hS.k_upper)
  exact le_of_mul_le_mul_right h hp

/-- The native integer radius is an admissible multiplicity once the
positive exponent slack absorbs a factor of two. -/
theorem alpogeNativeSquareMultiplicity_bounds
    (R : ℕ) (hR : 2 ≤ R) (ε : ℝ) (hε : 0 ≤ ε)
    (hslack : 2 ≤ (((R ^ 2 - 1 : ℕ) : ℝ) ^ (ε / 2))) :
    (((R ^ 2 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2 - ε)) ≤ R ∧
      (R : ℝ) ≤ (((R ^ 2 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2 + ε / 2)) := by
  let x : ℝ := (R ^ 2 - 1 : ℕ)
  have hRr : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hxdef : x = (R : ℝ) ^ 2 - 1 := by
    dsimp [x]
    rw [Nat.cast_sub (by nlinarith : 1 ≤ R ^ 2), Nat.cast_pow, Nat.cast_one]
  have hx3 : 3 ≤ x := by rw [hxdef]; nlinarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hs0 := Real.sqrt_nonneg x
  have hs2 := Real.sq_sqrt hx0.le
  have hsR : Real.sqrt x ≤ R := by nlinarith
  have hRs : (R : ℝ) ≤ 2 * Real.sqrt x := by nlinarith
  have hs : Real.sqrt x = x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x
  constructor
  · change x ^ ((1 : ℝ) / 2 - ε) ≤ R
    calc
      x ^ ((1 : ℝ) / 2 - ε) ≤ x ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ ≤ R := by rw [← hs]; exact hsR
  · change (R : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2)
    calc
      (R : ℝ) ≤ 2 * Real.sqrt x := hRs
      _ ≤ x ^ (ε / 2) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hslack hs0
      _ = x ^ ((1 : ℝ) / 2 + ε / 2) := by
        rw [hs, ← Real.rpow_add hx0]
        congr 1
        ring

/-- Choosing `k = x * m` pays both lattice-size inequalities whenever the
host has at least `x` elements and the stated multiplicity upper bound holds.
This lemma does not identify `k` with a measured lattice invariant. -/
theorem alpogeNativeSquareMultiplicity_lattice_sizes
    {x ε : ℝ} {n m : ℕ} (hx1 : 1 ≤ x) (hε : ε ≤ (2 : ℝ) / 3)
    (hn : x ≤ (n : ℝ))
    (hm : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2)) :
    x * (m : ℝ) ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) := by
  have hx0 : 0 < x := by linarith
  have hnn : x ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  calc
    x * (m : ℝ) ≤ x * x ^ ((1 : ℝ) / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left hm hx0.le
    _ = x ^ (1 + ((1 : ℝ) / 2 + ε / 2)) := by
      simpa only [Real.rpow_one] using
        (Real.rpow_add hx0 (1 : ℝ) ((1 : ℝ) / 2 + ε / 2)).symm
    _ ≤ x ^ (2 + ((1 : ℝ) / 2 - ε)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    _ = x ^ 2 * x ^ ((1 : ℝ) / 2 - ε) := by
      simpa only [Real.rpow_two] using
        Real.rpow_add hx0 (2 : ℝ) ((1 : ℝ) / 2 - ε)
    _ ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) :=
      mul_le_mul_of_nonneg_right hnn (Real.rpow_nonneg hx0.le _)

/-- All eight scalar size fields hold with the explicit integer parameter
`R` and parameter `x*R`, provided the actual top/thick counts and `aE` meet
their original conditions. -/
theorem alpogeNativeRestSize_of_squareClock
    (R : ℕ) (hR : 2 ≤ R) (ε : ℝ) (hε : 0 ≤ ε) (hεup : ε ≤ (2 : ℝ) / 3)
    (n nT nT2 : ℕ) (b aE : ℝ)
    (hb : 0 < b)
    (haE : aE ≤ 2 * ((R ^ 2 - 1 : ℕ) : ℝ) * b)
    (hTop : ((R ^ 2 - 1 : ℕ) : ℝ) ^ (-(ε / 8)) * n / 2 ≤ nT)
    (hThick : ((R ^ 2 - 1 : ℕ) : ℝ) ^ (-ε) ≤ (nT2 : ℝ) / n)
    (hn : ((R ^ 2 - 1 : ℕ) : ℝ) ≤ n)
    (hslack : 2 ≤ ((R ^ 2 - 1 : ℕ) : ℝ) ^ (ε / 2)) :
    AlpogeNativeRestSize ε ((R ^ 2 - 1 : ℕ) : ℝ) n nT nT2 R b
      (((R ^ 2 - 1 : ℕ) : ℝ) * R) aE := by
  obtain ⟨hlo, hup⟩ := alpogeNativeSquareMultiplicity_bounds R hR ε hε hslack
  have hx1 : (1 : ℝ) ≤ ((R ^ 2 - 1 : ℕ) : ℝ) := by
    have hsq : 2 ≤ R ^ 2 := by nlinarith
    exact_mod_cast (show 1 ≤ R ^ 2 - 1 by omega)
  exact ⟨hb, haE, hTop, hThick, hlo, hup, le_rfl,
    alpogeNativeSquareMultiplicity_lattice_sizes hx1 hεup hn hup⟩

/-- The consumer's existing large-scale threshold already absorbs the
rounding factor.  No extra asymptotic threshold is needed to choose `m=R`
and `k=x*R` on its same constructed `PageN` host. -/
theorem alpogeNativeSquareMultiplicity_pageN_of_largeX
    (R : ℕ) (hR : 2 ≤ R) (ε C : ℝ) (hε52 : ε < 1 / 52)
    (hLarge : alpogeNativeLargeX ε C ((R ^ 2 - 1 : ℕ) : ℝ))
    (e : ℕ)
    (hPage : AlpogeThin.UpperTheory.Top.PageN ε ((R ^ 2 - 1 : ℕ) : ℝ) e)
    (nT nT2 : ℕ) (b aE : ℝ)
    (hb : 0 < b) (haE : aE ≤ 2 * ((R ^ 2 - 1 : ℕ) : ℝ) * b)
    (hTop : ((R ^ 2 - 1 : ℕ) : ℝ) ^ (-(ε / 8)) *
        Fintype.card (AlpogeNativeDyadicH e) / 2 ≤ nT)
    (hThick : ((R ^ 2 - 1 : ℕ) : ℝ) ^ (-ε) ≤
        (nT2 : ℝ) / Fintype.card (AlpogeNativeDyadicH e)) :
    AlpogeNativeRestSize ε ((R ^ 2 - 1 : ℕ) : ℝ)
      (Fintype.card (AlpogeNativeDyadicH e)) nT nT2 R b
      (((R ^ 2 - 1 : ℕ) : ℝ) * R) aE := by
  obtain ⟨hε, _hC, hx3, h26, _hmove⟩ := hLarge
  have hx1 : (1 : ℝ) ≤ ((R ^ 2 - 1 : ℕ) : ℝ) := by linarith
  have hn : ((R ^ 2 - 1 : ℕ) : ℝ) ≤
      Fintype.card (AlpogeNativeDyadicH e) := by
    rw [alpogeNativeDyadicH_card, Nat.cast_pow, Nat.cast_ofNat]
    exact (Real.self_le_rpow_of_one_le hx1 (by linarith)).trans hPage.1
  have hslack : (2 : ℝ) ≤ ((R ^ 2 - 1 : ℕ) : ℝ) ^ (ε / 2) :=
    (show (2 : ℝ) ≤ 26 by norm_num).trans
      (h26.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)))
  exact alpogeNativeRestSize_of_squareClock R hR ε hε.le (by linarith)
    _ nT nT2 b aE hb haE hTop hThick hn hslack

/-- The same `PageN` exponent already selected by the native arithmetic
construction supports `m=R` and `k=(R^2-1)*R`.  No host or prime pair is
reselected and the threshold is uniform in both the exponent and radius.

The returned statement accepts the actual top/thick counts and actual
`aE` bound; it supplies the remaining four multiplicity/lattice inequalities. -/
theorem alpogeNativeSquareMultiplicity_pageN_eventually
    (ε : ℝ) (hε : 0 < ε) (hε52 : ε < 1 / 52) :
    ∃ X₀ : ℝ, ∀ R : ℕ, 2 ≤ R → X₀ ≤ ((R ^ 2 - 1 : ℕ) : ℝ) →
      ∀ e : ℕ, AlpogeThin.UpperTheory.Top.PageN ε ((R ^ 2 - 1 : ℕ) : ℝ) e →
      ∀ (nT nT2 : ℕ) (b aE : ℝ),
        0 < b → aE ≤ 2 * ((R ^ 2 - 1 : ℕ) : ℝ) * b →
        ((R ^ 2 - 1 : ℕ) : ℝ) ^ (-(ε / 8)) *
            Fintype.card (AlpogeNativeDyadicH e) / 2 ≤ nT →
        ((R ^ 2 - 1 : ℕ) : ℝ) ^ (-ε) ≤
            (nT2 : ℝ) / Fintype.card (AlpogeNativeDyadicH e) →
        AlpogeNativeRestSize ε ((R ^ 2 - 1 : ℕ) : ℝ)
          (Fintype.card (AlpogeNativeDyadicH e)) nT nT2 R b
          (((R ^ 2 - 1 : ℕ) : ℝ) * R) aE := by
  refine ⟨alpogeNativeLargeXThreshold ε,
    fun R hR hXR e hPage nT nT2 b aE hb haE hTop hThick => ?_⟩
  exact alpogeNativeSquareMultiplicity_pageN_of_largeX R hR ε 0 hε52
    (alpogeNativeLargeX_of_threshold_le hε le_rfl hXR) e hPage
    nT nT2 b aE hb haE hTop hThick

end RHLean.Analysis

end
