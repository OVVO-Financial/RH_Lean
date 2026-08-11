import Mathlib
import RHLean.Analysis.NativePNTChebyshev

/-!
# Elementary `psi`/`theta` transfer

The Selberg--Erdos endgame runs on the prime-power mass `psi`.  The prime
number theorem is a statement about the prime mass `theta`, and then about the
prime counting function.  This module supplies the elementary bridge, using
only the square-root confinement of repeated prime powers already proved in
`RHLean.Analysis.NativePNTChebyshev`.

Nothing here assumes or produces an asymptotic for either function.  The
content is exactly that their difference is `o(N)`, so one normalized limit
exists precisely when the other does.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace RHLean.Analysis

/-- Every prime at most `N` carries multiplicity at least one in `psi`, so the
prime layer never exceeds the prime-power layer. -/
theorem nativeTheta_le_psi (N : ℕ) : nativeTheta N ≤ nativePsi N := by
  rw [nativePsi_eq_sum_mul_log_prime]
  unfold nativeTheta
  apply Finset.sum_le_sum
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpPrime⟩
  have hpN : p ≤ N := (Finset.mem_Icc.mp hpIcc).2
  have hlogpos : 0 < p.log N := Nat.log_pos hpPrime.one_lt hpN
  have hone : (1 : ℝ) ≤ ((p.log N : ℕ) : ℝ) := by exact_mod_cast hlogpos
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
  have hmul := mul_le_mul_of_nonneg_right hone hlogp
  linarith

/-- `log x / sqrt x -> 0`, the only limit input needed by the transfer. -/
theorem nativeLog_div_sqrt_atTop :
    Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  have h := Real.isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)
  have htend := h.tendsto_div_nhds_zero
  simpa only [← Real.sqrt_eq_rpow] using htend

/-- The same limit read along the natural numbers. -/
theorem nativeLog_div_sqrt_natCast_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / Real.sqrt (N : ℝ)) atTop (𝓝 0) :=
  nativeLog_div_sqrt_atTop.comp tendsto_natCast_atTop_atTop

/-- **The prime-power correction is `o(N)`.**  All repeated prime powers live
below the square-root cutoff, so `psi - theta` is at most `sqrt N log N`. -/
theorem nativePsi_sub_theta_div_atTop :
    Tendsto (fun N : ℕ => (nativePsi N - nativeTheta N) / (N : ℝ))
      atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ nativeLog_div_sqrt_natCast_atTop
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact div_nonneg (sub_nonneg.mpr (nativeTheta_le_psi N)) hNpos.le
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hbound := nativePsi_le_theta_add_sqrt_log N hN
    have hlogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    have hsqrtpos : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
    have hsplit : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt hNpos.le
    have hsqrtNat : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have hsqrtNatSq : (Nat.sqrt N) ^ 2 ≤ N := Nat.sqrt_le' N
      have hsq : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) := by
        exact_mod_cast hsqrtNatSq
      have hrealSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := by
        rw [Real.sq_sqrt]
        positivity
      have hleft : 0 ≤ ((Nat.sqrt N : ℕ) : ℝ) := by positivity
      have hright : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have h1 : nativePsi N - nativeTheta N ≤
        ((Nat.sqrt N : ℕ) : ℝ) * Real.log (N : ℝ) := by linarith
    have h2 : ((Nat.sqrt N : ℕ) : ℝ) * Real.log (N : ℝ) ≤
        Real.sqrt (N : ℝ) * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right hsqrtNat hlogN
    have h3 : nativePsi N - nativeTheta N ≤
        Real.sqrt (N : ℝ) * Real.log (N : ℝ) := h1.trans h2
    rw [div_le_div_iff hNpos hsqrtpos]
    calc (nativePsi N - nativeTheta N) * Real.sqrt (N : ℝ)
        ≤ (Real.sqrt (N : ℝ) * Real.log (N : ℝ)) * Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_right h3 hsqrtpos.le
      _ = Real.log (N : ℝ) * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by ring
      _ = Real.log (N : ℝ) * (N : ℝ) := by rw [hsplit]

/-- **`theta ~ N` if and only if `psi ~ N`.**  The endgame may therefore be run
on whichever of the two masses is more convenient. -/
theorem nativeTheta_div_atTop_one_iff :
    Tendsto (fun N : ℕ => nativeTheta N / (N : ℝ)) atTop (𝓝 1) ↔
      Tendsto (fun N : ℕ => nativePsi N / (N : ℝ)) atTop (𝓝 1) := by
  have hfwd : ∀ N : ℕ,
      nativeTheta N / (N : ℝ) + (nativePsi N - nativeTheta N) / (N : ℝ) =
        nativePsi N / (N : ℝ) := by
    intro N
    rw [div_add_div_same]
    congr 1
    ring
  have hback : ∀ N : ℕ,
      nativePsi N / (N : ℝ) - (nativePsi N - nativeTheta N) / (N : ℝ) =
        nativeTheta N / (N : ℝ) := by
    intro N
    rw [div_sub_div_same]
    congr 1
    ring
  constructor
  · intro h
    have hsum := h.add nativePsi_sub_theta_div_atTop
    rw [add_zero] at hsum
    simpa only [hfwd] using hsum
  · intro h
    have hdiff := h.sub nativePsi_sub_theta_div_atTop
    rw [sub_zero] at hdiff
    simpa only [hback] using hdiff

end RHLean.Analysis
