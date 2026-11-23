import RHLean.Analysis.AlpogeNativeWindowLandau
import RHLean.Analysis.AlpogeSignedSquareInterpolation

/-!
# Native real interpolation of the complete Alpoge Gz source

On a closed unit cell `[n,n+1]`, the complete prime-power arithmetic
source is affine: the new von Mangoldt term cancels at the right endpoint.
Consequently the real Gz equals the chord of its two native integer values
plus the deterministic logarithmic chord defect. We retain that exact
signed identity before estimating the defect by `1/n` for `n >= 1`.

The existing finite Mertens bounds then give a uniform two-sided error
between real Gz and its integer floor value. An explicitly assumed
integer square-root bound therefore transfers to all real arguments.
No square-root bound is established here. The one-sided square-clock
criterion at `R^2-1` remains the weaker sufficient target supplied by
`AlpogeNativeWindowLandau`.
-/

noncomputable section

namespace RHLean.Analysis

/-- The affine chord of the two native integer endpoint values. -/
def alpogeNativeUnitCellChord (n : ℕ) (x : ℝ) : ℝ :=
  (1 - (x - (n : ℝ))) * nativeAlpogeGz n +
    (x - (n : ℝ)) * nativeAlpogeGz (n + 1)

/-- The deterministic logarithmic defect on a real unit cell. -/
def alpogeNativeUnitCellLogDefect (n : ℕ) (x : ℝ) : ℝ :=
  (1 - (x - (n : ℝ))) * ((n : ℝ) * Real.log (n : ℝ)) +
    (x - (n : ℝ)) *
      (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) -
    x * Real.log x

/-- The full prime-power source is affine even at the right endpoint:
the new endpoint term has coefficient zero. -/
theorem alpogeNativeGzArithmetic_unitCell_source
    (n : ℕ) (x : ℝ) (hlo : (n : ℝ) ≤ x)
    (hhi : x ≤ (n : ℝ) + 1) :
    x * nativeLambdaRecip ⌊x⌋₊ - nativePsi ⌊x⌋₊ =
      x * nativeLambdaRecip n - nativePsi n := by
  by_cases hx : x = ((n + 1 : ℕ) : ℝ)
  · rw [hx, Nat.floor_natCast]
    exact nativeAlpogeGz_primePowerEndpoint_cancel n
  · have hxne : x ≠ (n : ℝ) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hx
    have hxlt : x < (n : ℝ) + 1 := lt_of_le_of_ne hhi hxne
    have hfloor : ⌊x⌋₊ = n :=
      (Nat.floor_eq_iff ((Nat.cast_nonneg n).trans hlo)).mpr ⟨hlo, hxlt⟩
    rw [hfloor]

/-- Exact real interpolation of the original complete signed source.
On a unit cell the arithmetic chord defect vanishes identically. -/
theorem alpogeNativeGzArithmetic_unitCell_eq
    (n : ℕ) (x : ℝ) (hlo : (n : ℝ) ≤ x)
    (hhi : x ≤ (n : ℝ) + 1) :
    alpogeNativeGzArithmetic x =
      alpogeNativeUnitCellChord n x + alpogeNativeUnitCellLogDefect n x := by
  have hsource := alpogeNativeGzArithmetic_unitCell_source n x hlo hhi
  have hnext := nativeAlpogeGz_primePowerEndpoint_cancel n
  unfold alpogeNativeGzArithmetic alpogeNativeUnitCellChord
    alpogeNativeUnitCellLogDefect nativeAlpogeGz
  push_cast at hnext ⊢
  linear_combination hsource - (x - (n : ℝ)) * hnext

/-- Convexity of `x log x` gives the sign of the deterministic defect. -/
theorem alpogeNativeUnitCellLogDefect_nonneg
    (n : ℕ) (x : ℝ) (hlo : (n : ℝ) ≤ x)
    (hhi : x ≤ (n : ℝ) + 1) :
    0 ≤ alpogeNativeUnitCellLogDefect n x := by
  have hweight : 0 ≤ 1 - (x - (n : ℝ)) := by linarith
  have hnmem : (n : ℝ) ∈ Set.Ici (0 : ℝ) := by
    simpa only [Set.mem_Ici] using (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
  have hnnextmem : (n : ℝ) + 1 ∈ Set.Ici (0 : ℝ) := by
    simp only [Set.mem_Ici]
    positivity
  have hconvex := Real.convexOn_mul_log.2
    (x := (n : ℝ)) (y := (n : ℝ) + 1)
    (a := 1 - (x - (n : ℝ))) (b := x - (n : ℝ))
    hnmem hnnextmem hweight (sub_nonneg.mpr hlo)
    (show (1 - (x - (n : ℝ))) + (x - (n : ℝ)) = 1 by ring)
  simp only [smul_eq_mul] at hconvex
  have hcoordinate :
      (1 - (x - (n : ℝ))) * (n : ℝ) +
        (x - (n : ℝ)) * ((n : ℝ) + 1) = x := by ring
  rw [hcoordinate] at hconvex
  exact sub_nonneg.mpr hconvex

/-- A sufficient, non-sharp curvature bound; no derivative estimate or
arithmetic error term is inserted into the exact source identity. -/
theorem alpogeNativeUnitCellLogDefect_le_inv
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hlo : (n : ℝ) ≤ x)
    (hhi : x ≤ (n : ℝ) + 1) :
    alpogeNativeUnitCellLogDefect n x ≤ 1 / (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hxpos : 0 < x := hnpos.trans_le hlo
  have hnnext : 0 < (n : ℝ) + 1 := by linarith
  have hlogRight := Real.log_le_sub_one_of_pos (div_pos hnnext hnpos)
  rw [Real.log_div hnnext.ne' hnpos.ne'] at hlogRight
  have hright := mul_le_mul_of_nonneg_left hlogRight hnnext.le
  have hrightId :
      ((n : ℝ) + 1) * (((n : ℝ) + 1) / (n : ℝ) - 1) =
        ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp [hnpos.ne']
    ring
  rw [hrightId] at hright
  have hrightWeighted :=
    mul_le_mul_of_nonneg_left hright (sub_nonneg.mpr hlo)
  have hlogLeft := Real.log_le_sub_one_of_pos (div_pos hnpos hxpos)
  rw [Real.log_div hnpos.ne' hxpos.ne'] at hlogLeft
  have hleft := mul_le_mul_of_nonneg_left hlogLeft hxpos.le
  have hleftId : x * ((n : ℝ) / x - 1) = (n : ℝ) - x := by
    field_simp [hxpos.ne']
  rw [hleftId] at hleft
  have hratio :
      (x - (n : ℝ)) * (((n : ℝ) + 1) / (n : ℝ)) - (x - (n : ℝ)) =
        (x - (n : ℝ)) / (n : ℝ) := by
    field_simp [hnpos.ne']
    ring
  have hdefect :
      alpogeNativeUnitCellLogDefect n x ≤ (x - (n : ℝ)) / (n : ℝ) := by
    unfold alpogeNativeUnitCellLogDefect
    nlinarith only [hrightWeighted, hleft, hratio]
  exact hdefect.trans
    (div_le_div_of_nonneg_right (by linarith : x - (n : ℝ) ≤ 1) hnpos.le)

/-- The real value lies above its integer chord, with an explicit
vanishing `1/n` defect on the closed unit cell. -/
theorem alpogeNativeGzArithmetic_unitCell_bounds
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hlo : (n : ℝ) ≤ x)
    (hhi : x ≤ (n : ℝ) + 1) :
    alpogeNativeUnitCellChord n x ≤ alpogeNativeGzArithmetic x ∧
      alpogeNativeGzArithmetic x ≤ alpogeNativeUnitCellChord n x + 1 / (n : ℝ) := by
  rw [alpogeNativeGzArithmetic_unitCell_eq n x hlo hhi]
  constructor
  · linarith only [alpogeNativeUnitCellLogDefect_nonneg n x hlo hhi]
  · linarith only [alpogeNativeUnitCellLogDefect_le_inv n hn x hlo hhi]

/-- The real/integer floor error is uniformly bounded using the already
proved two-sided finite-Mertens step bound for the complete native Gz. -/
theorem alpogeNativeGzArithmetic_sub_floor_abs_le
    (x : ℝ) (hx : 1 ≤ x) :
    |alpogeNativeGzArithmetic x - nativeAlpogeGz ⌊x⌋₊| ≤
      alpogeGzInterpolationSlope + 1 := by
  let n := ⌊x⌋₊
  have hx0 : 0 ≤ x := by linarith
  have hn : 1 ≤ n := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hlo : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hhi : x ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have ht0 : 0 ≤ x - (n : ℝ) := sub_nonneg.mpr hlo
  have ht1 : x - (n : ℝ) ≤ 1 := by linarith
  have hdefect0 := alpogeNativeUnitCellLogDefect_nonneg n x hlo hhi
  have hdefect1 : alpogeNativeUnitCellLogDefect n x ≤ 1 := by
    have hinv : 1 / (n : ℝ) ≤ 1 := (div_le_iff₀ hnpos).mpr (by simpa using hnR)
    exact (alpogeNativeUnitCellLogDefect_le_inv n hn x hlo hhi).trans hinv
  have hstep := nativeAlpogeGz_succ_abs_le n hn
  have hrewrite :
      alpogeNativeGzArithmetic x - nativeAlpogeGz n =
        (x - (n : ℝ)) * (nativeAlpogeGz (n + 1) - nativeAlpogeGz n) +
          alpogeNativeUnitCellLogDefect n x := by
    rw [alpogeNativeGzArithmetic_unitCell_eq n x hlo hhi]
    unfold alpogeNativeUnitCellChord
    ring
  change |alpogeNativeGzArithmetic x - nativeAlpogeGz n| ≤ _
  rw [hrewrite]
  calc
    |(x - (n : ℝ)) * (nativeAlpogeGz (n + 1) - nativeAlpogeGz n) +
        alpogeNativeUnitCellLogDefect n x| ≤
      |(x - (n : ℝ)) * (nativeAlpogeGz (n + 1) - nativeAlpogeGz n)| +
        |alpogeNativeUnitCellLogDefect n x| := abs_add_le _ _
    _ = (x - (n : ℝ)) * |nativeAlpogeGz (n + 1) - nativeAlpogeGz n| +
        alpogeNativeUnitCellLogDefect n x := by
      rw [abs_mul, abs_of_nonneg ht0, abs_of_nonneg hdefect0]
    _ ≤ (x - (n : ℝ)) * alpogeGzInterpolationSlope + 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hstep ht0) hdefect1
    _ ≤ alpogeGzInterpolationSlope + 1 := by
      have hweight := mul_le_mul_of_nonneg_right ht1 alpogeGzInterpolationSlope_nonneg
      linarith only [hweight]

/-- An optional absolute integer bound transfers to the real source
with the same initial threshold. The bound remains an explicit input. -/
theorem alpogeNativeGzArithmetic_abs_le_of_integer_sqrt_bound_from
    (N₀ : ℕ) (hN₀ : 1 ≤ N₀) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, N₀ ≤ N → |nativeAlpogeGz N| ≤ C * Real.sqrt (N : ℝ))
    (x : ℝ) (hx : (N₀ : ℝ) ≤ x) :
    |alpogeNativeGzArithmetic x| ≤
      (C + alpogeGzInterpolationSlope + 1) * Real.sqrt x := by
  let n := ⌊x⌋₊
  have hN₀R : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
  have hx1 : 1 ≤ x := hN₀R.trans hx
  have hx0 : 0 ≤ x := by linarith
  have hn : N₀ ≤ n := (Nat.le_floor_iff hx0).mpr hx
  have hlo : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hfloor := alpogeNativeGzArithmetic_sub_floor_abs_le x hx1
  have hroot := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlo) hC
  have hsqrt1 : 1 ≤ Real.sqrt x := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx1
  have hconstant := mul_le_mul_of_nonneg_left hsqrt1
    (add_nonneg alpogeGzInterpolationSlope_nonneg (by norm_num : (0 : ℝ) ≤ 1))
  calc
    |alpogeNativeGzArithmetic x| =
        |(alpogeNativeGzArithmetic x - nativeAlpogeGz n) + nativeAlpogeGz n| := by
      congr 1
      ring
    _ ≤ |alpogeNativeGzArithmetic x - nativeAlpogeGz n| + |nativeAlpogeGz n| :=
      abs_add_le _ _
    _ ≤ (alpogeGzInterpolationSlope + 1) + C * Real.sqrt (n : ℝ) :=
      add_le_add hfloor (hbound n hn)
    _ ≤ (C + alpogeGzInterpolationSlope + 1) * Real.sqrt x := by
      nlinarith only [hroot, hconstant]

/-- The special case with the natural threshold `1`. -/
theorem alpogeNativeGzArithmetic_abs_le_of_integer_sqrt_bound
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 1 ≤ N → |nativeAlpogeGz N| ≤ C * Real.sqrt (N : ℝ))
    (x : ℝ) (hx : 1 ≤ x) :
    |alpogeNativeGzArithmetic x| ≤
      (C + alpogeGzInterpolationSlope + 1) * Real.sqrt x := by
  exact alpogeNativeGzArithmetic_abs_le_of_integer_sqrt_bound_from
    1 (by norm_num) C hC hbound x (by simpa using hx)

/-- The existing absolute square-lattice comparison extends to every real
argument `x >= 4`. This optional comparison at `R^2` does not replace the
one-sided sufficient square-clock criterion at `R^2-1`. -/
theorem alpogeNativeGzArithmetic_abs_le_of_square_lattice_bound
    (C : ℝ) (hC : 0 ≤ C)
    (hSquare : ∀ R : ℕ, 2 ≤ R → |nativeAlpogeGz (R ^ 2)| ≤ C * (R : ℝ))
    (x : ℝ) (hx : 4 ≤ x) :
    |alpogeNativeGzArithmetic x| ≤
      (2 * C + 4 * alpogeGzInterpolationSlope + 1) * Real.sqrt x := by
  have hconstant : 0 ≤ 2 * C + 3 * alpogeGzInterpolationSlope := by
    nlinarith [alpogeGzInterpolationSlope_nonneg]
  have h := alpogeNativeGzArithmetic_abs_le_of_integer_sqrt_bound_from
    4 (by norm_num) (2 * C + 3 * alpogeGzInterpolationSlope) hconstant
    (fun N hN => nativeAlpogeGz_all_of_square_lattice_critical C hC hSquare N hN)
    x (by simpa using hx)
  calc
    |alpogeNativeGzArithmetic x| ≤
        ((2 * C + 3 * alpogeGzInterpolationSlope) + alpogeGzInterpolationSlope + 1) *
          Real.sqrt x := h
    _ = (2 * C + 4 * alpogeGzInterpolationSlope + 1) * Real.sqrt x := by ring

end RHLean.Analysis
