import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib

/-!
# Finite-scale amplitude coordinates and reflection

For x > 1 and A > 0, the coordinate is log(A)/log(x), with inverse x^s.
This is an exact finite-scale change of coordinates, not a claim that the
coordinate of a sample is the real part of a zeta zero. The checked Option
interface explicitly rejects a zero amplitude and bases at or below one.
-/

noncomputable section
namespace RHLean.Analysis.MertensAmplitude
open Set

/-- Algebraic coordinate; its amplitude interpretation requires x > 1 and A > 0. -/
def amplitudeCoordinate (x A : ℝ) : ℝ := Real.log A / Real.log x

/-- Domain-checked coordinate. In particular, zero amplitude has no coordinate. -/
def amplitudeCoordinate? (x A : ℝ) : Option ℝ :=
  if 1 < x ∧ 0 < A then some (amplitudeCoordinate x A) else none

/-- Reflection in amplitude space, corresponding to s |-> 1-s. -/
def reflectedAmplitude (x A : ℝ) : ℝ := x / A

/-- The positive amplitude interval corresponding to [l,u]. -/
def amplitudeBand (x l u : ℝ) : Set ℝ := Set.Icc (x ^ l) (x ^ u)

theorem amplitudeCoordinate_eq_logb (x A : ℝ) :
    amplitudeCoordinate x A = Real.logb x A := rfl

theorem checkedCoordinate_some {x A : ℝ} (hx : 1 < x) (hA : 0 < A) :
    amplitudeCoordinate? x A = some (amplitudeCoordinate x A) := by
  simp only [amplitudeCoordinate?, ite_eq_left (And.intro hx hA)]

theorem checkedCoordinate_zero (x : ℝ) : amplitudeCoordinate? x 0 = none := by
  simp [amplitudeCoordinate?]

theorem checkedCoordinate_invalid_base {x A : ℝ} (hx : x ≤ 1) :
    amplitudeCoordinate? x A = none := by
  simp [amplitudeCoordinate?, not_lt.mpr hx]

/-- Powers become horizontal coordinates, for every real exponent. -/
theorem coordinate_rpow {x : ℝ} (hx : 1 < x) (s : ℝ) :
    amplitudeCoordinate x (x ^ s) = s :=
  Real.logb_rpow (zero_lt_one.trans hx) (ne_of_gt hx)

/-- Recover the actual positive amplitude exactly. -/
theorem rpow_coordinate {x A : ℝ} (hx : 1 < x) (hA : 0 < A) :
    x ^ amplitudeCoordinate x A = A :=
  Real.rpow_logb (zero_lt_one.trans hx) (ne_of_gt hx) hA

theorem coordinate_one (x : ℝ) : amplitudeCoordinate x 1 = 0 := by
  simp [amplitudeCoordinate]

theorem coordinate_self {x : ℝ} (hx : 1 < x) : amplitudeCoordinate x x = 1 :=
  Real.logb_self_eq_one hx

theorem coordinate_sqrt {x : ℝ} (hx : 1 < x) :
    amplitudeCoordinate x (Real.sqrt x) = (1 : ℝ) / 2 := by
  rw [Real.sqrt_eq_rpow]
  exact coordinate_rpow hx _

theorem coordinate_le_iff {x A s : ℝ} (hx : 1 < x) (hA : 0 < A) :
    amplitudeCoordinate x A ≤ s ↔ A ≤ x ^ s :=
  Real.logb_le_iff_le_rpow hx hA

theorem coordinate_lt_iff {x A s : ℝ} (hx : 1 < x) (hA : 0 < A) :
    amplitudeCoordinate x A < s ↔ A < x ^ s :=
  Real.logb_lt_iff_lt_rpow hx hA

theorem le_coordinate_iff {x A s : ℝ} (hx : 1 < x) (hA : 0 < A) :
    s ≤ amplitudeCoordinate x A ↔ x ^ s ≤ A :=
  Real.le_logb_iff_rpow_le hx hA

theorem lt_coordinate_iff {x A s : ℝ} (hx : 1 < x) (hA : 0 < A) :
    s < amplitudeCoordinate x A ↔ x ^ s < A :=
  Real.lt_logb_iff_rpow_lt hx hA

/-- Exact amplitude-band to horizontal-interval equivalence. -/
theorem coordinate_mem_Icc_iff {x A l u : ℝ} (hx : 1 < x) (hA : 0 < A) :
    amplitudeCoordinate x A ∈ Set.Icc l u ↔ A ∈ amplitudeBand x l u :=
  and_congr (le_coordinate_iff hx hA) (coordinate_le_iff hx hA)

/-- The entire amplitude band maps onto the entire interval, not just into it. -/
theorem image_amplitudeBand {x : ℝ} (hx : 1 < x) (l u : ℝ) :
    amplitudeCoordinate x '' amplitudeBand x l u = Set.Icc l u := by
  ext s
  constructor
  · rintro ⟨A, hA, rfl⟩
    have hApos : 0 < A :=
      (Real.rpow_pos_of_pos (zero_lt_one.trans hx) l).trans_le hA.1
    exact (coordinate_mem_Icc_iff hx hApos).mpr hA
  · intro hs
    refine ⟨x ^ s, ?_, coordinate_rpow hx s⟩
    apply (coordinate_mem_Icc_iff hx (Real.rpow_pos_of_pos (zero_lt_one.trans hx) s)).mp
    rwa [coordinate_rpow hx s]

/-- The unit-to-linear amplitude interval maps exactly to the critical-strip coordinates. -/
theorem coordinate_mem_unit_iff {x A : ℝ} (hx : 1 < x) (hA : 0 < A) :
    amplitudeCoordinate x A ∈ Set.Icc (0 : ℝ) 1 ↔ 1 ≤ A ∧ A ≤ x := by
  simpa only [amplitudeBand, Set.mem_Icc, Real.rpow_zero, Real.rpow_one] using!
    (coordinate_mem_Icc_iff (l := 0) (u := 1) hx hA)

theorem reflectedAmplitude_pos {x A : ℝ} (hx : 0 < x) (hA : 0 < A) :
    0 < reflectedAmplitude x A := div_pos hx hA

/-- Reflection of the coordinate is exactly division of x by the amplitude. -/
theorem coordinate_reflection {x A : ℝ} (hx : 1 < x) (hA : 0 < A) :
    amplitudeCoordinate x (reflectedAmplitude x A) = 1 - amplitudeCoordinate x A := by
  change Real.logb x (x / A) = 1 - Real.logb x A
  rw [Real.logb_div (zero_lt_one.trans hx).ne' hA.ne', Real.logb_self_eq_one hx]

theorem amplitude_mul_reflection {x A : ℝ} (hA : 0 < A) :
    A * reflectedAmplitude x A = x := by
  change A * (x / A) = x
  calc
    A * (x / A) = x * (A / A) := by ring
    _ = x := by rw [div_self hA.ne', mul_one]

theorem reflection_involutive {x A : ℝ} (hx : 0 < x) (hA : 0 < A) :
    reflectedAmplitude x (reflectedAmplitude x A) = A := by
  change x / (x / A) = A
  exact (div_eq_iff (div_ne_zero hx.ne' hA.ne')).mpr
    (amplitude_mul_reflection (x := x) hA).symm

theorem reflection_rpow {x : ℝ} (hx : 0 < x) (s : ℝ) :
    reflectedAmplitude x (x ^ s) = x ^ (1 - s) := by
  unfold reflectedAmplitude
  rw [Real.rpow_sub hx, Real.rpow_one]

/-- The only positive amplitude fixed by reflection is sqrt(x). -/
theorem reflection_fixed_iff {x A : ℝ} (hx : 1 < x) (hA : 0 < A) :
    reflectedAmplitude x A = A ↔ A = Real.sqrt x := by
  constructor
  · intro h
    have hc := coordinate_reflection hx hA
    rw [h] at hc
    have hh : amplitudeCoordinate x A = (1 : ℝ) / 2 := by linarith
    calc
      A = x ^ amplitudeCoordinate x A := (rpow_coordinate hx hA).symm
      _ = Real.sqrt x := by rw [hh, Real.sqrt_eq_rpow]
  · rintro rfl
    rw [Real.sqrt_eq_rpow, reflection_rpow (zero_lt_one.trans hx)]
    congr 1
    norm_num

/-- Any symmetric amplitude band is invariant under amplitude reflection. -/
theorem reflection_mem_symmetricBand_iff {x A a : ℝ} (hx : 1 < x) (hA : 0 < A) :
    reflectedAmplitude x A ∈ amplitudeBand x (1 - a) a ↔
      A ∈ amplitudeBand x (1 - a) a := by
  rw [← coordinate_mem_Icc_iff hx (reflectedAmplitude_pos (zero_lt_one.trans hx) hA),
    ← coordinate_mem_Icc_iff hx hA, coordinate_reflection hx hA]
  simp only [Set.mem_Icc]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith

/-- The symmetric band is centered at coordinate one half. -/
theorem symmetricBand_iff_centered {x A a : ℝ} (hx : 1 < x) (hA : 0 < A) :
    A ∈ amplitudeBand x (1 - a) a ↔
      |amplitudeCoordinate x A - (1 : ℝ) / 2| ≤ a - (1 : ℝ) / 2 := by
  rw [← coordinate_mem_Icc_iff hx hA, abs_le]
  simp only [Set.mem_Icc]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith

/-- Crossing a lower amplitude curve is equivalent to the reflected coordinate
moving below the complementary upper wall, at this same finite scale. -/
theorem crossing_iff_reflected_coordinate {x A a : ℝ} (hx : 1 < x) (hA : 0 < A) :
    x ^ a < A ↔ amplitudeCoordinate x (reflectedAmplitude x A) < 1 - a := by
  rw [coordinate_reflection hx hA, ← lt_coordinate_iff hx hA]
  constructor <;> intro h <;> linarith

/-- A multiplicative envelope constant is a finite horizontal correction. -/
theorem coordinate_scaled_power {x C a : ℝ} (hx : 1 < x) (hC : 0 < C) :
    amplitudeCoordinate x (C * x ^ a) = a + Real.log C / Real.log x := by
  change Real.logb x (C * x ^ a) = a + Real.logb x C
  rw [Real.logb_mul hC.ne' (Real.rpow_pos_of_pos (zero_lt_one.trans hx) a).ne',
    Real.logb_rpow (zero_lt_one.trans hx) (ne_of_gt hx), add_comm]

/-- Exact special case requested by the user, with no claim of universal
membership of actual Mertens samples in this band. -/
theorem eighths_band_iff {x A : ℝ} (hx : 1 < x) (hA : 0 < A) :
    (x ^ ((1 : ℝ) / 8) ≤ A ∧ A ≤ x ^ ((7 : ℝ) / 8)) ↔
      ((1 : ℝ) / 8 ≤ amplitudeCoordinate x A ∧
        amplitudeCoordinate x A ≤ (7 : ℝ) / 8) :=
  (coordinate_mem_Icc_iff hx hA).symm

end RHLean.Analysis.MertensAmplitude
