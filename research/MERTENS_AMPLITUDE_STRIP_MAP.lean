import «research.MERTENS_AMPLITUDE_COORDINATES»
import «research.MERTENS_CONVERSE_IDENTIFICATION»

/-!
# Actual Mertens amplitudes in horizontal strip coordinates

The finite amplitude is the norm of the existing genuine mertensSummatory.
Its checked coordinate is absent at M(n)=0, or at n<=1. The clipped amplitude
max(1,|M(n)|) is used only for the separately labelled asymptotic interface
already proved in #948 and #949; it is not substituted for a zero sample.
A reflected amplitude n/|M(n)| is an algebraic partner, not another observed
Mertens sum and not a claimed zeta zero.
-/

noncomputable section
namespace RHLean.Analysis.MertensAmplitude
open RHLean.Analysis.MertensExponent
open Filter Set
open scoped ArithmeticFunction.Moebius BigOperators

/-- The actual amplitude, without clipping or a model sequence. -/
def mertensAmplitude (n : ℕ) : ℝ := ‖mertensSummatory n‖

/-- The actual pointwise coordinate, absent at invalid bases and zero amplitudes. -/
def mertensAmplitudeCoordinate (n : ℕ) : Option ℝ :=
  amplitudeCoordinate? (n : ℝ) (mertensAmplitude n)

/-- Discrete signed arithmetic underlying the complex-valued library sum. -/
theorem mertens_eq_integer_sum (n : ℕ) :
    mertensSummatory n = ((∑ k ∈ Finset.Icc 1 n, μ k : ℤ) : ℂ) := by
  rw [← sum_Icc_one_moebius_eq_mertensSummatory]
  simp only [Int.cast_sum]

/-- A nonzero Mertens amplitude is at least one because the sum is integral. -/
theorem one_le_mertensAmplitude {n : ℕ} (hM : mertensSummatory n ≠ 0) :
    1 ≤ mertensAmplitude n := by
  let z : ℤ := ∑ k ∈ Finset.Icc 1 n, μ k
  have hz : mertensSummatory n = (z : ℂ) := mertens_eq_integer_sum n
  have hz0 : z ≠ 0 := by
    intro h
    apply hM
    rw [hz, h, Int.cast_zero]
  have habs : (1 : ℤ) ≤ |z| := by
    have hp : 0 < |z| := abs_pos.mpr hz0
    omega
  unfold mertensAmplitude
  rw [hz, Complex.norm_intCast]
  exact_mod_cast habs

theorem mertensAmplitude_pos {n : ℕ} (hM : mertensSummatory n ≠ 0) :
    0 < mertensAmplitude n := norm_pos_iff.mpr hM

theorem mertensAmplitude_le (n : ℕ) : mertensAmplitude n ≤ (n : ℝ) :=
  mertens_norm_le n

theorem mertensCoordinate_some {n : ℕ} (hn : 2 ≤ n) (hM : mertensSummatory n ≠ 0) :
    mertensAmplitudeCoordinate n = some (amplitudeCoordinate (n : ℝ) (mertensAmplitude n)) := by
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  exact checkedCoordinate_some hnR (mertensAmplitude_pos hM)

theorem mertensCoordinate_none_of_zero {n : ℕ} (hM : mertensSummatory n = 0) :
    mertensAmplitudeCoordinate n = none := by
  simp only [mertensAmplitudeCoordinate, mertensAmplitude, hM, norm_zero, checkedCoordinate_zero]

theorem mertensCoordinate_none_of_small {n : ℕ} (hn : n ≤ 1) :
    mertensAmplitudeCoordinate n = none := by
  apply checkedCoordinate_invalid_base
  exact_mod_cast hn

/-- Every actual nonzero sample lies in the full [0,1] coordinate interval. -/
theorem mertensCoordinate_mem_unit {n : ℕ} (hn : 2 ≤ n) (hM : mertensSummatory n ≠ 0) :
    amplitudeCoordinate (n : ℝ) (mertensAmplitude n) ∈ Set.Icc (0 : ℝ) 1 := by
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  exact (coordinate_mem_unit_iff hnR (mertensAmplitude_pos hM)).mpr
    ⟨one_le_mertensAmplitude hM, mertensAmplitude_le n⟩

/-- Exact finite membership equivalence for the actual, unclipped amplitude. -/
theorem mertens_amplitudeBand_iff {n : ℕ} (hn : 2 ≤ n)
    (hM : mertensSummatory n ≠ 0) (l u : ℝ) :
    mertensAmplitude n ∈ amplitudeBand (n : ℝ) l u ↔
      amplitudeCoordinate (n : ℝ) (mertensAmplitude n) ∈ Set.Icc l u := by
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  exact (coordinate_mem_Icc_iff hnR (mertensAmplitude_pos hM)).symm

/-- The reflected coordinate of an actual nonzero amplitude is exactly 1-s. -/
theorem mertens_coordinate_reflection {n : ℕ} (hn : 2 ≤ n)
    (hM : mertensSummatory n ≠ 0) :
    amplitudeCoordinate (n : ℝ) (reflectedAmplitude (n : ℝ) (mertensAmplitude n)) =
      1 - amplitudeCoordinate (n : ℝ) (mertensAmplitude n) := by
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  exact coordinate_reflection hnR (mertensAmplitude_pos hM)

/-- A genuine lower-cone crossing gives the complementary reflected crossing. -/
theorem mertens_eighth_crossing_iff {n : ℕ} (hn : 2 ≤ n)
    (hM : mertensSummatory n ≠ 0) :
    (n : ℝ) ^ ((1 : ℝ) / 8) < mertensAmplitude n ↔
      amplitudeCoordinate (n : ℝ) (reflectedAmplitude (n : ℝ) (mertensAmplitude n)) <
        (7 : ℝ) / 8 := by
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  simpa only [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num] using!
    (crossing_iff_reflected_coordinate (a := (1 : ℝ) / 8) hnR (mertensAmplitude_pos hM))

/-- Away from M(n)=0, the existing clipped log slope agrees with the actual coordinate. -/
theorem actual_coordinate_eq_logSlope {n : ℕ} (hM : mertensSummatory n ≠ 0) :
    amplitudeCoordinate (n : ℝ) (mertensAmplitude n) = mertensLogSlope n := by
  have hnorm : 1 ≤ ‖mertensSummatory n‖ := one_le_mertensAmplitude hM
  unfold amplitudeCoordinate mertensAmplitude mertensLogSlope
  rw [max_eq_right hnorm]

/-- The clipping used for the asymptotic theorem is displayed explicitly. -/
theorem clipped_coordinate_eq_logSlope (n : ℕ) :
    amplitudeCoordinate (n : ℝ) (max 1 (mertensAmplitude n)) = mertensLogSlope n := rfl

/-- Actual amplitude coordinates connect to the previously proved boundary
identification through the explicitly clipped natural-endpoint limsup. -/
theorem amplitude_limsup_eq_rightmost :
    Filter.limsup (fun n : ℕ => amplitudeCoordinate (n : ℝ) (max 1 (mertensAmplitude n)))
      atTop = zetaRightmostRealPart := logLimsup_eq_rightmost

/-- Exact regression: M(2)=0 must have no actual amplitude coordinate. -/
theorem mertens_two : mertensSummatory 2 = 0 := by
  have h2 : μ 2 = (-1 : ℤ) := ArithmeticFunction.moebius_apply_prime (by norm_num)
  norm_num [mertensSummatory, Finset.sum_range_succ, ArithmeticFunction.moebius_apply_one, h2]

theorem mertensCoordinate_two : mertensAmplitudeCoordinate 2 = none :=
  mertensCoordinate_none_of_zero mertens_two

/-- Exact regression: a nonzero actual sample can lie below the eighth cone. -/
theorem mertens_three : mertensSummatory 3 = (-1 : ℂ) := by
  have h2 : μ 2 = (-1 : ℤ) := ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h3 : μ 3 = (-1 : ℤ) := ArithmeticFunction.moebius_apply_prime (by norm_num)
  norm_num [mertensSummatory, Finset.sum_range_succ, ArithmeticFunction.moebius_apply_one, h2, h3]

theorem mertensAmplitude_three : mertensAmplitude 3 = 1 := by
  change ‖mertensSummatory 3‖ = 1
  rw [mertens_three]
  norm_num

theorem mertensCoordinate_three : mertensAmplitudeCoordinate 3 = some 0 := by
  change amplitudeCoordinate? (3 : ℝ) (mertensAmplitude 3) = some 0
  rw [mertensAmplitude_three, checkedCoordinate_some (by norm_num) (by norm_num), coordinate_one]

/-- Mapping a band is not asserting that every actual sample belongs to it. -/
theorem mertens_three_outside_eighths :
    ¬ (mertensAmplitude 3 ∈ amplitudeBand (3 : ℝ) ((1 : ℝ) / 8) ((7 : ℝ) / 8)) := by
  rw [mertensAmplitude_three]
  intro h
  have hc := (coordinate_mem_Icc_iff (x := (3 : ℝ)) (A := (1 : ℝ))
    (l := (1 : ℝ) / 8) (u := (7 : ℝ) / 8) (by norm_num) (by norm_num)).mpr h
  norm_num [amplitudeCoordinate, Set.mem_Icc] at hc

end RHLean.Analysis.MertensAmplitude
