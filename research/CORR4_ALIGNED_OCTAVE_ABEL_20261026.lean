import Mathlib
import «research.CORR4_TFREE_ALIGNED_SOURCE_20261026»

/-!
# CORR-4: exact octave Abel return at the aligned zero boundary

These are literal a6/period-36 kernel identities, with the same
normalized discrete tent as #1026. The quotient-octave weight is
nonnegative but no pointwise saving for its signed a6 pairing is
asserted. The gain of a factor 1/u is an OPEN analytic estimate,
not an algebraic corollary of this identity.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- The genuine finite tent-averaged a6 cumulative source at quotient u. -/
def corr4PhysicalA6Prefix (X H u : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (X + H - 1),
    vf919ExcludedNormCoefficients m *
      (corr4TentRamp X H (u * m) : ℂ)

/-- The literal tent bucket between consecutive denominator u and u+1. -/
def corr4PhysicalA6Octave (X H u : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (X + H - 1),
    vf919ExcludedNormCoefficients m *
      ((corr4TentRamp X H (u * m) : ℂ) -
       (corr4TentRamp X H ((u + 1) * m) : ℂ))

theorem corr4PhysicalA6Prefix_sub_eq_octave (X H u : ℕ) :
    corr4PhysicalA6Prefix X H u -
      corr4PhysicalA6Prefix X H (u + 1) =
      corr4PhysicalA6Octave X H u := by
  unfold corr4PhysicalA6Prefix corr4PhysicalA6Octave
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Zero-aligned first Abel has NO terminal plateau term. This is the
coefficient-exact identity behind the proposed Case-B octave source. -/
theorem corr4_aligned_first_abel_octaves (q : ℕ) (hq : 1 ≤ q)
    (b : ℕ → ℂ) :
    (∑ u ∈ Finset.Icc 1 (36 * q),
       corr4SharpQuotientDifference u * b u) =
    ∑ u ∈ Finset.Icc 1 (36 * q - 1),
      (vf919SharpQuotientKernel36 u : ℂ) * (b u - b (u + 1)) := by
  have hfirst := corr4_difference_kernel_signed_abel
    (36 * q) (fun u => (vf919SharpQuotientKernel36 u : ℂ)) b
    corr4_sharp_quotient_kernel_zero
  have hz : (vf919SharpQuotientKernel36 (36 * q) : ℂ) = 0 := by
    rw [corr4_quotient_kernel_zero_at_36_multiple]
    norm_num
  have hqpos : 1 ≤ 36 * q := by omega
  have hqsucc : (36 * q - 1) + 1 = 36 * q := by omega
  have hsplit :
      (∑ u ∈ Finset.Icc 1 (36 * q),
        (vf919SharpQuotientKernel36 u : ℂ) * (b u - b (u + 1))) =
      ∑ u ∈ Finset.Icc 1 (36 * q - 1),
        (vf919SharpQuotientKernel36 u : ℂ) * (b u - b (u + 1)) := by
      conv_lhs =>
        rw [← hqsucc, Finset.sum_Icc_succ_top (by omega :
          1 ≤ (36 * q - 1) + 1)]
      rw [hqsucc, hz]
      ring
  change (∑ u ∈ Finset.Icc 1 (36 * q),
      ((vf919SharpQuotientKernel36 u : ℂ) -
        (vf919SharpQuotientKernel36 (u - 1) : ℂ)) * b u) = _
  rw [hfirst, hz, zero_mul, add_zero, hsplit]

theorem corr4_aligned_actual_low_source_eq_octaves (X H q : ℕ)
    (hq : 1 ≤ q) :
    (∑ u ∈ Finset.Icc 1 (36 * q),
       corr4SharpQuotientDifference u * corr4PhysicalA6Prefix X H u) =
    ∑ u ∈ Finset.Icc 1 (36 * q - 1),
      (vf919SharpQuotientKernel36 u : ℂ) * corr4PhysicalA6Octave X H u := by
  rw [corr4_aligned_first_abel_octaves q hq
    (corr4PhysicalA6Prefix X H)]
  apply Finset.sum_congr rfl
  intro u hu
  rw [corr4PhysicalA6Prefix_sub_eq_octave]

#print axioms corr4PhysicalA6Prefix_sub_eq_octave
#print axioms corr4_aligned_first_abel_octaves
#print axioms corr4_aligned_actual_low_source_eq_octaves

end RHLean.Analysis
