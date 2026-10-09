import Mathlib
import RHLean.Analysis.PartialMomentSchurTarget

/-!
# OAI seven-eighths asymmetric row tails in genuine NNS LPM/UPM currency

Stage II OAI's prime-amplitude bin variable g is a REAL clipped
logarithmic amplitude, with 0 <= g <= delta/2. The hard high-row
exponent is dependent on both amplitude and row cardinality.
This module gives the exact partial-moment interface to an
arbitrary finite row family, retaining nonnegative row weights.

The important result is the one-sided Markov-type bound:
  gap^2 * weightedCount {u | g(u) >= target + gap}
    <= UPM_2(g, target).
And the corresponding LOW-tail bound. It is only a USEFUL
REDUCTION, not a claim that the real arithmetic supplies a small
UPM_2. A power saving must be established in a SEPARATE
physical signed/character-moment theorem.

The existing native RHLean.Analysis.PartialMomentSchurTarget
already proves the arbitrary-target four-sector decomposition
and invariant Schur covariance. We reuse its exact scalar
partialUpper/partialLower constructs rather than importing
a new probabilistic axiom or OAI's incompatible Lean toolchain.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

/-- NNS upper partial second moment of finite actual row amplitudes. -/
def vf919RowUPM2 {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (g : ι → ℝ) (target : ℝ) : ℝ :=
  ∑ u ∈ S, w u * (partialUpper (g u) target)^2

/-- NNS lower partial second moment at the SAME amplitude target. -/
def vf919RowLPM2 {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (g : ι → ℝ) (target : ℝ) : ℝ :=
  ∑ u ∈ S, w u * (partialLower (g u) target)^2

/-- Without NEW directional information, ordinary squared energy
is just the sum of the two partial energies. Splitting is not
by itself a power saving or additional cancellation. -/
theorem vf919RowPartialSquare_reassembly (x target : ℝ) :
    (partialUpper x target)^2 + (partialLower x target)^2 =
      (x - target)^2 := by
  by_cases h : target ≤ x
  · simp [partialUpper, partialLower, h, not_lt_of_ge h]
  · have hlt : x < target := lt_of_not_ge h
    simp [partialUpper, partialLower, h, hlt]
    ring

/-- The finite weighed LPM/UPM identity holds for any real
weights (no statistical normalizations or hidden assumptions). -/
theorem vf919RowUPM2_add_LPM2_eq_deviationSquare
    {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (g : ι → ℝ) (target : ℝ) :
    vf919RowUPM2 S w g target +
      vf919RowLPM2 S w g target =
    ∑ u ∈ S, w u * (g u - target)^2 := by
  unfold vf919RowUPM2 vf919RowLPM2
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  calc
    w u * (partialUpper (g u) target)^2 +
        w u * (partialLower (g u) target)^2 =
      w u * ((partialUpper (g u) target)^2 +
        (partialLower (g u) target)^2) := by ring
    _ = w u * (g u - target)^2 := by
      rw [vf919RowPartialSquare_reassembly]

/-- UPM_2 bounds the weighted population of genuinely upper
amplitude rows. This is an EXACT finite-mass inequality;
an asymptotic power gain requires an independent estimate
of the UPM_2 on the actual character-row population. -/
theorem vf919RowUPM2_controls_upperTail
    {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (g : ι → ℝ) (target gap : ℝ)
    (hgap : 0 < gap)
    (hw : ∀ u ∈ S, 0 ≤ w u) :
    gap^2 *
      (∑ u ∈ S.filter (fun u => target + gap ≤ g u), w u) ≤
        vf919RowUPM2 S w g target := by
  classical
  unfold vf919RowUPM2
  rw [Finset.mul_sum]
  calc
    (∑ u ∈ S.filter (fun u => target + gap ≤ g u), gap^2 * w u) ≤
      ∑ u ∈ S.filter (fun u => target + gap ≤ g u),
        w u * (partialUpper (g u) target)^2 := by
          apply Finset.sum_le_sum
          intro u hu
          have huS := (Finset.mem_filter.mp hu).1
          have huGap := (Finset.mem_filter.mp hu).2
          have hut : target ≤ g u := by linarith
          have hsplit : partialUpper (g u) target = g u - target := by
            simp [partialUpper, hut]
          rw [hsplit]
          have hle : gap ≤ g u - target := by linarith
          have hnonneg : 0 ≤ g u - target := by linarith
          have hsquare : gap^2 ≤ (g u - target)^2 := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hle)
              (add_nonneg hgap.le hnonneg)]
          have hb := mul_le_mul_of_nonneg_left hsquare (hw u huS)
          nlinarith
    _ ≤ ∑ u ∈ S, w u * (partialUpper (g u) target)^2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _)
          intro u hu _
          exact mul_nonneg (hw u hu) (sq_nonneg _)

/-- LPM_2 symmetrically controls genuine LOWER amplitude rows.
The two inequalities may have VERY different strengths if the
actual row distribution is asymmetric. -/
theorem vf919RowLPM2_controls_lowerTail
    {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (g : ι → ℝ) (target gap : ℝ)
    (hgap : 0 < gap)
    (hw : ∀ u ∈ S, 0 ≤ w u) :
    gap^2 *
      (∑ u ∈ S.filter (fun u => g u ≤ target - gap), w u) ≤
        vf919RowLPM2 S w g target := by
  classical
  unfold vf919RowLPM2
  rw [Finset.mul_sum]
  calc
    (∑ u ∈ S.filter (fun u => g u ≤ target - gap), gap^2 * w u) ≤
      ∑ u ∈ S.filter (fun u => g u ≤ target - gap),
        w u * (partialLower (g u) target)^2 := by
          apply Finset.sum_le_sum
          intro u hu
          have huS := (Finset.mem_filter.mp hu).1
          have huGap := (Finset.mem_filter.mp hu).2
          have hut : g u < target := by linarith
          have hsplit : partialLower (g u) target = target - g u := by
            simp [partialLower, hut]
          rw [hsplit]
          have hle : gap ≤ target - g u := by linarith
          have hnonneg : 0 ≤ target - g u := by linarith
          have hsquare : gap^2 ≤ (target - g u)^2 := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hle)
              (add_nonneg hgap.le hnonneg)]
          have hb := mul_le_mul_of_nonneg_left hsquare (hw u huS)
          nlinarith
    _ ≤ ∑ u ∈ S, w u * (partialLower (g u) target)^2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _)
          intro u hu _
          exact mul_nonneg (hw u hu) (sq_nonneg _)

/-- For clipped OAI amplitudes, near-saturation of
g/delta at 1/2 is equivalently a LOWER tail of
deficit d(u) = 1/2 - g(u)/delta.

Rows with deficit <= eta/2 are controlled by
LPM_2(deficit; eta); this is the specific dangerous
tail seen in the Stage II numerical endpoint margin.
-/
theorem vf919OAI_saturationTail_le_deficitLPM2
    {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (x : ι → ℝ) (eta : ℝ)
    (heta : 0 < eta)
    (hw : ∀ u ∈ S, 0 ≤ w u) :
    (eta / 2)^2 *
      (∑ u ∈ S.filter (fun u => (1 / 2 : ℝ) - x u ≤ eta / 2),
        w u) ≤
      vf919RowLPM2 S w (fun u => (1 / 2 : ℝ) - x u) eta := by
  have h := vf919RowLPM2_controls_lowerTail S w
    (fun u => (1 / 2 : ℝ) - x u) eta (eta / 2)
    (by linarith) hw
  convert h using 1
  congr 1
  apply Finset.sum_congr
  · ext u
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hu, hux⟩
      exact ⟨hu, by linarith⟩
    · rintro ⟨hu, hux⟩
      exact ⟨hu, by linarith⟩
  · intro u _
    rfl

end RHLean.Analysis
