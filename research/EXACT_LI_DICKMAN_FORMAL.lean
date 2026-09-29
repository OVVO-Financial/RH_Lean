import Mathlib

/-!
# Exact-Li Dickman model by method of steps

This file constructs the continuous reciprocal exact-Li reference directly by
the classical method of steps.  It deliberately avoids Mellin inversion.

Segment n represents the Dickman solution on [n,n+1].  Segment zero is the
constant one; each successor segment is the integral solution of

  u * rho'(u) + rho(u-1) = 0

with its left endpoint glued to the preceding segment.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Interval

namespace RHLean.Analysis

/-- Method-of-steps Dickman segment.  Segment n is intended for u in [n,n+1]. -/
def exactLiDickmanSegment : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun u =>
      exactLiDickmanSegment n (n + 1 : ℕ) -
        ∫ v in ((n + 1 : ℕ) : ℝ)..u,
          exactLiDickmanSegment n (v - 1) / v

@[simp] theorem exactLiDickmanSegment_zero (u : ℝ) :
    exactLiDickmanSegment 0 u = 1 := rfl

/-- Consecutive method-of-steps pieces agree at their common endpoint. -/
@[simp] theorem exactLiDickmanSegment_succ_left (n : ℕ) :
    exactLiDickmanSegment (n + 1) (n + 1 : ℕ) =
      exactLiDickmanSegment n (n + 1 : ℕ) := by
  simp [exactLiDickmanSegment]

private theorem exactLiDickman_shift_mapsTo
    (n : ℕ) :
    MapsTo (fun v : ℝ => v - 1)
      (Icc (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)))
      (Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) := by
  intro v hv
  constructor <;> norm_num at hv ⊢ <;> linarith

/-- Every Dickman segment is continuous on its native unit interval. -/
theorem exactLiDickmanSegment_continuousOn (n : ℕ) :
    ContinuousOn (exactLiDickmanSegment n)
      (Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) := by
  induction n with
  | zero =>
      simpa [exactLiDickmanSegment] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 1))
  | succ n ih =>
      let a : ℝ := ((n + 1 : ℕ) : ℝ)
      let b : ℝ := ((n + 2 : ℕ) : ℝ)
      let f : ℝ → ℝ := fun v => exactLiDickmanSegment n (v - 1) / v
      have hshift :
          ContinuousOn (fun v : ℝ => v - 1) (Icc a b) := by
        fun_prop
      have hmap :
          MapsTo (fun v : ℝ => v - 1) (Icc a b)
            (Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) := by
        simpa [a, b] using exactLiDickman_shift_mapsTo n
      have hprev :
          ContinuousOn (fun v : ℝ => exactLiDickmanSegment n (v - 1))
            (Icc a b) :=
        ih.comp hshift hmap
      have hden :
          ContinuousOn (fun v : ℝ => v) (Icc a b) := continuousOn_id
      have hne : ∀ v ∈ Icc a b, v ≠ 0 := by
        intro v hv
        have ha : (1 : ℝ) ≤ a := by
          dsimp [a]
          exact_mod_cast (show 1 ≤ n + 1 by omega)
        have hvpos : 0 < v := lt_of_lt_of_le (by norm_num) (ha.trans hv.1)
        exact ne_of_gt hvpos
      have hf : ContinuousOn f (Icc a b) := by
        dsimp [f]
        exact hprev.div hden hne
      have hab : a ≤ b := by
        dsimp [a, b]
        norm_num
      have hfint : IntervalIntegrable f MeasureTheory.volume a b := by
        simpa [uIcc_of_le hab] using hf.intervalIntegrable
      have hprim :
          ContinuousOn (fun u : ℝ => ∫ v in a..u, f v)
            (Icc a b) := by
        have ha_mem : a ∈ [[a, b]] := left_mem_uIcc
        have hp :=
          intervalIntegral.continuousOn_primitive_interval' hfint ha_mem
        simpa [uIcc_of_le hab] using hp
      have hconst :
          ContinuousOn (fun _ : ℝ =>
            exactLiDickmanSegment n (n + 1 : ℕ)) (Icc a b) :=
        continuousOn_const
      have hout :
          ContinuousOn
            (fun u : ℝ =>
              exactLiDickmanSegment n (n + 1 : ℕ) -
                ∫ v in a..u, f v)
            (Icc a b) :=
        hconst.sub hprim
      simpa [exactLiDickmanSegment, a, b, f] using hout

/-- The delay integrand on one successor segment is interval-integrable. -/
theorem exactLiDickmanSegment_delay_intervalIntegrable
    (n : ℕ) :
    IntervalIntegrable
      (fun v : ℝ => exactLiDickmanSegment n (v - 1) / v)
      MeasureTheory.volume
      (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)) := by
  let a : ℝ := ((n + 1 : ℕ) : ℝ)
  let b : ℝ := ((n + 2 : ℕ) : ℝ)
  have hshift :
      ContinuousOn (fun v : ℝ => v - 1) (Icc a b) := by
    fun_prop
  have hmap :
      MapsTo (fun v : ℝ => v - 1) (Icc a b)
        (Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) := by
    simpa [a, b] using exactLiDickman_shift_mapsTo n
  have hprev :
      ContinuousOn (fun v : ℝ => exactLiDickmanSegment n (v - 1))
        (Icc a b) :=
    (exactLiDickmanSegment_continuousOn n).comp hshift hmap
  have hne : ∀ v ∈ Icc a b, v ≠ 0 := by
    intro v hv
    have ha : (1 : ℝ) ≤ a := by
      dsimp [a]
      exact_mod_cast (show 1 ≤ n + 1 by omega)
    have hvpos : 0 < v := lt_of_lt_of_le (by norm_num) (ha.trans hv.1)
    exact ne_of_gt hvpos
  have hf :
      ContinuousOn
        (fun v : ℝ => exactLiDickmanSegment n (v - 1) / v)
        (Icc a b) :=
    hprev.div continuousOn_id hne
  have hab : a ≤ b := by
    dsimp [a, b]
    norm_num
  simpa [a, b, uIcc_of_le hab] using hf.intervalIntegrable


/-- **Dickman delay differential equation on each open successor segment.**
For u in (n+1,n+2), the method-of-steps segment satisfies
  rho'(u) = -rho(u-1)/u.
This is the differential core of the exact-Li continuous reference. -/
theorem exactLiDickmanSegment_succ_hasDerivAt
    (n : ℕ) {u : ℝ}
    (hu : u ∈ Ioo (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ))) :
    HasDerivAt (exactLiDickmanSegment (n + 1))
      (- exactLiDickmanSegment n (u - 1) / u) u := by
  let a : ℝ := ((n + 1 : ℕ) : ℝ)
  let b : ℝ := ((n + 2 : ℕ) : ℝ)
  let g : ℝ → ℝ := fun v => exactLiDickmanSegment n (v - 1) / v
  have hu' : u ∈ Ioo a b := by
    simpa [a, b] using hu
  have hshift :
      ContinuousOn (fun v : ℝ => v - 1) (Icc a b) := by
    fun_prop
  have hmap :
      MapsTo (fun v : ℝ => v - 1) (Icc a b)
        (Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) := by
    simpa [a, b] using exactLiDickman_shift_mapsTo n
  have hprev :
      ContinuousOn (fun v : ℝ => exactLiDickmanSegment n (v - 1))
        (Icc a b) :=
    (exactLiDickmanSegment_continuousOn n).comp hshift hmap
  have hne : ∀ v ∈ Icc a b, v ≠ 0 := by
    intro v hv
    have ha : (1 : ℝ) ≤ a := by
      dsimp [a]
      exact_mod_cast (show 1 ≤ n + 1 by omega)
    have hvpos : 0 < v := lt_of_lt_of_le (by norm_num) (ha.trans hv.1)
    exact ne_of_gt hvpos
  have hgcont : ContinuousOn g (Icc a b) := by
    dsimp [g]
    exact hprev.div continuousOn_id hne
  have hgint : IntervalIntegrable g MeasureTheory.volume a b := by
    simpa [a, b, g] using
      exactLiDickmanSegment_delay_intervalIntegrable n
  have hgAt : ContinuousAt g u :=
    (hgcont u (Ioo_subset_Icc_self hu')).continuousAt
      (Icc_mem_nhds hu'.1 hu'.2)
  have hgmeas : StronglyMeasurableAtFilter g (𝓝 u) := by
    exact (hgcont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter
      isOpen_Ioo u hu'
  have hab : a ≤ b := by
    dsimp [a, b]
    norm_num
  have hau : a ≤ u := hu'.1.le
  have hgint_u : IntervalIntegrable g MeasureTheory.volume a u := by
    apply IntervalIntegrable.mono_set hgint
    rw [uIcc_of_le hau, uIcc_of_le hab]
    intro x hx
    exact ⟨hx.1, hx.2.trans hu'.2.le⟩
  have hint :
      HasDerivAt (fun z : ℝ => ∫ v in a..z, g v) (g u) u :=
    intervalIntegral.integral_hasDerivAt_right hgint_u hgmeas hgAt
  have hconst :
      HasDerivAt
        (fun _ : ℝ => exactLiDickmanSegment n (n + 1 : ℕ)) 0 u :=
    hasDerivAt_const u _
  have hsub := hconst.sub hint
  simpa [exactLiDickmanSegment, a, g, neg_div] using hsub

end RHLean.Analysis
