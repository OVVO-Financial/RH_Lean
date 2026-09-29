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
      have hfu : ContinuousOn f [[a, b]] := by
        simpa [uIcc_of_le hab] using hf
      have hfint : IntervalIntegrable f MeasureTheory.volume a b :=
        hfu.intervalIntegrable
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
      convert hout using 1

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
  have hfu :
      ContinuousOn
        (fun v : ℝ => exactLiDickmanSegment n (v - 1) / v)
        [[a, b]] := by
    simpa [uIcc_of_le hab] using hf
  simpa [a, b] using hfu.intervalIntegrable


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
  have hgmeas : StronglyMeasurableAtFilter g (nhds u) := by
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


/-- **Dickman unit-interval endpoint identity.**
For every method-of-steps segment,
  (n+1) * rho(n+1) = ∫_n^{n+1} rho(u) du.
This is the finite form used for the factorial envelope. -/
theorem exactLiDickmanSegment_endpoint_identity (n : ℕ) :
    (((n + 1 : ℕ) : ℝ)) *
        exactLiDickmanSegment n (n + 1 : ℕ) =
      ∫ u in (n : ℝ)..(((n + 1 : ℕ) : ℝ)),
        exactLiDickmanSegment n u := by
  induction n with
  | zero =>
      norm_num [exactLiDickmanSegment]
  | succ n ih =>
      let a : ℝ := ((n + 1 : ℕ) : ℝ)
      let b : ℝ := ((n + 2 : ℕ) : ℝ)
      let p : ℝ → ℝ := exactLiDickmanSegment n
      let r : ℝ → ℝ := exactLiDickmanSegment (n + 1)
      have hab : a ≤ b := by
        dsimp [a, b]
        norm_num
      have hrcont : ContinuousOn r (Icc a b) := by
        simpa [r, a, b, Nat.cast_add, Nat.cast_one, add_assoc] using
          exactLiDickmanSegment_continuousOn (n + 1)
      have hshift :
          ContinuousOn (fun u : ℝ => u - 1) (Icc a b) := by
        fun_prop
      have hmap :
          MapsTo (fun u : ℝ => u - 1) (Icc a b)
            (Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) := by
        simpa [a, b] using exactLiDickman_shift_mapsTo n
      have hpcont :
          ContinuousOn (fun u : ℝ => p (u - 1)) (Icc a b) := by
        dsimp [p]
        exact (exactLiDickmanSegment_continuousOn n).comp hshift hmap
      have hprodcont :
          ContinuousOn (fun u : ℝ => u * r u) (Icc a b) :=
        continuousOn_id.mul hrcont
      have hderiv :
          ∀ u ∈ Ioo a b,
            HasDerivWithinAt (fun t : ℝ => t * r t)
              (r u - p (u - 1)) (Ioi u) u := by
        intro u hu
        have hu0 : u ≠ 0 := by
          have ha1 : (1 : ℝ) ≤ a := by
            dsimp [a]
            exact_mod_cast (show 1 ≤ n + 1 by omega)
          exact ne_of_gt (lt_of_lt_of_le (by norm_num) (ha1.trans hu.1.le))
        have hrder :
            HasDerivAt r (-p (u - 1) / u) u := by
          simpa [r, p, a, b] using
            exactLiDickmanSegment_succ_hasDerivAt n
              (by simpa [a, b] using hu)
        have hmul := (hasDerivAt_id u).mul hrder
        have hcoef :
            r u + u * (-p (u - 1) / u) =
              r u - p (u - 1) := by
          field_simp [hu0]
          ring
        have hmul' :
            HasDerivAt (fun t : ℝ => t * r t)
              (r u + u * (-p (u - 1) / u)) u := by
          simpa using hmul
        rw [hcoef] at hmul'
        exact hmul'.hasDerivWithinAt
      have hr_uIcc : ContinuousOn r [[a, b]] := by
        simpa [uIcc_of_le hab] using hrcont
      have hp_uIcc :
          ContinuousOn (fun u : ℝ => p (u - 1)) [[a, b]] := by
        simpa [uIcc_of_le hab] using hpcont
      have hrint : IntervalIntegrable r MeasureTheory.volume a b :=
        hr_uIcc.intervalIntegrable
      have hpint :
          IntervalIntegrable (fun u : ℝ => p (u - 1))
            MeasureTheory.volume a b :=
        hp_uIcc.intervalIntegrable
      have hdiffint :
          IntervalIntegrable (fun u : ℝ => r u - p (u - 1))
            MeasureTheory.volume a b :=
        hrint.sub hpint
      have hFTC :=
        intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
          (a := a) (b := b) (f := fun u : ℝ => u * r u)
          (f' := fun u : ℝ => r u - p (u - 1))
          hab hprodcont hderiv hdiffint
      rw [intervalIntegral.integral_sub hrint hpint] at hFTC
      change (∫ u in a..b, r u) - (∫ u in a..b, p (u - 1)) =
        b * r b - a * r a at hFTC
      have hpShift :
          (∫ u in a..b, p (u - 1)) =
            ∫ u in (n : ℝ)..a, p u := by
        rw [intervalIntegral.integral_comp_sub_right]
        congr 1 <;> dsimp [a, b] <;> push_cast <;> ring
      have ih' :
          a * p a = ∫ u in (n : ℝ)..a, p u := by
        simpa [a, p] using ih
      have hpIntegral :
          (∫ u in a..b, p (u - 1)) = a * p a := by
        rw [hpShift, ← ih']
      have hglue : r a = p a := by
        simpa [r, p, a] using exactLiDickmanSegment_succ_left n
      rw [hpIntegral, hglue] at hFTC
      have htarget :
          b * r b = ∫ u in a..b, r u := by
        linarith
      simpa [a, b, r, Nat.cast_add, Nat.cast_one, add_assoc] using htarget




/-- A nonnegative preceding Dickman segment forces the successor segment to be
antitone on its native unit interval. -/
theorem exactLiDickmanSegment_succ_antitoneOn_of_prev_nonneg
    (n : ℕ)
    (hprev : ∀ u ∈ Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ)),
      0 ≤ exactLiDickmanSegment n u) :
    AntitoneOn (exactLiDickmanSegment (n + 1))
      (Icc (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ))) := by
  apply antitoneOn_of_deriv_nonpos
    (convex_Icc (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)))
    (exactLiDickmanSegment_continuousOn (n + 1))
  · rw [interior_Icc]
    intro u hu
    exact
      (exactLiDickmanSegment_succ_hasDerivAt n
        (u := u) hu).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro u hu
    have hd :=
      exactLiDickmanSegment_succ_hasDerivAt n
        (u := u) hu
    rw [hd.deriv]
    have hshift :
        u - 1 ∈ Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ)) := by
      constructor <;> norm_num at hu ⊢ <;> linarith
    have hnum := hprev (u - 1) hshift
    have hupos : 0 < u := by
      have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      linarith [hu.1]
    have hdiv :
        0 ≤ exactLiDickmanSegment n (u - 1) / u :=
      div_nonneg hnum hupos.le
    have hneg :
        -(exactLiDickmanSegment n (u - 1) / u) ≤ 0 :=
      neg_nonpos.mpr hdiv
    simpa [neg_div] using hneg

/-- If the previous Dickman segment is nonnegative, then the successor segment
is nonnegative as well.  The key endpoint step uses the exact endpoint-average
identity: an antitone function has integral at least its right endpoint, while
the identity multiplies that same endpoint by n+2. -/
theorem exactLiDickmanSegment_succ_nonneg_of_prev_nonneg
    (n : ℕ)
    (hprev : ∀ u ∈ Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ)),
      0 ≤ exactLiDickmanSegment n u) :
    ∀ u ∈ Icc (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)),
      0 ≤ exactLiDickmanSegment (n + 1) u := by
  let a : ℝ := ((n + 1 : ℕ) : ℝ)
  let b : ℝ := ((n + 2 : ℕ) : ℝ)
  let f : ℝ → ℝ := exactLiDickmanSegment (n + 1)
  have hab : a ≤ b := by
    dsimp [a, b]
    norm_num
  have hanti : AntitoneOn f (Icc a b) := by
    simpa [a, b, f] using
      exactLiDickmanSegment_succ_antitoneOn_of_prev_nonneg n hprev
  have hcont : ContinuousOn f [[a, b]] := by
    have hc := exactLiDickmanSegment_continuousOn (n + 1)
    simpa [a, b, f, uIcc_of_le hab, Nat.cast_add, Nat.cast_one, add_assoc] using hc
  have hfint : IntervalIntegrable f MeasureTheory.volume a b :=
    hcont.intervalIntegrable
  have hconstint :
      IntervalIntegrable (fun _ : ℝ => f b) MeasureTheory.volume a b := by
    exact (continuousOn_const :
      ContinuousOn (fun _ : ℝ => f b) [[a, b]]).intervalIntegrable
  have hbmem : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hmono :
      (∫ x in a..b, f b) ≤ ∫ x in a..b, f x := by
    apply intervalIntegral.integral_mono_on hab hconstint hfint
    intro x hx
    exact hanti hx hbmem hx.2
  have hconst :
      (∫ _x in a..b, f b) = f b := by
    rw [intervalIntegral.integral_const]
    dsimp [a, b]
    push_cast
    ring
  rw [hconst] at hmono
  have hid := exactLiDickmanSegment_endpoint_identity (n + 1)
  have hid' :
      b * f b = ∫ x in a..b, f x := by
    simpa [a, b, f, Nat.cast_add, Nat.cast_one, add_assoc] using hid
  rw [← hid'] at hmono
  have hbgt : (1 : ℝ) < b := by
    dsimp [b]
    exact_mod_cast (show 1 < n + 2 by omega)
  have hright : 0 ≤ f b := by
    nlinarith
  intro u hu
  exact hright.trans (hanti hu hbmem hu.2)

/-- Every method-of-steps Dickman segment is nonnegative on its native unit
interval. -/
theorem exactLiDickmanSegment_nonneg (n : ℕ) :
    ∀ u ∈ Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ)),
      0 ≤ exactLiDickmanSegment n u := by
  induction n with
  | zero =>
      intro u hu
      simp [exactLiDickmanSegment]
  | succ n ih =>
      exact exactLiDickmanSegment_succ_nonneg_of_prev_nonneg n ih

/-- Hence every Dickman segment is antitone on its native interval. -/
theorem exactLiDickmanSegment_antitoneOn (n : ℕ) :
    AntitoneOn (exactLiDickmanSegment n)
      (Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) := by
  cases n with
  | zero =>
      intro x hx y hy hxy
      simp [exactLiDickmanSegment]
  | succ n =>
      exact
        exactLiDickmanSegment_succ_antitoneOn_of_prev_nonneg n
          (exactLiDickmanSegment_nonneg n)


/-- **Factorial Dickman envelope.**
On the native segment `[n,n+1]`, the method-of-steps solution is at most
`1/n!`.  The proof uses the endpoint-average identity and antitonicity; no
asymptotic estimate is used. -/
theorem exactLiDickmanSegment_le_inv_factorial (n : ℕ) :
    ∀ u ∈ Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ)),
      exactLiDickmanSegment n u ≤
        (Nat.factorial n : ℝ)⁻¹ := by
  induction n with
  | zero =>
      intro u hu
      norm_num [exactLiDickmanSegment]
  | succ n ih =>
      let a : ℝ := ((n + 1 : ℕ) : ℝ)
      let b : ℝ := ((n + 2 : ℕ) : ℝ)
      let p : ℝ → ℝ := exactLiDickmanSegment n
      let f : ℝ → ℝ := exactLiDickmanSegment (n + 1)
      have hab : a ≤ b := by
        dsimp [a, b]
        norm_num
      have hna : ((n : ℕ) : ℝ) ≤ a := by
        dsimp [a]
        norm_num
      have hpcont :
          ContinuousOn p
            [[((n : ℕ) : ℝ), a]] := by
        have hc := exactLiDickmanSegment_continuousOn n
        simpa [p, a, uIcc_of_le hna] using hc
      have hpint :
          IntervalIntegrable p MeasureTheory.volume ((n : ℕ) : ℝ) a :=
        hpcont.intervalIntegrable
      have hcint :
          IntervalIntegrable (fun _ : ℝ => (Nat.factorial n : ℝ)⁻¹)
            MeasureTheory.volume ((n : ℕ) : ℝ) a := by
        exact (continuousOn_const :
          ContinuousOn (fun _ : ℝ => (Nat.factorial n : ℝ)⁻¹)
            [[((n : ℕ) : ℝ), a]]).intervalIntegrable
      have hint_le :
          (∫ x in ((n : ℕ) : ℝ)..a, p x) ≤
            (Nat.factorial n : ℝ)⁻¹ := by
        calc
          (∫ x in ((n : ℕ) : ℝ)..a, p x)
              ≤ ∫ _x in ((n : ℕ) : ℝ)..a,
                  (Nat.factorial n : ℝ)⁻¹ := by
                apply intervalIntegral.integral_mono_on hna hpint hcint
                intro x hx
                exact ih x (by simpa [a] using hx)
          _ = (Nat.factorial n : ℝ)⁻¹ := by
                simp [a]
      have hid := exactLiDickmanSegment_endpoint_identity n
      have hid' :
          a * p a =
            ∫ x in ((n : ℕ) : ℝ)..a, p x := by
        simpa [a, p] using hid
      have hprod :
          a * p a ≤ (Nat.factorial n : ℝ)⁻¹ := by
        rw [hid']
        exact hint_le
      have hapos : 0 < a := by
        dsimp [a]
        positivity
      have hpa :
          p a ≤ (Nat.factorial n : ℝ)⁻¹ / a := by
        apply (le_div_iff₀ hapos).2
        simpa [mul_comm] using hprod
      have hfac :
          (Nat.factorial (n + 1) : ℝ) =
            a * (Nat.factorial n : ℝ) := by
        dsimp [a]
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hratio :
          (Nat.factorial n : ℝ)⁻¹ / a =
            (Nat.factorial (n + 1) : ℝ)⁻¹ := by
        rw [hfac]
        simp only [div_eq_mul_inv, mul_inv_rev]
      have hleft :
          f a ≤ (Nat.factorial (n + 1) : ℝ)⁻¹ := by
        have hglue : f a = p a := by
          simpa [f, p, a] using exactLiDickmanSegment_succ_left n
        rw [hglue, ← hratio]
        exact hpa
      have hanti : AntitoneOn f (Icc a b) := by
        simpa [f, a, b, Nat.cast_add, Nat.cast_one, add_assoc] using
          exactLiDickmanSegment_antitoneOn (n + 1)
      intro u hu
      have hamem : a ∈ Icc a b := ⟨le_rfl, hab⟩
      have hule : f u ≤ f a := hanti hamem hu hu.1
      exact hule.trans hleft


/-- The elementary majorant for one logarithmic Dickman segment in the
continuous exact-Li total-variation integral. -/
def exactLiDickmanFactorialMajorant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (n + 2) / (Nat.factorial (n + 1) : ℝ)

/-- The factorial Dickman majorant is summable. -/
theorem exactLiDickmanFactorialMajorant_summable :
    Summable exactLiDickmanFactorialMajorant := by
  let f : ℕ → ℝ := fun n =>
    (2 : ℝ) ^ n / (Nat.factorial n : ℝ)
  have hs : Summable f := by
    simpa [f] using Real.summable_pow_div_factorial 2
  have hshift : Summable (fun n : ℕ => f (n + 1)) :=
    (summable_nat_add_iff 1 (G := ℝ)).2 hs
  have hpoint :
      exactLiDickmanFactorialMajorant =
        fun n : ℕ => 2 * f (n + 1) := by
    funext n
    unfold exactLiDickmanFactorialMajorant
    dsimp [f]
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    ring
  rw [hpoint]
  exact hshift.mul_left 2

/-- **Exact majorant sum.**
The segment bounds add to the explicit constant `2 * (exp 2 - 1)`. -/
theorem tsum_exactLiDickmanFactorialMajorant :
    (∑' n : ℕ, exactLiDickmanFactorialMajorant n) =
      2 * (Real.exp 2 - 1) := by
  let f : ℕ → ℝ := fun n =>
    (2 : ℝ) ^ n / (Nat.factorial n : ℝ)
  have hs : Summable f := by
    simpa [f] using Real.summable_pow_div_factorial 2
  have hsplit := hs.sum_add_tsum_nat_add 1
  have hsum : (∑' n : ℕ, f n) = Real.exp 2 := by
    dsimp [f]
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hprefix : (∑ n ∈ Finset.range 1, f n) = 1 := by
    simp [f]
  have htail : (∑' n : ℕ, f (n + 1)) = Real.exp 2 - 1 := by
    rw [hprefix, hsum] at hsplit
    linarith
  have hpoint :
      ∀ n : ℕ, exactLiDickmanFactorialMajorant n =
        2 * f (n + 1) := by
    intro n
    unfold exactLiDickmanFactorialMajorant
    dsimp [f]
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    ring
  calc
    (∑' n : ℕ, exactLiDickmanFactorialMajorant n)
        = ∑' n : ℕ, 2 * f (n + 1) := tsum_congr hpoint
    _ = 2 * ∑' n : ℕ, f (n + 1) := by rw [tsum_mul_left]
    _ = 2 * (Real.exp 2 - 1) := by rw [htail]


/-- The total-variation integrand on logarithmic segment `n`.
Under `t = 2^(u+1)`, this is exactly
`2^(u+1) * rho(u) / (u+1)`. -/
def exactLiDickmanVariationIntegrand (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp ((u + 1) * Real.log 2) / (u + 1) *
    exactLiDickmanSegment n u

/-- One complete logarithmic Dickman segment of the continuous Li
total-variation integral. -/
def exactLiDickmanVariationSegment (n : ℕ) : ℝ :=
  ∫ u in (n : ℝ)..((n + 1 : ℕ) : ℝ),
    exactLiDickmanVariationIntegrand n u

private theorem exactLiDickmanVariationIntegrand_continuousOn (n : ℕ) :
    ContinuousOn (exactLiDickmanVariationIntegrand n)
      (Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) := by
  have hden :
      ∀ u ∈ Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ)),
        u + 1 ≠ 0 := by
    intro u hu
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hunonneg : 0 ≤ u := hnn.trans hu.1
    linarith
  have hnum :
      ContinuousOn
        (fun u : ℝ => Real.exp ((u + 1) * Real.log 2))
        (Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) := by
    fun_prop
  have hdencont :
      ContinuousOn (fun u : ℝ => u + 1)
        (Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) := by
    fun_prop
  unfold exactLiDickmanVariationIntegrand
  exact (hnum.div hdencont hden).mul
    (exactLiDickmanSegment_continuousOn n)

/-- Pointwise factorial majorant for the continuous Li variation density on a
native Dickman segment. -/
theorem exactLiDickmanVariationIntegrand_le_majorant
    (n : ℕ) {u : ℝ}
    (hu : u ∈ Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) :
    exactLiDickmanVariationIntegrand n u ≤
      exactLiDickmanFactorialMajorant n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hu1pos : 0 < u + 1 := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith [hu.1]
  have harg :
      (u + 1) * Real.log 2 ≤
        (((n + 2 : ℕ) : ℝ)) * Real.log 2 := by
    apply mul_le_mul_of_nonneg_right _ hlog2.le
    have huupper : u ≤ (n : ℝ) + 1 := by
      simpa [Nat.cast_add, Nat.cast_one] using hu.2
    have hshift : u + 1 ≤ (n : ℝ) + 2 := by linarith
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hshift
  have hexp :
      Real.exp ((u + 1) * Real.log 2) ≤
        (2 : ℝ) ^ (n + 2) := by
    calc
      Real.exp ((u + 1) * Real.log 2)
          ≤ Real.exp ((((n + 2 : ℕ) : ℝ)) * Real.log 2) :=
            Real.exp_le_exp.mpr harg
      _ = (2 : ℝ) ^ (n + 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hdenle :
      ((n + 1 : ℕ) : ℝ) ≤ u + 1 := by
    have hshift : (n : ℝ) + 1 ≤ u + 1 := by linarith [hu.1]
    simpa [Nat.cast_add, Nat.cast_one] using hshift
  have hfrac :
      Real.exp ((u + 1) * Real.log 2) / (u + 1) ≤
        (2 : ℝ) ^ (n + 2) / ((n + 1 : ℕ) : ℝ) := by
    calc
      Real.exp ((u + 1) * Real.log 2) / (u + 1)
          ≤ (2 : ℝ) ^ (n + 2) / (u + 1) :=
            div_le_div_of_nonneg_right hexp hu1pos.le
      _ ≤ (2 : ℝ) ^ (n + 2) / ((n + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hn1pos hdenle
  have hrho0 : 0 ≤ exactLiDickmanSegment n u :=
    exactLiDickmanSegment_nonneg n u hu
  have hrho :
      exactLiDickmanSegment n u ≤
        (Nat.factorial n : ℝ)⁻¹ :=
    exactLiDickmanSegment_le_inv_factorial n u hu
  unfold exactLiDickmanVariationIntegrand
  calc
    Real.exp ((u + 1) * Real.log 2) / (u + 1) *
        exactLiDickmanSegment n u
        ≤ ((2 : ℝ) ^ (n + 2) / ((n + 1 : ℕ) : ℝ)) *
            exactLiDickmanSegment n u :=
          mul_le_mul_of_nonneg_right hfrac hrho0
    _ ≤ ((2 : ℝ) ^ (n + 2) / ((n + 1 : ℕ) : ℝ)) *
          (Nat.factorial n : ℝ)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hrho (by positivity)
    _ = exactLiDickmanFactorialMajorant n := by
          unfold exactLiDickmanFactorialMajorant
          rw [Nat.factorial_succ]
          push_cast
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring

/-- The continuous Li variation integrand is nonnegative on each native
Dickman segment. -/
theorem exactLiDickmanVariationIntegrand_nonneg
    (n : ℕ) {u : ℝ}
    (hu : u ∈ Icc ((n : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ))) :
    0 ≤ exactLiDickmanVariationIntegrand n u := by
  unfold exactLiDickmanVariationIntegrand
  have hu1pos : 0 < u + 1 := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith [hu.1]
  exact mul_nonneg
    (div_nonneg (Real.exp_pos _).le hu1pos.le)
    (exactLiDickmanSegment_nonneg n u hu)

/-- **One-segment variation bound.**
Every complete logarithmic Dickman segment contributes at most
`2^(n+2)/(n+1)!`. -/
theorem exactLiDickmanVariationSegment_le_majorant (n : ℕ) :
    exactLiDickmanVariationSegment n ≤
      exactLiDickmanFactorialMajorant n := by
  have hab : (n : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by norm_num
  have hcont := exactLiDickmanVariationIntegrand_continuousOn n
  have hint : IntervalIntegrable
      (exactLiDickmanVariationIntegrand n) MeasureTheory.volume
      (n : ℝ) (((n + 1 : ℕ) : ℝ)) := by
    have hu :
        ContinuousOn (exactLiDickmanVariationIntegrand n)
          [[(n : ℝ), (((n + 1 : ℕ) : ℝ))]] := by
      simpa [uIcc_of_le hab] using hcont
    exact hu.intervalIntegrable
  have hconst : IntervalIntegrable
      (fun _ : ℝ => exactLiDickmanFactorialMajorant n)
      MeasureTheory.volume (n : ℝ) (((n + 1 : ℕ) : ℝ)) := by
    exact (continuousOn_const :
      ContinuousOn (fun _ : ℝ => exactLiDickmanFactorialMajorant n)
        [[(n : ℝ), (((n + 1 : ℕ) : ℝ))]]).intervalIntegrable
  unfold exactLiDickmanVariationSegment
  calc
    (∫ u in (n : ℝ)..((n + 1 : ℕ) : ℝ),
        exactLiDickmanVariationIntegrand n u)
        ≤ ∫ _u in (n : ℝ)..((n + 1 : ℕ) : ℝ),
            exactLiDickmanFactorialMajorant n := by
          apply intervalIntegral.integral_mono_on hab hint hconst
          intro u hu
          exact exactLiDickmanVariationIntegrand_le_majorant n hu
    _ = exactLiDickmanFactorialMajorant n := by
          simp

/-- Every complete continuous-Li variation segment is nonnegative. -/
theorem exactLiDickmanVariationSegment_nonneg (n : ℕ) :
    0 ≤ exactLiDickmanVariationSegment n := by
  unfold exactLiDickmanVariationSegment
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  exact exactLiDickmanVariationIntegrand_nonneg n hu


/-- **Uniform complete-segment total-variation bound.**
Every finite collection of complete logarithmic Dickman segments is bounded by
the same explicit constant `2 * (exp 2 - 1)`. -/
theorem sum_exactLiDickmanVariationSegment_le (N : ℕ) :
    (∑ n ∈ Finset.range N, exactLiDickmanVariationSegment n) ≤
      2 * (Real.exp 2 - 1) := by
  calc
    (∑ n ∈ Finset.range N, exactLiDickmanVariationSegment n)
        ≤ ∑ n ∈ Finset.range N,
            exactLiDickmanFactorialMajorant n := by
          apply Finset.sum_le_sum
          intro n hn
          exact exactLiDickmanVariationSegment_le_majorant n
    _ ≤ ∑' n : ℕ, exactLiDickmanFactorialMajorant n := by
          exact exactLiDickmanFactorialMajorant_summable.sum_le_tsum
            (Finset.range N) (fun n hn => by
              unfold exactLiDickmanFactorialMajorant
              positivity)
    _ = 2 * (Real.exp 2 - 1) :=
          tsum_exactLiDickmanFactorialMajorant


/-- Final partial logarithmic Dickman segment, from the left integer endpoint
to an arbitrary point in the native unit interval. -/
def exactLiDickmanVariationPartial (N : ℕ) (u : ℝ) : ℝ :=
  ∫ v in (N : ℝ)..u, exactLiDickmanVariationIntegrand N v

/-- A partial final segment is nonnegative. -/
theorem exactLiDickmanVariationPartial_nonneg
    (N : ℕ) {u : ℝ}
    (hu : u ∈ Icc ((N : ℕ) : ℝ) (((N + 1 : ℕ) : ℝ))) :
    0 ≤ exactLiDickmanVariationPartial N u := by
  unfold exactLiDickmanVariationPartial
  apply intervalIntegral.integral_nonneg hu.1
  intro v hv
  exact exactLiDickmanVariationIntegrand_nonneg N
    ⟨hv.1.trans hu.1, hv.2.trans hu.2⟩

/-- A partial final segment is bounded by the same factorial majorant as the
complete segment. -/
theorem exactLiDickmanVariationPartial_le_majorant
    (N : ℕ) {u : ℝ}
    (hu : u ∈ Icc ((N : ℕ) : ℝ) (((N + 1 : ℕ) : ℝ))) :
    exactLiDickmanVariationPartial N u ≤
      exactLiDickmanFactorialMajorant N := by
  have hfullInt :
      IntervalIntegrable (exactLiDickmanVariationIntegrand N)
        MeasureTheory.volume (N : ℝ) (((N + 1 : ℕ) : ℝ)) := by
    have hab : (N : ℝ) ≤ (((N + 1 : ℕ) : ℝ)) := by norm_num
    have hc := exactLiDickmanVariationIntegrand_continuousOn N
    have hucc :
        ContinuousOn (exactLiDickmanVariationIntegrand N)
          [[(N : ℝ), (((N + 1 : ℕ) : ℝ))]] := by
      simpa [uIcc_of_le hab] using hc
    exact hucc.intervalIntegrable
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict
        (Ioc ((N : ℕ) : ℝ) (((N + 1 : ℕ) : ℝ)))]
        exactLiDickmanVariationIntegrand N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact exactLiDickmanVariationIntegrand_nonneg N
      ⟨hv.1, hv.2⟩
  have hpartialFull :
      exactLiDickmanVariationPartial N u ≤
        exactLiDickmanVariationSegment N := by
    unfold exactLiDickmanVariationPartial exactLiDickmanVariationSegment
    exact intervalIntegral.integral_mono_interval
      le_rfl hu.1 hu.2 hnonneg hfullInt
  exact hpartialFull.trans
    (exactLiDickmanVariationSegment_le_majorant N)

/-- Continuous exact-Li variation accumulated through all complete logarithmic
segments below N and one final partial segment. -/
def exactLiDickmanVariationPrimitive (N : ℕ) (u : ℝ) : ℝ :=
  (∑ n ∈ Finset.range N, exactLiDickmanVariationSegment n) +
    exactLiDickmanVariationPartial N u

/-- The finite continuous exact-Li variation primitive is nonnegative. -/
theorem exactLiDickmanVariationPrimitive_nonneg
    (N : ℕ) {u : ℝ}
    (hu : u ∈ Icc ((N : ℕ) : ℝ) (((N + 1 : ℕ) : ℝ))) :
    0 ≤ exactLiDickmanVariationPrimitive N u := by
  unfold exactLiDickmanVariationPrimitive
  exact add_nonneg
    (Finset.sum_nonneg fun n hn => exactLiDickmanVariationSegment_nonneg n)
    (exactLiDickmanVariationPartial_nonneg N hu)

/-- **Uniform continuous exact-Li total-variation bound.**
At every finite logarithmic endpoint, complete segments plus the last partial
segment cost at most the universal Dickman constant `2 * (exp 2 - 1)`. -/
theorem exactLiDickmanVariationPrimitive_le
    (N : ℕ) {u : ℝ}
    (hu : u ∈ Icc ((N : ℕ) : ℝ) (((N + 1 : ℕ) : ℝ))) :
    exactLiDickmanVariationPrimitive N u ≤
      2 * (Real.exp 2 - 1) := by
  have hpart :=
    exactLiDickmanVariationPartial_le_majorant N hu
  have hsum :
      (∑ n ∈ Finset.range N, exactLiDickmanVariationSegment n) ≤
        ∑ n ∈ Finset.range N, exactLiDickmanFactorialMajorant n := by
    apply Finset.sum_le_sum
    intro n hn
    exact exactLiDickmanVariationSegment_le_majorant n
  have hcombine :
      exactLiDickmanVariationPrimitive N u ≤
        ∑ n ∈ Finset.range (N + 1),
          exactLiDickmanFactorialMajorant n := by
    unfold exactLiDickmanVariationPrimitive
    rw [Finset.sum_range_succ]
    exact add_le_add hsum hpart
  calc
    exactLiDickmanVariationPrimitive N u
        ≤ ∑ n ∈ Finset.range (N + 1),
            exactLiDickmanFactorialMajorant n := hcombine
    _ ≤ ∑' n : ℕ, exactLiDickmanFactorialMajorant n := by
          exact exactLiDickmanFactorialMajorant_summable.sum_le_tsum
            (Finset.range (N + 1)) (fun n hn => by
              unfold exactLiDickmanFactorialMajorant
              positivity)
    _ = 2 * (Real.exp 2 - 1) :=
          tsum_exactLiDickmanFactorialMajorant

end RHLean.Analysis
