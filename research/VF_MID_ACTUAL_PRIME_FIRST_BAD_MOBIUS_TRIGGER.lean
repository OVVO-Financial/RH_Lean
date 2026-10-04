import Mathlib
import «research.VF_MID_OWNER_ADMISSIBLE_ESCAPE_CLASS»
import «research.VF_MID_ENDPOINT_TRIGGER_DICTIONARY»

/-!
# Actual-prime first bad scale: exact subdoubling Mobius trigger

This file attacks the post-#884 arithmetic seam without inserting a new
cancellation hypothesis.

The merged admissibility class says that a channel-threatening actual-prime
scale must reproduce on a strict child.  The correct place to start that
reproduction is a *minimal* bad scale.  At a minimal bad scale B, every earlier
anchor A is already inside the radial wall.

On any subdoubling run A <= B <= 2A the repository already proves the exact
frozen-wheel/Mobius identity

  Tracking(A,B)
    = VFMass(A,B)
      - 1/2 PrefixSupply(A,A,B)
      + 1/2 SurvivorMobiusMass(A,B),

and also

  Tracking(A,B) = -(D_B-D_A).

Therefore a first escape forces an explicit signed inequality on the physical
survivor Mobius mass after the deterministic frozen-wheel term is retained
exactly.  No norm, covariance estimate, PNT rate, or probabilistic cancellation
is used here.

This is the exact trigger that the zero-target owner tree must consume.  It is
strictly weaker and more faithful than trying to prove that an arbitrary bad
scale immediately selects a raw VF child packet.
-/

noncomputable section

namespace RHLean.Analysis

/-- The actual prime endpoint is bad at R, while every genuine earlier square
scale from 2 onward is not bad. -/
def VFMidActualPrimeFirstBadAt (K : ℝ) (R : ℕ) : Prop :=
  VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect K R ∧
    ∀ S : ℕ, 2 ≤ S → S < R →
      ¬ VFMidSyntheticBadAt vfMidActualPrimeEndpointDefect K S

/-- Every earlier scale below a first bad scale is inside the same radial wall. -/
theorem vfMidActualPrimeFirstBadAt_prior_inside
    {K : ℝ} {R S : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K R)
    (hS : 2 ≤ S) (hSR : S < R) :
    |vfMidActualPrimeEndpointDefect S| ≤
      K * vfMidSyntheticRadialScale S := by
  exact le_of_not_gt (hfirst.2 S hS hSR)

/-- **Upper first-escape trigger in exact subdoubling Mobius currency.**

If the anchor A is inside the radial wall and the later endpoint B lies above
the upper wall, then the exact frozen-wheel/Mobius tracking expression is
strictly more negative than the radial-wall increment. -/
theorem vfMidActualPrimeUpperEscape_forces_subdoublingMobiusTrigger
    {K : ℝ} {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hAinside :
      |vfMidActualPrimeEndpointDefect A| ≤
        K * vfMidSyntheticRadialScale A)
    (hBupper :
      K * vfMidSyntheticRadialScale B <
        vfMidActualPrimeEndpointDefect B) :
    vfMidDyadicVFMass A B -
          (1 / 2 : ℝ) * vfMidDyadicPrefixSupply A A B +
          (1 / 2 : ℝ) * vfMidDyadicPrefixSurvivorMobiusMassReal A B <
      K * vfMidSyntheticRadialScale A -
        K * vfMidSyntheticRadialScale B := by
  have hAupper :
      vfMidActualPrimeEndpointDefect A ≤
        K * vfMidSyntheticRadialScale A :=
    (le_abs_self _).trans hAinside
  have hdiff :
      K * vfMidSyntheticRadialScale B -
          K * vfMidSyntheticRadialScale A <
        vfMidActualPrimeEndpointDefect B -
          vfMidActualPrimeEndpointDefect A := by
    linarith
  have htrack :=
    vfMidDyadicVFTrackingDefect_eq_neg_primeError_increment
      (A := A) (B := B) (by omega : 2 ≤ A) (by omega : 2 ≤ B) hAB
  have hdict :=
    vfMidDyadicVFTrackingDefect_eq_frozenWheel_add_half_moebius
      hA hAB hBA
  have htrack' :
      vfMidDyadicVFTrackingDefect A B =
        -(vfMidActualPrimeEndpointDefect B -
          vfMidActualPrimeEndpointDefect A) := by
    simpa [vfMidActualPrimeEndpointDefect] using htrack
  rw [htrack'] at hdict
  linarith

/-- **Lower first-escape trigger in exact subdoubling Mobius currency.**

If the anchor A is inside the radial wall and B lies below the lower wall, the
same exact frozen-wheel/Mobius expression is forced strictly positive by more
than the radial-wall increment. -/
theorem vfMidActualPrimeLowerEscape_forces_subdoublingMobiusTrigger
    {K : ℝ} {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hAinside :
      |vfMidActualPrimeEndpointDefect A| ≤
        K * vfMidSyntheticRadialScale A)
    (hBlower :
      vfMidActualPrimeEndpointDefect B <
        -(K * vfMidSyntheticRadialScale B)) :
    K * vfMidSyntheticRadialScale B -
        K * vfMidSyntheticRadialScale A <
      vfMidDyadicVFMass A B -
          (1 / 2 : ℝ) * vfMidDyadicPrefixSupply A A B +
          (1 / 2 : ℝ) * vfMidDyadicPrefixSurvivorMobiusMassReal A B := by
  have hnegabs :
      -|vfMidActualPrimeEndpointDefect A| ≤
        vfMidActualPrimeEndpointDefect A :=
    neg_abs_le _
  have hnegBound :
      -(K * vfMidSyntheticRadialScale A) ≤
        -|vfMidActualPrimeEndpointDefect A| :=
    neg_le_neg hAinside
  have hAlower :
      -(K * vfMidSyntheticRadialScale A) ≤
        vfMidActualPrimeEndpointDefect A :=
    hnegBound.trans hnegabs
  have hdiff :
      vfMidActualPrimeEndpointDefect B -
          vfMidActualPrimeEndpointDefect A <
        K * vfMidSyntheticRadialScale A -
          K * vfMidSyntheticRadialScale B := by
    linarith
  have htrack :=
    vfMidDyadicVFTrackingDefect_eq_neg_primeError_increment
      (A := A) (B := B) (by omega : 2 ≤ A) (by omega : 2 ≤ B) hAB
  have hdict :=
    vfMidDyadicVFTrackingDefect_eq_frozenWheel_add_half_moebius
      hA hAB hBA
  have htrack' :
      vfMidDyadicVFTrackingDefect A B =
        -(vfMidActualPrimeEndpointDefect B -
          vfMidActualPrimeEndpointDefect A) := by
    simpa [vfMidActualPrimeEndpointDefect] using htrack
  rw [htrack'] at hdict
  linarith

/-- **Minimal bad scale gives one of the two exact signed Mobius triggers.**

No sign of the escape is assumed.  The absolute radial violation is split only
at the last line into the lower-wall and upper-wall cases. -/
theorem vfMidActualPrimeFirstBadAt_forces_subdoublingMobiusTrigger
    {K : ℝ} {A B : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 3 ≤ A) (hABlt : A < B) (hBA : B ≤ 2 * A) :
    (K * vfMidSyntheticRadialScale B -
          K * vfMidSyntheticRadialScale A <
        vfMidDyadicVFMass A B -
          (1 / 2 : ℝ) * vfMidDyadicPrefixSupply A A B +
          (1 / 2 : ℝ) * vfMidDyadicPrefixSurvivorMobiusMassReal A B) ∨
    (vfMidDyadicVFMass A B -
          (1 / 2 : ℝ) * vfMidDyadicPrefixSupply A A B +
          (1 / 2 : ℝ) * vfMidDyadicPrefixSurvivorMobiusMassReal A B <
        K * vfMidSyntheticRadialScale A -
          K * vfMidSyntheticRadialScale B) := by
  have hAinside :=
    vfMidActualPrimeFirstBadAt_prior_inside
      hfirst (by omega : 2 ≤ A) hABlt
  have hbad := hfirst.1
  unfold VFMidSyntheticBadAt at hbad
  by_cases hsign : 0 ≤ vfMidActualPrimeEndpointDefect B
  · have hupper :
        K * vfMidSyntheticRadialScale B <
          vfMidActualPrimeEndpointDefect B := by
      simpa [abs_of_nonneg hsign] using hbad
    exact Or.inr
      (vfMidActualPrimeUpperEscape_forces_subdoublingMobiusTrigger
        hA hABlt.le hBA hAinside hupper)
  · have hnonpos : vfMidActualPrimeEndpointDefect B ≤ 0 :=
      le_of_not_ge hsign
    have hlower :
        vfMidActualPrimeEndpointDefect B <
          -(K * vfMidSyntheticRadialScale B) := by
      rw [abs_of_nonpos hnonpos] at hbad
      linarith
    exact Or.inl
      (vfMidActualPrimeLowerEscape_forces_subdoublingMobiusTrigger
        hA hABlt.le hBA hAinside hlower)

end RHLean.Analysis
