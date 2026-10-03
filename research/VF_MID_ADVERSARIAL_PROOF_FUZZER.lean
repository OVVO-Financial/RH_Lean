import Mathlib
import «research.VF_MID_RECURSIVE_SCALE_DESCENT»
import «research.VF_MID_VON_KOCH_BRIDGE»

/-!
# VF-mid adversarial proof fuzzer

This file is a logic audit for the direct VF radial-channel proof.

The goal is not to construct fake primes. It is to construct an explicit
synthetic endpoint-defect series which satisfies the weak structural statements
that are often invoked informally:

* exact block-to-endpoint recurrence;
* perfect left/right midpoint balance inside every block;
* the exact quadratic correlation/energy identity.

Nevertheless the synthetic series escapes every fixed radial channel

  |D_R| <= K R log R.

Thus none of those weak statements, alone or in any combination which holds for
this model, can prove the VF endpoint theorem.

The file then isolates the stronger arithmetic law which does kill the
countermodel: a channel-threatening bad scale must reproduce on an actual
strict recursive VF child scale. Since VF_MID_RECURSIVE_SCALE_DESCENT already
proves every such child has smaller square index, finite base control plus this
reproduction law rules out every bad scale by strong induction.

This is the intended proof fuzzer:

  weak local balance + recurrence         -- countermodel survives;
  strict bad-scale reproduction to child  -- countermodel dies;
  actual pi + reproduction                -- VF radial channel follows.

No probabilistic independence, Li approximation, PNT rate, or RH hypothesis is
used in the logical descent theorem.
-/

noncomputable section

namespace RHLean.Analysis

/-! ## 1. The radial scale and abstract containment -/

def vfMidSyntheticRadialScale (R : ℕ) : ℝ :=
  (R : ℝ) * Real.log (R : ℝ)

theorem vfMidSyntheticRadialScale_pos
    {R : ℕ} (hR : 2 ≤ R) :
    0 < vfMidSyntheticRadialScale R := by
  unfold vfMidSyntheticRadialScale
  have hR1 : (1 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 1 < R by omega)
  exact mul_pos (by positivity) (Real.log_pos hR1)

def VFMidSyntheticRadialBounded (D : ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ R : ℕ, 2 ≤ R →
      |D R| ≤ K * vfMidSyntheticRadialScale R

theorem vfMidActualRadialBounded_iff_squareEndpoint :
    VFMidSyntheticRadialBounded
        (fun R => vfMidPrimeError ((R : ℝ) ^ 2)) ↔
      VFMidSquareEndpointVonKochBoundedStatement := by
  constructor
  · rintro ⟨K, hK0, hK⟩
    refine ⟨K, hK0, ?_⟩
    intro R hR
    have h := hK R hR
    change |vfMidPrimeError ((R : ℝ) ^ 2)| ≤
      K * ((R : ℝ) * Real.log (R : ℝ)) at h
    calc
      |vfMidPrimeError ((R : ℝ) ^ 2)| ≤
          K * ((R : ℝ) * Real.log (R : ℝ)) := h
      _ = K * (R : ℝ) * Real.log (R : ℝ) := by ring
  · rintro ⟨K, hK0, hK⟩
    refine ⟨K, hK0, ?_⟩
    intro R hR
    have h := hK R hR
    change |vfMidPrimeError ((R : ℝ) ^ 2)| ≤
      K * (R : ℝ) * Real.log (R : ℝ) at h
    calc
      |vfMidPrimeError ((R : ℝ) ^ 2)| ≤
          K * (R : ℝ) * Real.log (R : ℝ) := h
      _ = K * ((R : ℝ) * Real.log (R : ℝ)) := by ring

/-! ## 2. Amplified radial countermodels -/

def VFMidAmplifierNonnegative (a : ℕ → ℝ) : Prop :=
  ∀ R : ℕ, 2 ≤ R → 0 ≤ a R

def VFMidAmplifierEscapesEveryConstant (a : ℕ → ℝ) : Prop :=
  ∀ K : ℝ, 0 ≤ K →
    ∃ R : ℕ, 2 ≤ R ∧ K < a R

def vfMidAmplifiedSyntheticDefect
    (a : ℕ → ℝ) (R : ℕ) : ℝ :=
  a R * vfMidSyntheticRadialScale R

theorem not_vfMidSyntheticRadialBounded_of_unboundedAmplifier
    (a : ℕ → ℝ)
    (ha0 : VFMidAmplifierNonnegative a)
    (haUnbounded : VFMidAmplifierEscapesEveryConstant a) :
    ¬ VFMidSyntheticRadialBounded (vfMidAmplifiedSyntheticDefect a) := by
  intro hbound
  rcases hbound with ⟨K, hK0, hK⟩
  obtain ⟨R, hR, hKR⟩ := haUnbounded K hK0
  have hscale : 0 < vfMidSyntheticRadialScale R :=
    vfMidSyntheticRadialScale_pos hR
  have haR0 : 0 ≤ a R := ha0 R hR
  have hstrict :
      K * vfMidSyntheticRadialScale R <
        a R * vfMidSyntheticRadialScale R :=
    mul_lt_mul_of_pos_right hKR hscale
  have habs :
      |vfMidAmplifiedSyntheticDefect a R| =
        a R * vfMidSyntheticRadialScale R := by
    rw [vfMidAmplifiedSyntheticDefect,
      abs_of_nonneg (mul_nonneg haR0 hscale.le)]
  have hupper := hK R hR
  rw [habs] at hupper
  linarith

def vfMidLinearAmplifier (R : ℕ) : ℝ := (R : ℝ)

theorem vfMidLinearAmplifier_nonnegative :
    VFMidAmplifierNonnegative vfMidLinearAmplifier := by
  intro R _hR
  simp [vfMidLinearAmplifier]

theorem vfMidLinearAmplifier_escapesEveryConstant :
    VFMidAmplifierEscapesEveryConstant vfMidLinearAmplifier := by
  intro K hK0
  obtain ⟨R : ℕ, hRnat⟩ := exists_nat_gt (K + 2)
  have hRreal : K + 2 < (R : ℝ) := by
    exact_mod_cast hRnat
  have h2Rreal : (2 : ℝ) < (R : ℝ) := by
    linarith
  have h2R : 2 ≤ R := by
    have : 2 < R := by exact_mod_cast h2Rreal
    omega
  refine ⟨R, h2R, ?_⟩
  simp only [vfMidLinearAmplifier]
  linarith

def vfMidLogicAdversaryDefect (R : ℕ) : ℝ :=
  vfMidAmplifiedSyntheticDefect vfMidLinearAmplifier R

theorem vfMidLogicAdversary_not_radialBounded :
    ¬ VFMidSyntheticRadialBounded vfMidLogicAdversaryDefect := by
  exact
    not_vfMidSyntheticRadialBounded_of_unboundedAmplifier
      vfMidLinearAmplifier
      vfMidLinearAmplifier_nonnegative
      vfMidLinearAmplifier_escapesEveryConstant

/-! ## 3. The adversary passes weak recurrence and spatial-balance tests -/

def vfMidSyntheticBandError (D : ℕ → ℝ) (R : ℕ) : ℝ :=
  D (R + 1) - D R

theorem vfMidSyntheticEndpoint_recurrence
    (D : ℕ → ℝ) (R : ℕ) :
    D (R + 1) = D R + vfMidSyntheticBandError D R := by
  unfold vfMidSyntheticBandError
  ring

def vfMidSyntheticLeftHalfError (D : ℕ → ℝ) (R : ℕ) : ℝ :=
  vfMidSyntheticBandError D R / 2

def vfMidSyntheticRightHalfError (D : ℕ → ℝ) (R : ℕ) : ℝ :=
  vfMidSyntheticBandError D R / 2

theorem vfMidSynthetic_halves_reassemble
    (D : ℕ → ℝ) (R : ℕ) :
    vfMidSyntheticLeftHalfError D R +
        vfMidSyntheticRightHalfError D R =
      vfMidSyntheticBandError D R := by
  unfold vfMidSyntheticLeftHalfError vfMidSyntheticRightHalfError
  ring

theorem vfMidSynthetic_midpointBias_eq_zero
    (D : ℕ → ℝ) (R : ℕ) :
    vfMidSyntheticLeftHalfError D R -
        vfMidSyntheticRightHalfError D R = 0 := by
  unfold vfMidSyntheticLeftHalfError vfMidSyntheticRightHalfError
  ring

theorem vfMidSynthetic_energy_step
    (D : ℕ → ℝ) (R : ℕ) :
    D (R + 1) ^ 2 - D R ^ 2 =
      2 * D R * vfMidSyntheticBandError D R +
        vfMidSyntheticBandError D R ^ 2 := by
  rw [vfMidSyntheticEndpoint_recurrence D R]
  ring

theorem vfMidLogicAdversary_passes_balance_but_escapes :
    (∀ R : ℕ,
      vfMidSyntheticLeftHalfError vfMidLogicAdversaryDefect R -
        vfMidSyntheticRightHalfError vfMidLogicAdversaryDefect R = 0) ∧
    (∀ R : ℕ,
      vfMidLogicAdversaryDefect (R + 1) =
        vfMidLogicAdversaryDefect R +
          vfMidSyntheticBandError vfMidLogicAdversaryDefect R) ∧
    ¬ VFMidSyntheticRadialBounded vfMidLogicAdversaryDefect := by
  refine ⟨?_, ?_, vfMidLogicAdversary_not_radialBounded⟩
  · intro R
    exact vfMidSynthetic_midpointBias_eq_zero vfMidLogicAdversaryDefect R
  · intro R
    exact vfMidSyntheticEndpoint_recurrence vfMidLogicAdversaryDefect R

/-! ## 4. The exact stronger law that kills an escaping series -/

def VFMidSyntheticBadAt
    (D : ℕ → ℝ) (K : ℝ) (R : ℕ) : Prop :=
  K * vfMidSyntheticRadialScale R < |D R|

theorem vfMidNoSyntheticBadScale_of_recursiveReproduction
    (D : ℕ → ℝ) (K : ℝ)
    (hsmall :
      ∀ R : ℕ, R < 7 → ¬ VFMidSyntheticBadAt D K R)
    (hdesc :
      ∀ R : ℕ, 7 ≤ R → VFMidSyntheticBadAt D K R →
        ∃ S : ℕ,
          VFMidRecursiveScaleStep R S ∧
            VFMidSyntheticBadAt D K S) :
    ∀ R : ℕ, ¬ VFMidSyntheticBadAt D K R := by
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
      intro hbad
      by_cases hR7 : R < 7
      · exact hsmall R hR7 hbad
      · have hR : 7 ≤ R := by omega
        obtain ⟨S, hstep, hbadS⟩ := hdesc R hR hbad
        exact ih S (vfMidRecursiveScaleStep_lt hstep) hbadS

theorem vfMidSyntheticRadialBounded_of_recursiveReproduction
    (D : ℕ → ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hsmall :
      ∀ R : ℕ, R < 7 → ¬ VFMidSyntheticBadAt D K R)
    (hdesc :
      ∀ R : ℕ, 7 ≤ R → VFMidSyntheticBadAt D K R →
        ∃ S : ℕ,
          VFMidRecursiveScaleStep R S ∧
            VFMidSyntheticBadAt D K S) :
    VFMidSyntheticRadialBounded D := by
  refine ⟨K, hK0, ?_⟩
  intro R hR
  have hno :=
    vfMidNoSyntheticBadScale_of_recursiveReproduction
      D K hsmall hdesc R
  exact le_of_not_gt hno

theorem vfMidSquareEndpointVonKochBounded_of_recursiveEscapeReproduction
    (K : ℝ) (hK0 : 0 ≤ K)
    (hsmall :
      ∀ R : ℕ, R < 7 →
        ¬ VFMidSyntheticBadAt
          (fun S => vfMidPrimeError ((S : ℝ) ^ 2)) K R)
    (hdesc :
      ∀ R : ℕ, 7 ≤ R →
        VFMidSyntheticBadAt
          (fun S => vfMidPrimeError ((S : ℝ) ^ 2)) K R →
        ∃ S : ℕ,
          VFMidRecursiveScaleStep R S ∧
            VFMidSyntheticBadAt
              (fun T => vfMidPrimeError ((T : ℝ) ^ 2)) K S) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  rw [← vfMidActualRadialBounded_iff_squareEndpoint]
  exact
    vfMidSyntheticRadialBounded_of_recursiveReproduction
      (fun R => vfMidPrimeError ((R : ℝ) ^ 2))
      K hK0 hsmall hdesc

theorem vfMidLogicAdversary_reproduction_must_fail
    (K : ℝ) (hK0 : 0 ≤ K)
    (hsmall :
      ∀ R : ℕ, R < 7 →
        ¬ VFMidSyntheticBadAt vfMidLogicAdversaryDefect K R) :
    ¬ (∀ R : ℕ, 7 ≤ R →
        VFMidSyntheticBadAt vfMidLogicAdversaryDefect K R →
          ∃ S : ℕ,
            VFMidRecursiveScaleStep R S ∧
              VFMidSyntheticBadAt vfMidLogicAdversaryDefect K S) := by
  intro hdesc
  have hbounded :
      VFMidSyntheticRadialBounded vfMidLogicAdversaryDefect :=
    vfMidSyntheticRadialBounded_of_recursiveReproduction
      vfMidLogicAdversaryDefect K hK0 hsmall hdesc
  exact vfMidLogicAdversary_not_radialBounded hbounded

end RHLean.Analysis
