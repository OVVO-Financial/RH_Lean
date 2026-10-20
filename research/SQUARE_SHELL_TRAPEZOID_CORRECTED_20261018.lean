import Mathlib

/-!
# Exact trapezoidal square-shell smoothing: finite identities and energy budget

All shells use the half-open integer convention `(r^2+t, (r+1)^2+t]`.
The unshifted Mobius sum agrees with the traditional *open* square shell,
because Mobius vanishes at nontrivial squares.  With this convention the
right endpoint of one shell is the left endpoint of the next.

The core results are universal finite-algebra statements about an arbitrary
integer-indexed prefix primitive `P`.  Its 1-Lipschitz hypothesis is the
elementary bounded-atom property of the Mobius prefix, not a prime density
estimate.  The complete smoothed second moment is *not* bounded in this file:
the corresponding signed analytic hypothesis is an explicitly open Prop.

No Stieltjes integral, zero-frequency cancellation, RH hypothesis, admitted
lemma, or external 7/8 theorem is used.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- The centered shift index `k = 0,...,2T` represents `t = k-T`. -/
def shellTrapezoidShift (T k : ℕ) : ℤ :=
  (k : ℤ) - (T : ℤ)

/-- Uniform average over the `2T+1` integer translations. -/
def shellTrapezoidMean (T : ℕ) (g : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range (2 * T + 1), g k) / ((2 * T + 1 : ℕ) : ℝ)

/-- The square endpoint interpreted in the integer clock. -/
def shellTrapezoidSquare (r : ℕ) : ℤ := (r : ℤ) ^ 2

/-- Any prefix primitive produces a translated half-open shell increment. -/
def shellTrapezoidShifted
    (P : ℤ → ℝ) (r T k : ℕ) : ℝ :=
  P (shellTrapezoidSquare (r + 1) + shellTrapezoidShift T k) -
    P (shellTrapezoidSquare r + shellTrapezoidShift T k)

/-- Untranslated shell increment; equal to a Mobius shell sum for its prefix. -/
def shellTrapezoidSharp (P : ℤ → ℝ) (r : ℕ) : ℝ :=
  P (shellTrapezoidSquare (r + 1)) - P (shellTrapezoidSquare r)

/-- Genuine finite translation average, not a Li-density proxy. -/
def shellTrapezoidSmoothed
    (P : ℤ → ℝ) (r T : ℕ) : ℝ :=
  shellTrapezoidMean T (shellTrapezoidShifted P r T)

/-- Signed sawtooth at one square endpoint.  The two sides have opposite
signs after the prefix increments are expanded, unlike an unsigned triangular
collar. -/
def shellTrapezoidSaw
    (P : ℤ → ℝ) (x : ℤ) (T : ℕ) : ℝ :=
  shellTrapezoidMean T (fun k =>
    P (x + shellTrapezoidShift T k) - P x)

/-- Sharp minus smoothed: *one* endpoint sawtooth difference. -/
def shellTrapezoidResidual
    (P : ℤ → ℝ) (r T : ℕ) : ℝ :=
  shellTrapezoidSharp P r - shellTrapezoidSmoothed P r T

theorem shellTrapezoidMean_sub
    (T : ℕ) (f g : ℕ → ℝ) :
    shellTrapezoidMean T (fun k => f k - g k) =
      shellTrapezoidMean T f - shellTrapezoidMean T g := by
  unfold shellTrapezoidMean
  rw [Finset.sum_sub_distrib]
  ring

theorem shellTrapezoidMean_const (T : ℕ) (a : ℝ) :
    shellTrapezoidMean T (fun _ => a) = a := by
  have hN : (((2 * T + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  simp only [shellTrapezoidMean, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  field_simp [hN]

theorem shellTrapezoidSaw_eq_mean_sub_center
    (P : ℤ → ℝ) (x : ℤ) (T : ℕ) :
    shellTrapezoidSaw P x T =
      shellTrapezoidMean T (fun k =>
        P (x + shellTrapezoidShift T k)) - P x := by
  unfold shellTrapezoidSaw
  rw [shellTrapezoidMean_sub, shellTrapezoidMean_const]

/-- **Exact telescoping**: no deleted square-site term, no boundary
approximation, and no unproved analytic estimate. -/
theorem shellTrapezoidResidual_eq_saw_difference
    (P : ℤ → ℝ) (r T : ℕ) :
    shellTrapezoidResidual P r T =
      shellTrapezoidSaw P (shellTrapezoidSquare r) T -
      shellTrapezoidSaw P (shellTrapezoidSquare (r + 1)) T := by
  unfold shellTrapezoidResidual shellTrapezoidSharp shellTrapezoidSmoothed
    shellTrapezoidShifted
  rw [shellTrapezoidMean_sub]
  rw [shellTrapezoidSaw_eq_mean_sub_center,
      shellTrapezoidSaw_eq_mean_sub_center]
  ring

/-- The centered finite translation window is contained in `[-T,T]`. -/
theorem shellTrapezoidShift_abs_le
    (T k : ℕ) (hk : k ∈ Finset.range (2 * T + 1)) :
    |shellTrapezoidShift T k| ≤ (T : ℤ) := by
  have hk' : k ≤ 2 * T := by
    have := Finset.mem_range.mp hk
    omega
  have hki : (k : ℤ) ≤ 2 * (T : ℤ) := by exact_mod_cast hk'
  have hk0 : 0 ≤ (k : ℤ) := Int.natCast_nonneg _
  unfold shellTrapezoidShift
  apply abs_le.mpr
  constructor <;> omega

/-- This is a purely deterministic property.  The actual Mobius prefix has it
because each of its individual integer increments belongs to `{-1,0,1}`. -/
def ShellTrapezoidUnitLipschitz (P : ℤ → ℝ) : Prop :=
  ∀ x y : ℤ, |P x - P y| ≤ |(((x - y : ℤ) : ℝ))|

theorem shellTrapezoidShifted_abs_le_radius
    (P : ℤ → ℝ) (hLip : ShellTrapezoidUnitLipschitz P)
    (x : ℤ) (T k : ℕ) (hk : k ∈ Finset.range (2 * T + 1)) :
    |P (x + shellTrapezoidShift T k) - P x| ≤ (T : ℝ) := by
  have hshift : |((shellTrapezoidShift T k : ℤ) : ℝ)| ≤ (T : ℝ) := by
    exact_mod_cast shellTrapezoidShift_abs_le T k hk
  calc
    |P (x + shellTrapezoidShift T k) - P x| ≤
        |((((x + shellTrapezoidShift T k) - x : ℤ) : ℝ))| :=
      hLip _ _
    _ = |((shellTrapezoidShift T k : ℤ) : ℝ)| := by simp
    _ ≤ (T : ℝ) := hshift

/-- The elementary per-endpoint sawtooth bound, using no signed cancellation.
The sharper `T/2` follows from triangular weights and square-site vanishing;
the present `T` bound is enough for the exact `H*T^2` energy exponent. -/
theorem shellTrapezoidSaw_abs_le_radius
    (P : ℤ → ℝ) (hLip : ShellTrapezoidUnitLipschitz P)
    (x : ℤ) (T : ℕ) :
    |shellTrapezoidSaw P x T| ≤ (T : ℝ) := by
  have hN : (0 : ℝ) < (((2 * T + 1 : ℕ) : ℝ)) := by positivity
  have hsum :
      |∑ k ∈ Finset.range (2 * T + 1),
          (P (x + shellTrapezoidShift T k) - P x)| ≤
        (((2 * T + 1 : ℕ) : ℝ)) * (T : ℝ) := by
    calc
      |∑ k ∈ Finset.range (2 * T + 1),
          (P (x + shellTrapezoidShift T k) - P x)| ≤
          ∑ k ∈ Finset.range (2 * T + 1),
            |P (x + shellTrapezoidShift T k) - P x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range (2 * T + 1), (T : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact shellTrapezoidShifted_abs_le_radius P hLip x T k hk
      _ = (((2 * T + 1 : ℕ) : ℝ)) * (T : ℝ) := by simp
  unfold shellTrapezoidSaw shellTrapezoidMean
  rw [abs_div, abs_of_pos hN]
  exact (div_le_iff₀ hN).2 (by simpa [mul_comm] using! hsum)

theorem shellTrapezoidResidual_sq_le
    (P : ℤ → ℝ) (hLip : ShellTrapezoidUnitLipschitz P)
    (r T : ℕ) :
    shellTrapezoidResidual P r T ^ 2 ≤ 4 * (T : ℝ) ^ 2 := by
  have hleft := shellTrapezoidSaw_abs_le_radius
    P hLip (shellTrapezoidSquare r) T
  have hright := shellTrapezoidSaw_abs_le_radius
    P hLip (shellTrapezoidSquare (r + 1)) T
  have htri :
      |shellTrapezoidSaw P (shellTrapezoidSquare r) T -
          shellTrapezoidSaw P (shellTrapezoidSquare (r + 1)) T| ≤
        2 * (T : ℝ) := by
    have hab := abs_sub_le
      (shellTrapezoidSaw P (shellTrapezoidSquare r) T)
      0 (shellTrapezoidSaw P (shellTrapezoidSquare (r + 1)) T)
    simp only [sub_zero, zero_sub, abs_neg] at hab
    linarith
  have hsq :=
    (sq_le_sq₀ (abs_nonneg _)
      (by positivity : 0 ≤ 2 * (T : ℝ))).2 htri
  rw [shellTrapezoidResidual_eq_saw_difference]
  rw [sq_abs] at hsq
  nlinarith [hsq]

/-- Second moment over the `H` consecutive square shells `H <= r < 2H`. -/
def shellTrapezoidEnergy (f : ℕ → ℝ) (H : ℕ) : ℝ :=
  ∑ k ∈ Finset.range H, f (H + k) ^ 2

/-- **Unconditional deterministic collar budget** for every unit-Lipschitz
primitive. At `T=floor(H^(2/3))`, the paper exponent is `H^(7/3)`. -/
theorem shellTrapezoidResidual_energy_le
    (P : ℤ → ℝ) (hLip : ShellTrapezoidUnitLipschitz P)
    (H T : ℕ) :
    shellTrapezoidEnergy (fun r => shellTrapezoidResidual P r T) H ≤
      4 * (H : ℝ) * (T : ℝ) ^ 2 := by
  unfold shellTrapezoidEnergy
  calc
    (∑ k ∈ Finset.range H, shellTrapezoidResidual P (H + k) T ^ 2) ≤
        ∑ _k ∈ Finset.range H, 4 * (T : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact shellTrapezoidResidual_sq_le P hLip (H + k) T
    _ = 4 * (H : ℝ) * (T : ℝ) ^ 2 := by
      simp
      ring

/-- Elementary energy comparison, with no omitted cross term. -/
theorem shellTrapezoidEnergy_add_le
    (f g : ℕ → ℝ) (H : ℕ) :
    shellTrapezoidEnergy (fun r => f r + g r) H ≤
      2 * shellTrapezoidEnergy f H + 2 * shellTrapezoidEnergy g H := by
  unfold shellTrapezoidEnergy
  calc
    (∑ k ∈ Finset.range H, (f (H + k) + g (H + k)) ^ 2) ≤
        ∑ k ∈ Finset.range H,
          (2 * f (H + k) ^ 2 + 2 * g (H + k) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      nlinarith [sq_nonneg (f (H + k) - g (H + k))]
    _ = 2 * (∑ k ∈ Finset.range H, f (H + k) ^ 2) +
        2 * (∑ k ∈ Finset.range H, g (H + k) ^ 2) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum]

def shellTrapezoidSharpEnergy (P : ℤ → ℝ) (H : ℕ) : ℝ :=
  shellTrapezoidEnergy (shellTrapezoidSharp P) H

def shellTrapezoidSmoothedEnergy (P : ℤ → ℝ) (H T : ℕ) : ℝ :=
  shellTrapezoidEnergy (fun r => shellTrapezoidSmoothed P r T) H

/-- Sharp energy controlled by *the complete smoothed* energy and the collar. -/
theorem shellTrapezoidSharpEnergy_le_smoothed
    (P : ℤ → ℝ) (H T : ℕ) :
    shellTrapezoidSharpEnergy P H ≤
      2 * shellTrapezoidSmoothedEnergy P H T +
        2 * shellTrapezoidEnergy (fun r => shellTrapezoidResidual P r T) H := by
  have hfun : shellTrapezoidSharp P =
      (fun r => shellTrapezoidSmoothed P r T +
        shellTrapezoidResidual P r T) := by
    funext r
    unfold shellTrapezoidResidual
    ring
  unfold shellTrapezoidSharpEnergy shellTrapezoidSmoothedEnergy
  rw [hfun]
  exact shellTrapezoidEnergy_add_le _ _ H

/-- Conversely, complete smoothed energy is controlled by sharp plus collar. -/
theorem shellTrapezoidSmoothedEnergy_le_sharp
    (P : ℤ → ℝ) (H T : ℕ) :
    shellTrapezoidSmoothedEnergy P H T ≤
      2 * shellTrapezoidSharpEnergy P H +
        2 * shellTrapezoidEnergy (fun r => shellTrapezoidResidual P r T) H := by
  have hfun : (fun r => shellTrapezoidSmoothed P r T) =
      (fun r => shellTrapezoidSharp P r -
        shellTrapezoidResidual P r T) := by
    funext r
    unfold shellTrapezoidResidual
    ring
  unfold shellTrapezoidSharpEnergy shellTrapezoidSmoothedEnergy
  rw [hfun]
  have h := shellTrapezoidEnergy_add_le
    (shellTrapezoidSharp P)
    (fun r => -shellTrapezoidResidual P r T) H
  have hneg :
      shellTrapezoidEnergy (fun r => -shellTrapezoidResidual P r T) H =
        shellTrapezoidEnergy (fun r => shellTrapezoidResidual P r T) H := by
    unfold shellTrapezoidEnergy
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hneg] at h
  simpa only [sub_eq_add_neg] using! h

/-- Exact quantitative equivalence in the useful form: any envelope `B H`
which pays `H*(T H)^2` pays the sharp moment iff it pays the complete smoothed
moment. In particular the `H^(7/3+epsilon)` envelope works once the elementary
choice `T=floor(H^(2/3))` is instantiated. This is NOT a proof of either norm. -/
def ShellTrapezoidSharpBounded (P : ℤ → ℝ) (B : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, 1 ≤ H →
    shellTrapezoidSharpEnergy P H ≤ C * B H

def ShellTrapezoidSmoothedBounded
    (P : ℤ → ℝ) (T : ℕ → ℕ) (B : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, 1 ≤ H →
    shellTrapezoidSmoothedEnergy P H (T H) ≤ C * B H

theorem shellTrapezoidSharpBounded_iff_smoothedBounded
    (P : ℤ → ℝ) (hLip : ShellTrapezoidUnitLipschitz P)
    (T : ℕ → ℕ) (B : ℕ → ℝ)
    (hBudget : ∀ H : ℕ, 1 ≤ H →
      (H : ℝ) * (T H : ℝ) ^ 2 ≤ B H) :
    ShellTrapezoidSharpBounded P B ↔
      ShellTrapezoidSmoothedBounded P T B := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨2 * C + 8, by positivity, ?_⟩
    intro H hH
    have hcomp := shellTrapezoidSmoothedEnergy_le_sharp P H (T H)
    have hcoll := shellTrapezoidResidual_energy_le P hLip H (T H)
    have hbound' := hbound H hH
    have hbudget' := hBudget H hH
    nlinarith
  · rintro ⟨C, hC, hbound⟩
    refine ⟨2 * C + 8, by positivity, ?_⟩
    intro H hH
    have hcomp := shellTrapezoidSharpEnergy_le_smoothed P H (T H)
    have hcoll := shellTrapezoidResidual_energy_le P hLip H (T H)
    have hbound' := hbound H hH
    have hbudget' := hBudget H hH
    nlinarith

/-- The complete smoothed shell energy TARGET is a named Prop, not an axiom or
an independently established arithmetic input. It is equivalent to the sharp
target after the deterministic collar payment. A future source-level theorem
must PROVE this target from genuinely narrower signed arithmetic information.
No estimate on C and the high off-diagonal alone is asserted here. -/
def ShellTrapezoidCompleteSmoothedEnergyTarget
    (P : ℤ → ℝ) (T : ℕ → ℕ) (B : ℕ → ℝ) : Prop :=
  ShellTrapezoidSmoothedBounded P T B

/-- A logically conditional consumer only: this does not supply the target
and is not itself an independent dispersion mechanism. -/
theorem shellTrapezoidSharpBound_of_completeSmoothedEnergyTarget
    (P : ℤ → ℝ) (hLip : ShellTrapezoidUnitLipschitz P)
    (T : ℕ → ℕ) (B : ℕ → ℝ)
    (hBudget : ∀ H : ℕ, 1 ≤ H →
      (H : ℝ) * (T H : ℝ) ^ 2 ≤ B H)
    (hSigned : ShellTrapezoidCompleteSmoothedEnergyTarget P T B) :
    ShellTrapezoidSharpBounded P B :=
  (shellTrapezoidSharpBounded_iff_smoothedBounded P hLip T B hBudget).2 hSigned

#print axioms shellTrapezoidResidual_eq_saw_difference
#print axioms shellTrapezoidResidual_energy_le
#print axioms shellTrapezoidSharpBounded_iff_smoothedBounded
#print axioms shellTrapezoidSharpBound_of_completeSmoothedEnergyTarget

end RHLean.Analysis
