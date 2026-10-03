import Mathlib
import «research.VF_MID_LITERAL_BLOCK_CROSSING»

/-!
# VF-mid corner channels

This file formalizes the geometric channel obtained by linearly connecting
corners of the VF-mid square-block staircase.

There are two layers.

1. The literal adjacent-corner channel is exactly the black-line geometry:
   on [R^2,(R+1)^2], the upper line joins F_R to F_(R+1), while the lower
   line joins F_(R-1) to F_R, where F_R = vfMidFinishedMass R.

2. A widened outer-corner channel uses genuine VF corners displaced by L_R
   blocks on each side.  The canonical lag is

       L_R = min (R/2) floor(A * log(R)^2).

   One VF block has local mass O(R/log R), so O(log(R)^2) genuine VF blocks
   provide O(R log R) width.  The widening is therefore intrinsic to the VF
   staircase rather than an externally imposed radial interval.

The analytic geometry is proved unconditionally.  The sole arithmetic input
left by this route is containment of the honest prime-count endpoint between
the two canonical outer VF corners.
-/

noncomputable section

namespace RHLean.Analysis

/-! ## Literal adjacent-corner channel -/

/-- Affine coordinate of x in the square block [R^2,(R+1)^2]. -/
def vfMidCornerParameter (R : ℕ) (x : ℝ) : ℝ :=
  (x - (R : ℝ) ^ 2) / (2 * (R : ℝ) + 1)

/-- Upper black line: join the upper VF corners F_R and F_(R+1). -/
def vfMidUpperCornerChannel (R : ℕ) (x : ℝ) : ℝ :=
  let t := vfMidCornerParameter R x
  (1 - t) * vfMidFinishedMass R +
    t * vfMidFinishedMass (R + 1)

/-- Lower black line: join the lower VF corners F_(R-1) and F_R. -/
def vfMidLowerCornerChannel (R : ℕ) (x : ℝ) : ℝ :=
  let t := vfMidCornerParameter R x
  (1 - t) * vfMidFinishedMass (R - 1) +
    t * vfMidFinishedMass R

/-- Phase-language alias: the lower black line is the one-block lagged VF
corner chain F_(R-1) -> F_R. -/
abbrev vfMidLaggedCornerChannel := vfMidLowerCornerChannel

/-- Phase-language alias: the upper black line is the one-block advanced VF
corner chain F_R -> F_(R+1). -/
abbrev vfMidAdvancedCornerChannel := vfMidUpperCornerChannel

@[simp] theorem vfMidCornerParameter_left (R : ℕ) :
    vfMidCornerParameter R ((R : ℝ) ^ 2) = 0 := by
  simp [vfMidCornerParameter]

@[simp] theorem vfMidCornerParameter_right (R : ℕ) :
    vfMidCornerParameter R (((R + 1 : ℕ) : ℝ) ^ 2) = 1 := by
  unfold vfMidCornerParameter
  have hden : 2 * (R : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp [hden]
  ring

/-- Cast-normalized form used after Lean pushes the successor cast through
arithmetic expressions. -/
@[simp] theorem vfMidCornerParameter_right_cast (R : ℕ) :
    vfMidCornerParameter R (((R : ℝ) + 1) ^ 2) = 1 := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (vfMidCornerParameter_right R)

/-- Prime count at a real square endpoint is exactly the natural prime count
at the corresponding integer square. -/
@[simp] theorem vfMidPrimeCount_sq_exact (R : ℕ) :
    vfMidPrimeCount ((R : ℝ) ^ 2) =
      (Nat.primeCounting (R ^ 2) : ℝ) := by
  have hfloor : ⌊(R : ℝ) ^ 2⌋₊ = R ^ 2 := by
    rw [show (R : ℝ) ^ 2 = ((R ^ 2 : ℕ) : ℝ) by norm_num]
    exact Nat.floor_natCast (R ^ 2)
  unfold vfMidPrimeCount
  rw [hfloor]

theorem vfMidCornerParameter_mem_unit
    {R : ℕ} {x : ℝ}
    (hxl : (R : ℝ) ^ 2 ≤ x)
    (hxu : x ≤ (((R + 1 : ℕ) : ℝ) ^ 2)) :
    0 ≤ vfMidCornerParameter R x ∧
      vfMidCornerParameter R x ≤ 1 := by
  have hden : 0 < 2 * (R : ℝ) + 1 := by positivity
  constructor
  · unfold vfMidCornerParameter
    exact div_nonneg (sub_nonneg.mpr hxl) hden.le
  · unfold vfMidCornerParameter
    rw [div_le_one hden]
    push_cast at hxu
    nlinarith

@[simp] theorem vfMidUpperCornerChannel_left (R : ℕ) :
    vfMidUpperCornerChannel R ((R : ℝ) ^ 2) =
      vfMidFinishedMass R := by
  simp [vfMidUpperCornerChannel]

@[simp] theorem vfMidUpperCornerChannel_right (R : ℕ) :
    vfMidUpperCornerChannel R (((R + 1 : ℕ) : ℝ) ^ 2) =
      vfMidFinishedMass (R + 1) := by
  simp only [vfMidUpperCornerChannel, Nat.cast_add, Nat.cast_one]
  rw [vfMidCornerParameter_right_cast]
  ring

@[simp] theorem vfMidLowerCornerChannel_left (R : ℕ) :
    vfMidLowerCornerChannel R ((R : ℝ) ^ 2) =
      vfMidFinishedMass (R - 1) := by
  simp [vfMidLowerCornerChannel]

@[simp] theorem vfMidLowerCornerChannel_right (R : ℕ) :
    vfMidLowerCornerChannel R (((R + 1 : ℕ) : ℝ) ^ 2) =
      vfMidFinishedMass R := by
  simp only [vfMidLowerCornerChannel, Nat.cast_add, Nat.cast_one]
  rw [vfMidCornerParameter_right_cast]
  ring

/-- Cast-normalized successor-square forms used after simplification. -/
@[simp] theorem vfMidUpperCornerChannel_right_cast (R : ℕ) :
    vfMidUpperCornerChannel R (((R : ℝ) + 1) ^ 2) =
      vfMidFinishedMass (R + 1) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (vfMidUpperCornerChannel_right R)

@[simp] theorem vfMidLowerCornerChannel_right_cast (R : ℕ) :
    vfMidLowerCornerChannel R (((R : ℝ) + 1) ^ 2) =
      vfMidFinishedMass R := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (vfMidLowerCornerChannel_right R)

@[simp] theorem vfMidPrimeCount_succ_sq_exact (R : ℕ) :
    vfMidPrimeCount (((R : ℝ) + 1) ^ 2) =
      (Nat.primeCounting ((R + 1) ^ 2) : ℝ) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (vfMidPrimeCount_sq_exact (R + 1))

/-- Exact black-channel width: a convex combination of the two neighboring
VF band masses. -/
theorem vfMidCornerChannel_width
    (R : ℕ) (hR : 3 ≤ R) (x : ℝ) :
    vfMidUpperCornerChannel R x - vfMidLowerCornerChannel R x =
      (1 - vfMidCornerParameter R x) * vfMidBandMass (R - 1) +
        vfMidCornerParameter R x * vfMidBandMass R := by
  have hpred : 2 ≤ R - 1 := by omega
  have hsPred := vfMidFinishedMass_succ (R := R - 1) hpred
  have hpredSucc : R - 1 + 1 = R := by omega
  rw [hpredSucc] at hsPred
  have hs := vfMidFinishedMass_succ (R := R) (by omega : 2 ≤ R)
  have hdiffPred :
      vfMidFinishedMass R - vfMidFinishedMass (R - 1) =
        vfMidBandMass (R - 1) := by
    linarith
  have hdiff :
      vfMidFinishedMass (R + 1) - vfMidFinishedMass R =
        vfMidBandMass R := by
    linarith
  unfold vfMidUpperCornerChannel vfMidLowerCornerChannel
  dsimp
  calc
    (1 - vfMidCornerParameter R x) * vfMidFinishedMass R +
          vfMidCornerParameter R x * vfMidFinishedMass (R + 1) -
        ((1 - vfMidCornerParameter R x) * vfMidFinishedMass (R - 1) +
          vfMidCornerParameter R x * vfMidFinishedMass R)
        =
      (1 - vfMidCornerParameter R x) *
          (vfMidFinishedMass R - vfMidFinishedMass (R - 1)) +
        vfMidCornerParameter R x *
          (vfMidFinishedMass (R + 1) - vfMidFinishedMass R) := by
            ring
    _ = (1 - vfMidCornerParameter R x) * vfMidBandMass (R - 1) +
          vfMidCornerParameter R x * vfMidBandMass R := by
            rw [hdiffPred, hdiff]

/-- Pathwise inclusion of the prime staircase in the literal black channel
on one square block. -/
def VFMidCornerChannelContainsPrime (R : ℕ) : Prop :=
  ∀ x : ℝ,
    (R : ℝ) ^ 2 ≤ x →
    x ≤ (((R + 1 : ℕ) : ℝ) ^ 2) →
      vfMidLowerCornerChannel R x ≤ vfMidPrimeCount x ∧
        vfMidPrimeCount x ≤ vfMidUpperCornerChannel R x

/-- Literal channel inclusion forces the existing integer VF level to be
captured in the same square block. -/
theorem vfMidIntegerBlockCaptured_of_cornerChannel
    (R : ℕ) (hR : 2 ≤ R)
    (hchan : VFMidCornerChannelContainsPrime R) :
    VFMidIntegerBlockCaptured R := by
  have hsqNat : R ^ 2 ≤ (R + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hsq :
      (R : ℝ) ^ 2 ≤ (((R + 1 : ℕ) : ℝ) ^ 2) := by
    exact_mod_cast hsqNat
  have hleft :=
    hchan ((R : ℝ) ^ 2) le_rfl hsq
  have hright :=
    hchan (((R + 1 : ℕ) : ℝ) ^ 2) hsq le_rfl
  have hpiF :
      (Nat.primeCounting (R ^ 2) : ℝ) ≤ vfMidFinishedMass R := by
    simpa using hleft.2
  have hlow :
      Nat.primeCounting (R ^ 2) ≤ vfMidIntegerBlockLevel R := by
    unfold vfMidIntegerBlockLevel
    exact Nat.le_floor hpiF
  have hFpi :
      vfMidFinishedMass R ≤
        (Nat.primeCounting ((R + 1) ^ 2) : ℝ) := by
    simpa using hright.1
  have hKpi :
      (vfMidIntegerBlockLevel R : ℝ) ≤
        (Nat.primeCounting ((R + 1) ^ 2) : ℝ) :=
    (vfMidIntegerBlockLevel_cast_le R).trans hFpi
  have hupp :
      vfMidIntegerBlockLevel R ≤ Nat.primeCounting ((R + 1) ^ 2) := by
    exact_mod_cast hKpi
  exact ⟨hlow, hupp⟩

/-- Universal literal black-channel inclusion. -/
def VFMidCornerChannelContainmentStatement : Prop :=
  ∀ R : ℕ, 2 ≤ R → VFMidCornerChannelContainsPrime R

/-- The literal channel is a strong sufficient condition for the direct
square-endpoint target. -/
theorem vfMidSquareEndpointVonKochBounded_of_cornerChannel
    (hchan : VFMidCornerChannelContainmentStatement) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  apply vfMidSquareEndpointVonKochBounded_of_integerBlockCapture
  intro R hR
  exact vfMidIntegerBlockCaptured_of_cornerChannel R hR (hchan R hR)

/-! ## Widened outer-corner channel -/

/-- Canonical RH-safe number of neighboring VF blocks.  The min keeps the
lower corner inside a local [R/2,2R] window at every scale; asymptotically the
other argument is the intended A log(R)^2 lag. -/
def vfMidCanonicalCornerLag (A : ℝ) (R : ℕ) : ℕ :=
  min (R / 2) ⌊A * Real.log (R : ℝ) ^ 2⌋₊

/-- Lower outer VF corner at square node R. -/
def vfMidOuterLowerCorner (A : ℝ) (R : ℕ) : ℝ :=
  vfMidFinishedMass (R - vfMidCanonicalCornerLag A R)

/-- Upper outer VF corner at square node R. -/
def vfMidOuterUpperCorner (A : ℝ) (R : ℕ) : ℝ :=
  vfMidFinishedMass (R + vfMidCanonicalCornerLag A R)

/-- Piecewise-linear lower outer channel through the lower outer VF corners. -/
def vfMidOuterLowerChannel (A : ℝ) (R : ℕ) (x : ℝ) : ℝ :=
  let t := vfMidCornerParameter R x
  (1 - t) * vfMidOuterLowerCorner A R +
    t * vfMidOuterLowerCorner A (R + 1)

/-- Piecewise-linear upper outer channel through the upper outer VF corners. -/
def vfMidOuterUpperChannel (A : ℝ) (R : ℕ) (x : ℝ) : ℝ :=
  let t := vfMidCornerParameter R x
  (1 - t) * vfMidOuterUpperCorner A R +
    t * vfMidOuterUpperCorner A (R + 1)

@[simp] theorem vfMidOuterLowerChannel_left (A : ℝ) (R : ℕ) :
    vfMidOuterLowerChannel A R ((R : ℝ) ^ 2) =
      vfMidOuterLowerCorner A R := by
  simp [vfMidOuterLowerChannel]

@[simp] theorem vfMidOuterUpperChannel_left (A : ℝ) (R : ℕ) :
    vfMidOuterUpperChannel A R ((R : ℝ) ^ 2) =
      vfMidOuterUpperCorner A R := by
  simp [vfMidOuterUpperChannel]

@[simp] theorem vfMidOuterLowerChannel_right (A : ℝ) (R : ℕ) :
    vfMidOuterLowerChannel A R (((R + 1 : ℕ) : ℝ) ^ 2) =
      vfMidOuterLowerCorner A (R + 1) := by
  simp only [vfMidOuterLowerChannel, Nat.cast_add, Nat.cast_one]
  rw [vfMidCornerParameter_right_cast]
  ring

@[simp] theorem vfMidOuterUpperChannel_right (A : ℝ) (R : ℕ) :
    vfMidOuterUpperChannel A R (((R + 1 : ℕ) : ℝ) ^ 2) =
      vfMidOuterUpperCorner A (R + 1) := by
  simp only [vfMidOuterUpperChannel, Nat.cast_add, Nat.cast_one]
  rw [vfMidCornerParameter_right_cast]
  ring

/-- Full pathwise outer-channel inclusion.  This is stronger than the endpoint
statement needed by the RH consumer and is kept as the direct formal analogue
of the proposed picture. -/
def VFMidOuterCornerChannelContainsPrime (A : ℝ) : Prop :=
  ∀ R : ℕ, 4 ≤ R →
    ∀ x : ℝ,
      (R : ℝ) ^ 2 ≤ x →
      x ≤ (((R + 1 : ℕ) : ℝ) ^ 2) →
        vfMidOuterLowerChannel A R x ≤ vfMidPrimeCount x ∧
          vfMidPrimeCount x ≤ vfMidOuterUpperChannel A R x

/-- Endpoint inclusion is the minimal arithmetic target of the widened
channel route. -/
def VFMidOuterCornerEndpointBracket (A : ℝ) : Prop :=
  ∀ R : ℕ, 4 ≤ R →
    vfMidOuterLowerCorner A R ≤ (Nat.primeCounting (R ^ 2) : ℝ) ∧
      (Nat.primeCounting (R ^ 2) : ℝ) ≤ vfMidOuterUpperCorner A R

/-- Pathwise containment implies the endpoint bracket immediately. -/
theorem vfMidOuterCornerEndpointBracket_of_channel
    {A : ℝ} (hchan : VFMidOuterCornerChannelContainsPrime A) :
    VFMidOuterCornerEndpointBracket A := by
  intro R hR
  have hsqNat : R ^ 2 ≤ (R + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hsq :
      (R : ℝ) ^ 2 ≤ (((R + 1 : ℕ) : ℝ) ^ 2) := by
    exact_mod_cast hsqNat
  have h :=
    hchan R hR ((R : ℝ) ^ 2) le_rfl hsq
  simpa using h

/-! ## Intrinsic VF width estimates -/

/-- On a local half-to-double window, one VF band mass is at most
5 R / log R.  The constant is deliberately loose; the important feature is
the exact R/log R scale. -/
theorem vfMidBandMass_le_five_mul_base_div_log
    (R r : ℕ) (hR : 4 ≤ R)
    (hlow : (R : ℝ) / 2 ≤ (r : ℝ))
    (hupp : (r : ℝ) ≤ 2 * (R : ℝ)) :
    vfMidBandMass r ≤ 5 * (R : ℝ) / Real.log (R : ℝ) := by
  have hRreal : (4 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < (R : ℝ) := by positivity
  have hRgt1 : (1 : ℝ) < (R : ℝ) := by linarith
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos hRgt1
  have hsq : (R : ℝ) ≤ (r : ℝ) ^ 2 := by
    nlinarith
  have hr0 : 0 ≤ (r : ℝ) := by positivity
  have hmid :
      (R : ℝ) ≤ vfMidBandMidpoint r := by
    unfold vfMidBandMidpoint
    nlinarith [hsq]
  have hlogmid :
      Real.log (R : ℝ) ≤ Real.log (vfMidBandMidpoint r) :=
    Real.log_le_log hRpos hmid
  have hnum :
      2 * (r : ℝ) + 1 ≤ 5 * (R : ℝ) := by
    nlinarith
  unfold vfMidBandMass
  calc
    (2 * (r : ℝ) + 1) / Real.log (vfMidBandMidpoint r)
        ≤ (2 * (r : ℝ) + 1) / Real.log (R : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hlogR hlogmid
    _ ≤ 5 * (R : ℝ) / Real.log (R : ℝ) :=
      div_le_div_of_nonneg_right hnum hlogR.le

/-- Sum a uniform local band-mass bound over L consecutive completed VF
blocks. -/
theorem vfMidFinishedMass_add_sub_le_mul
    (R L : ℕ) (hR : 2 ≤ R) (B : ℝ)
    (hband : ∀ j : ℕ, j < L → vfMidBandMass (R + j) ≤ B) :
    vfMidFinishedMass (R + L) - vfMidFinishedMass R ≤
      (L : ℝ) * B := by
  revert hband
  induction L with
  | zero =>
      intro _hband
      simp
  | succ L ih =>
      intro hband
      have hRL : 2 ≤ R + L := by omega
      have hs := vfMidFinishedMass_succ (R := R + L) hRL
      have hidx : R + Nat.succ L = (R + L) + 1 := by omega
      rw [hidx, hs]
      have hi :=
        ih (fun j hj => hband j (by omega))
      have hlast := hband L (by omega)
      calc
        vfMidFinishedMass (R + L) + vfMidBandMass (R + L) -
              vfMidFinishedMass R
            = (vfMidFinishedMass (R + L) - vfMidFinishedMass R) +
                vfMidBandMass (R + L) := by ring
        _ ≤ (L : ℝ) * B + B := add_le_add hi hlast
        _ = (Nat.succ L : ℝ) * B := by
          push_cast
          ring

/-- Upper excursion across L neighboring VF blocks stays below
L * 5R/log R when the lag is at most half the base index. -/
theorem vfMidFinishedMass_add_sub_le_local
    (R L : ℕ) (hR : 4 ≤ R) (hhalf : 2 * L ≤ R) :
    vfMidFinishedMass (R + L) - vfMidFinishedMass R ≤
      (L : ℝ) * (5 * (R : ℝ) / Real.log (R : ℝ)) := by
  apply vfMidFinishedMass_add_sub_le_mul R L (by omega) _
  intro j hj
  apply vfMidBandMass_le_five_mul_base_div_log R (R + j) hR
  · have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
    push_cast
    nlinarith
  · have hjNat : R + j ≤ 2 * R := by omega
    exact_mod_cast hjNat

/-- Lower excursion across L neighboring VF blocks obeys the same local
R/log R per-block estimate. -/
theorem vfMidFinishedMass_sub_sub_le_local
    (R L : ℕ) (hR : 4 ≤ R) (hhalf : 2 * L ≤ R) :
    vfMidFinishedMass R - vfMidFinishedMass (R - L) ≤
      (L : ℝ) * (5 * (R : ℝ) / Real.log (R : ℝ)) := by
  have hLR : L ≤ R := by omega
  have hbase : 2 ≤ R - L := by omega
  have hadd : R - L + L = R := by omega
  have h :=
    vfMidFinishedMass_add_sub_le_mul (R - L) L hbase
      (5 * (R : ℝ) / Real.log (R : ℝ)) (by
        intro j hj
        apply vfMidBandMass_le_five_mul_base_div_log R (R - L + j) hR
        · have hnat : R ≤ 2 * (R - L + j) := by omega
          have hcast :
              (R : ℝ) ≤ 2 * ((R - L + j : ℕ) : ℝ) := by
            exact_mod_cast hnat
          nlinarith
        · have hnat : R - L + j ≤ 2 * R := by omega
          exact_mod_cast hnat)
  rw [hadd] at h
  exact h

/-- If L <= A log(R)^2 and L <= R/2, moving L genuine VF corners in either
direction costs at most 5 A R log R.  This is the formal scale identity behind
the widened-channel construction. -/
theorem vfMidFinishedMass_lag_excursions_le_rhScale
    {A : ℝ}
    (R L : ℕ) (hR : 4 ≤ R)
    (hhalf : 2 * L ≤ R)
    (hlag : (L : ℝ) ≤ A * Real.log (R : ℝ) ^ 2) :
    vfMidFinishedMass R - vfMidFinishedMass (R - L) ≤
        5 * A * (R : ℝ) * Real.log (R : ℝ) ∧
      vfMidFinishedMass (R + L) - vfMidFinishedMass R ≤
        5 * A * (R : ℝ) * Real.log (R : ℝ) := by
  have hRgt1 : (1 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 1 < R by omega)
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hRgt1
  have hfactor :
      0 ≤ 5 * (R : ℝ) / Real.log (R : ℝ) := by positivity
  have hscale :
      (L : ℝ) * (5 * (R : ℝ) / Real.log (R : ℝ)) ≤
        5 * A * (R : ℝ) * Real.log (R : ℝ) := by
    calc
      (L : ℝ) * (5 * (R : ℝ) / Real.log (R : ℝ))
          ≤ (A * Real.log (R : ℝ) ^ 2) *
              (5 * (R : ℝ) / Real.log (R : ℝ)) :=
        mul_le_mul_of_nonneg_right hlag hfactor
      _ = 5 * A * (R : ℝ) * Real.log (R : ℝ) := by
        field_simp [hlog.ne']
  constructor
  · exact (vfMidFinishedMass_sub_sub_le_local R L hR hhalf).trans hscale
  · exact (vfMidFinishedMass_add_sub_le_local R L hR hhalf).trans hscale

/-- The canonical lag never exceeds half the square-root index. -/
theorem vfMidCanonicalCornerLag_two_mul_le
    {A : ℝ} (R : ℕ) :
    2 * vfMidCanonicalCornerLag A R ≤ R := by
  unfold vfMidCanonicalCornerLag
  have hmin : min (R / 2) ⌊A * Real.log (R : ℝ) ^ 2⌋₊ ≤ R / 2 :=
    min_le_left _ _
  omega

/-- For nonnegative A, the canonical lag is at most A log(R)^2. -/
theorem vfMidCanonicalCornerLag_cast_le
    {A : ℝ} (hA : 0 ≤ A) (R : ℕ) :
    (vfMidCanonicalCornerLag A R : ℝ) ≤
      A * Real.log (R : ℝ) ^ 2 := by
  let n : ℕ := ⌊A * Real.log (R : ℝ) ^ 2⌋₊
  have harg : 0 ≤ A * Real.log (R : ℝ) ^ 2 := by positivity
  have hmin : vfMidCanonicalCornerLag A R ≤ n := by
    unfold vfMidCanonicalCornerLag
    dsimp [n]
    exact min_le_right _ _
  have hcast :
      (vfMidCanonicalCornerLag A R : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hmin
  have hfloor :
      (n : ℝ) ≤ A * Real.log (R : ℝ) ^ 2 := by
    dsimp [n]
    exact Nat.floor_le harg
  exact hcast.trans hfloor

/-- The two canonical outer corners are automatically within the full
5 A R log R allowance from the central VF square endpoint. -/
theorem vfMidCanonicalOuterCorners_rhSafe
    {A : ℝ} (hA : 0 ≤ A)
    (R : ℕ) (hR : 4 ≤ R) :
    vfMidFinishedMass R - vfMidOuterLowerCorner A R ≤
        5 * A * (R : ℝ) * Real.log (R : ℝ) ∧
      vfMidOuterUpperCorner A R - vfMidFinishedMass R ≤
        5 * A * (R : ℝ) * Real.log (R : ℝ) := by
  let L := vfMidCanonicalCornerLag A R
  have hhalf : 2 * L ≤ R :=
    vfMidCanonicalCornerLag_two_mul_le (A := A) R
  have hlag :
      (L : ℝ) ≤ A * Real.log (R : ℝ) ^ 2 := by
    dsimp [L]
    exact vfMidCanonicalCornerLag_cast_le hA R
  have h :=
    vfMidFinishedMass_lag_excursions_le_rhScale R L hR hhalf hlag
  simpa [vfMidOuterLowerCorner, vfMidOuterUpperCorner, L] using h

/-! ## Endpoint inclusion closes the RH-scale target -/

/-- Tail version of the square-endpoint target, starting at R = 4 so that the
local half-to-double corner geometry is available. -/
def VFMidSquareEndpointVonKochBoundedFromFourStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 4 ≤ R →
      |vfMidPrimeError ((R : ℝ) ^ 2)| ≤
        C * (R : ℝ) * Real.log (R : ℝ)

/-- Generic widened-corner bracket for an arbitrary lag schedule.  The
schedule is separated from its growth hypotheses so the geometry does not
privilege one fitted trajectory. -/
def VFMidLaggedCornerEndpointBracket (L : ℕ → ℕ) : Prop :=
  ∀ R : ℕ, 4 ≤ R →
    vfMidFinishedMass (R - L R) ≤
        (Nat.primeCounting (R ^ 2) : ℝ) ∧
      (Nat.primeCounting (R ^ 2) : ℝ) ≤
        vfMidFinishedMass (R + L R)

/-- Asymmetric phase bracket.  The left/lower VF control may lag by Lminus
blocks while the right/upper VF control may advance by Lplus blocks.  This is
the intrinsic lead/lag form of the corner geometry. -/
def VFMidLeadLagCornerEndpointBracket
    (Lminus Lplus : ℕ → ℕ) : Prop :=
  ∀ R : ℕ, 4 ≤ R →
    vfMidFinishedMass (R - Lminus R) ≤
        (Nat.primeCounting (R ^ 2) : ℝ) ∧
      (Nat.primeCounting (R ^ 2) : ℝ) ≤
        vfMidFinishedMass (R + Lplus R)

/-- The symmetric lag bracket is the diagonal special case of the asymmetric
lead/lag bracket. -/
theorem vfMidLeadLagCornerEndpointBracket_of_symmetric
    {L : ℕ → ℕ}
    (h : VFMidLaggedCornerEndpointBracket L) :
    VFMidLeadLagCornerEndpointBracket L L := by
  exact h

/-- Independent O(log(R)^2) lag and advance budgets still give the required
O(R log R) square-endpoint bound.  The two sides are allowed to use different
constants and different block counts. -/
theorem vfMidSquareEndpointVonKochBoundedFromFour_of_leadLagCornerBracket
    {Aminus Aplus : ℝ}
    (hAminus : 0 ≤ Aminus) (hAplus : 0 ≤ Aplus)
    (Lminus Lplus : ℕ → ℕ)
    (hhalfMinus : ∀ R : ℕ, 4 ≤ R → 2 * Lminus R ≤ R)
    (hhalfPlus : ∀ R : ℕ, 4 ≤ R → 2 * Lplus R ≤ R)
    (hlagMinus : ∀ R : ℕ, 4 ≤ R →
      (Lminus R : ℝ) ≤ Aminus * Real.log (R : ℝ) ^ 2)
    (hlagPlus : ∀ R : ℕ, 4 ≤ R →
      (Lplus R : ℝ) ≤ Aplus * Real.log (R : ℝ) ^ 2)
    (hbr : VFMidLeadLagCornerEndpointBracket Lminus Lplus) :
    VFMidSquareEndpointVonKochBoundedFromFourStatement := by
  refine ⟨5 * (Aminus + Aplus),
    mul_nonneg (by norm_num) (add_nonneg hAminus hAplus), ?_⟩
  intro R hR
  have hminus :=
    vfMidFinishedMass_lag_excursions_le_rhScale
      R (Lminus R) hR (hhalfMinus R hR) (hlagMinus R hR)
  have hplus :=
    vfMidFinishedMass_lag_excursions_le_rhScale
      R (Lplus R) hR (hhalfPlus R hR) (hlagPlus R hR)
  have hb := hbr R hR
  have hRgt1 : (1 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 1 < R by omega)
  have hscale0 :
      0 ≤ (R : ℝ) * Real.log (R : ℝ) :=
    mul_nonneg (by positivity) (Real.log_pos hRgt1).le
  have hminusC :
      5 * Aminus * (R : ℝ) * Real.log (R : ℝ) ≤
        5 * (Aminus + Aplus) * (R : ℝ) * Real.log (R : ℝ) := by
    have hcoef : 5 * Aminus ≤ 5 * (Aminus + Aplus) := by
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hcoef hscale0
    simpa [mul_assoc] using hm
  have hplusC :
      5 * Aplus * (R : ℝ) * Real.log (R : ℝ) ≤
        5 * (Aminus + Aplus) * (R : ℝ) * Real.log (R : ℝ) := by
    have hcoef : 5 * Aplus ≤ 5 * (Aminus + Aplus) := by
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hcoef hscale0
    simpa [mul_assoc] using hm
  have herr :
      vfMidPrimeError ((R : ℝ) ^ 2) =
        (Nat.primeCounting (R ^ 2) : ℝ) - vfMidFinishedMass R := by
    unfold vfMidPrimeError
    rw [vfMidPrimeCount_sq_exact R, vfMid_sq (by omega : 2 ≤ R)]
  rw [herr]
  apply abs_le.mpr
  constructor
  · have hlow := hminus.1
    have hbLower := hb.1
    linarith
  · have hupp := hplus.2
    have hbUpper := hb.2
    linarith

/-- Any O(log(R)^2) genuine-VF lag schedule gives an O(R log R) endpoint
bound once the actual prime endpoint is bracketed by its outer VF corners. -/
theorem vfMidSquareEndpointVonKochBoundedFromFour_of_laggedCornerBracket
    {A : ℝ} (hA : 0 ≤ A)
    (L : ℕ → ℕ)
    (hhalf : ∀ R : ℕ, 4 ≤ R → 2 * L R ≤ R)
    (hlag : ∀ R : ℕ, 4 ≤ R →
      (L R : ℝ) ≤ A * Real.log (R : ℝ) ^ 2)
    (hbr : VFMidLaggedCornerEndpointBracket L) :
    VFMidSquareEndpointVonKochBoundedFromFourStatement := by
  refine ⟨5 * A, mul_nonneg (by norm_num) hA, ?_⟩
  intro R hR
  have hcorners :=
    vfMidFinishedMass_lag_excursions_le_rhScale
      R (L R) hR (hhalf R hR) (hlag R hR)
  have hb := hbr R hR
  have herr :
      vfMidPrimeError ((R : ℝ) ^ 2) =
        (Nat.primeCounting (R ^ 2) : ℝ) - vfMidFinishedMass R := by
    unfold vfMidPrimeError
    rw [vfMidPrimeCount_sq_exact R, vfMid_sq (by omega : 2 ≤ R)]
  rw [herr]
  apply abs_le.mpr
  constructor <;> linarith

/-- Canonical outer-corner endpoint inclusion directly supplies the RH-scale
bound for every R >= 4. -/
theorem vfMidSquareEndpointVonKochBoundedFromFour_of_outerCornerBracket
    {A : ℝ} (hA : 0 ≤ A)
    (hbr : VFMidOuterCornerEndpointBracket A) :
    VFMidSquareEndpointVonKochBoundedFromFourStatement := by
  refine ⟨5 * A, mul_nonneg (by norm_num) hA, ?_⟩
  intro R hR
  have hcorners := vfMidCanonicalOuterCorners_rhSafe hA R hR
  have hb := hbr R hR
  have herr :
      vfMidPrimeError ((R : ℝ) ^ 2) =
        (Nat.primeCounting (R ^ 2) : ℝ) - vfMidFinishedMass R := by
    unfold vfMidPrimeError
    rw [vfMidPrimeCount_sq_exact R, vfMid_sq (by omega : 2 ≤ R)]
  rw [herr]
  apply abs_le.mpr
  constructor <;> linarith

/-- A bound from R >= 4 extends to all square scales by enlarging the constant
to absorb the two finite endpoints R = 2 and R = 3. -/
theorem vfMidSquareEndpointVonKochBounded_of_fromFour
    (h : VFMidSquareEndpointVonKochBoundedFromFourStatement) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  rcases h with ⟨C, hC, htail⟩
  let e2 : ℝ := |vfMidPrimeError 4|
  let e3 : ℝ := |vfMidPrimeError 9|
  let w2 : ℝ := 2 * Real.log 2
  let w3 : ℝ := 3 * Real.log 3
  let D : ℝ := C + e2 / w2 + e3 / w3
  have hw2 : 0 < w2 := by
    dsimp [w2]
    positivity
  have hw3 : 0 < w3 := by
    dsimp [w3]
    positivity
  have he20 : 0 ≤ e2 := by
    dsimp [e2]
    positivity
  have he30 : 0 ≤ e3 := by
    dsimp [e3]
    positivity
  have he2div0 : 0 ≤ e2 / w2 := div_nonneg he20 hw2.le
  have he3div0 : 0 ≤ e3 / w3 := div_nonneg he30 hw3.le
  have hD : 0 ≤ D := by
    dsimp [D]
    linarith
  have hCD : C ≤ D := by
    dsimp [D]
    linarith
  refine ⟨D, hD, ?_⟩
  intro R hR
  by_cases h4 : 4 ≤ R
  · have ht := htail R h4
    have hRgt1 : (1 : ℝ) < (R : ℝ) := by
      exact_mod_cast (show 1 < R by omega)
    have hscale0 :
        0 ≤ (R : ℝ) * Real.log (R : ℝ) :=
      mul_nonneg (by positivity) (Real.log_pos hRgt1).le
    have hm :=
      mul_le_mul_of_nonneg_right hCD hscale0
    calc
      |vfMidPrimeError ((R : ℝ) ^ 2)|
          ≤ C * (R : ℝ) * Real.log (R : ℝ) := ht
      _ = C * ((R : ℝ) * Real.log (R : ℝ)) := by ring
      _ ≤ D * ((R : ℝ) * Real.log (R : ℝ)) := hm
      _ = D * (R : ℝ) * Real.log (R : ℝ) := by ring
  · have hsmall : R = 2 ∨ R = 3 := by omega
    rcases hsmall with rfl | rfl
    · have hcoef : e2 / w2 ≤ D := by
        dsimp [D]
        linarith
      have heq : (e2 / w2) * w2 = e2 :=
        div_mul_cancel₀ _ hw2.ne'
      have hsmall2 : e2 ≤ D * w2 := by
        calc
          e2 = (e2 / w2) * w2 := heq.symm
          _ ≤ D * w2 := mul_le_mul_of_nonneg_right hcoef hw2.le
      norm_num [e2, w2] at hsmall2 ⊢
      exact hsmall2
    · have hcoef : e3 / w3 ≤ D := by
        dsimp [D]
        linarith
      have heq : (e3 / w3) * w3 = e3 :=
        div_mul_cancel₀ _ hw3.ne'
      have hsmall3 : e3 ≤ D * w3 := by
        calc
          e3 = (e3 / w3) * w3 := heq.symm
          _ ≤ D * w3 := mul_le_mul_of_nonneg_right hcoef hw3.le
      norm_num [e3, w3] at hsmall3 ⊢
      exact hsmall3

/-- The asymmetric lag/advance formulation is sufficient for the full
square-endpoint target after absorbing the finite initial scales. -/
theorem vfMidSquareEndpointVonKochBounded_of_leadLagCornerBracket
    {Aminus Aplus : ℝ}
    (hAminus : 0 ≤ Aminus) (hAplus : 0 ≤ Aplus)
    (Lminus Lplus : ℕ → ℕ)
    (hhalfMinus : ∀ R : ℕ, 4 ≤ R → 2 * Lminus R ≤ R)
    (hhalfPlus : ∀ R : ℕ, 4 ≤ R → 2 * Lplus R ≤ R)
    (hlagMinus : ∀ R : ℕ, 4 ≤ R →
      (Lminus R : ℝ) ≤ Aminus * Real.log (R : ℝ) ^ 2)
    (hlagPlus : ∀ R : ℕ, 4 ≤ R →
      (Lplus R : ℝ) ≤ Aplus * Real.log (R : ℝ) ^ 2)
    (hbr : VFMidLeadLagCornerEndpointBracket Lminus Lplus) :
    VFMidSquareEndpointVonKochBoundedStatement :=
  vfMidSquareEndpointVonKochBounded_of_fromFour
    (vfMidSquareEndpointVonKochBoundedFromFour_of_leadLagCornerBracket
      hAminus hAplus Lminus Lplus hhalfMinus hhalfPlus
      hlagMinus hlagPlus hbr)

/-- Downstream RH consumer for independently budgeted lagged and advanced
VF-corner chains. -/
theorem riemannHypothesis_of_leadLagCornerBracket
    (criterion : ClassicalVonKochRHCriterion)
    {Aminus Aplus : ℝ}
    (hAminus : 0 ≤ Aminus) (hAplus : 0 ≤ Aplus)
    (Lminus Lplus : ℕ → ℕ)
    (hhalfMinus : ∀ R : ℕ, 4 ≤ R → 2 * Lminus R ≤ R)
    (hhalfPlus : ∀ R : ℕ, 4 ≤ R → 2 * Lplus R ≤ R)
    (hlagMinus : ∀ R : ℕ, 4 ≤ R →
      (Lminus R : ℝ) ≤ Aminus * Real.log (R : ℝ) ^ 2)
    (hlagPlus : ∀ R : ℕ, 4 ≤ R →
      (Lplus R : ℝ) ≤ Aplus * Real.log (R : ℝ) ^ 2)
    (hbr : VFMidLeadLagCornerEndpointBracket Lminus Lplus) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_leadLagCornerBracket
      hAminus hAplus Lminus Lplus hhalfMinus hhalfPlus
      hlagMinus hlagPlus hbr)

/-- The generic lag-budget formulation is itself sufficient for the full
square-endpoint target after the finite initial scales are absorbed. -/
theorem vfMidSquareEndpointVonKochBounded_of_laggedCornerBracket
    {A : ℝ} (hA : 0 ≤ A)
    (L : ℕ → ℕ)
    (hhalf : ∀ R : ℕ, 4 ≤ R → 2 * L R ≤ R)
    (hlag : ∀ R : ℕ, 4 ≤ R →
      (L R : ℝ) ≤ A * Real.log (R : ℝ) ^ 2)
    (hbr : VFMidLaggedCornerEndpointBracket L) :
    VFMidSquareEndpointVonKochBoundedStatement :=
  vfMidSquareEndpointVonKochBounded_of_fromFour
    (vfMidSquareEndpointVonKochBoundedFromFour_of_laggedCornerBracket
      hA L hhalf hlag hbr)

/-- Downstream RH consumer for the generic O(log(R)^2) VF-corner budget. -/
theorem riemannHypothesis_of_laggedCornerBracket
    (criterion : ClassicalVonKochRHCriterion)
    {A : ℝ} (hA : 0 ≤ A)
    (L : ℕ → ℕ)
    (hhalf : ∀ R : ℕ, 4 ≤ R → 2 * L R ≤ R)
    (hlag : ∀ R : ℕ, 4 ≤ R →
      (L R : ℝ) ≤ A * Real.log (R : ℝ) ^ 2)
    (hbr : VFMidLaggedCornerEndpointBracket L) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_laggedCornerBracket
      hA L hhalf hlag hbr)

/-- The widened VF-corner inclusion is a sufficient condition for the direct
square-endpoint von-Koch target. -/
theorem vfMidSquareEndpointVonKochBounded_of_outerCornerBracket
    {A : ℝ} (hA : 0 ≤ A)
    (hbr : VFMidOuterCornerEndpointBracket A) :
    VFMidSquareEndpointVonKochBoundedStatement :=
  vfMidSquareEndpointVonKochBounded_of_fromFour
    (vfMidSquareEndpointVonKochBoundedFromFour_of_outerCornerBracket hA hbr)

/-- Existing downstream RH consumer for the widened VF-corner channel. -/
theorem riemannHypothesis_of_outerCornerBracket
    (criterion : ClassicalVonKochRHCriterion)
    {A : ℝ} (hA : 0 ≤ A)
    (hbr : VFMidOuterCornerEndpointBracket A) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_outerCornerBracket hA hbr)

/-! ## Theoretical prime-envelope inclusion API -/

/-- Real-valued theoretical lower envelope for ordinary prime count. -/
def PrimeCountingRealLowerEnvelope (L : ℕ → ℝ) : Prop :=
  ∀ x : ℕ, L x ≤ (Nat.primeCounting x : ℝ)

/-- Real-valued theoretical upper envelope for ordinary prime count. -/
def PrimeCountingRealUpperEnvelope (U : ℕ → ℝ) : Prop :=
  ∀ x : ℕ, (Nat.primeCounting x : ℝ) ≤ U x

/-- Intersecting two rigorous lower series by pointwise maximum preserves a
valid lower prime-count envelope. -/
theorem primeCountingRealLowerEnvelope_max
    {L₁ L₂ : ℕ → ℝ}
    (h₁ : PrimeCountingRealLowerEnvelope L₁)
    (h₂ : PrimeCountingRealLowerEnvelope L₂) :
    PrimeCountingRealLowerEnvelope (fun x => max (L₁ x) (L₂ x)) := by
  intro x
  exact max_le (h₁ x) (h₂ x)

/-- Intersecting two rigorous upper series by pointwise minimum preserves a
valid upper prime-count envelope. -/
theorem primeCountingRealUpperEnvelope_min
    {U₁ U₂ : ℕ → ℝ}
    (h₁ : PrimeCountingRealUpperEnvelope U₁)
    (h₂ : PrimeCountingRealUpperEnvelope U₂) :
    PrimeCountingRealUpperEnvelope (fun x => min (U₁ x) (U₂ x)) := by
  intro x
  exact le_min (h₁ x) (h₂ x)

/-- Real theoretical series trapped inside the canonical outer VF corners
force the endpoint bracket directly.  This is the continuous-series version
of the inclusion proof architecture. -/
theorem vfMidOuterCornerEndpointBracket_of_realPrimeCount_envelopes
    {A : ℝ}
    (L U : ℕ → ℝ)
    (hL : PrimeCountingRealLowerEnvelope L)
    (hU : PrimeCountingRealUpperEnvelope U)
    (hLower :
      ∀ R : ℕ, 4 ≤ R →
        vfMidOuterLowerCorner A R ≤ L (R ^ 2))
    (hUpper :
      ∀ R : ℕ, 4 ≤ R →
        U (R ^ 2) ≤ vfMidOuterUpperCorner A R) :
    VFMidOuterCornerEndpointBracket A := by
  intro R hR
  exact ⟨(hLower R hR).trans (hL (R ^ 2)),
    (hU (R ^ 2)).trans (hUpper R hR)⟩

/-- Intersect two lower and two upper theoretical series and consume the
resulting tight bracket in one step.  Repeated application gives the same API
for any finite family of proved envelopes. -/
theorem vfMidOuterCornerEndpointBracket_of_intersected_real_envelopes
    {A : ℝ}
    (L₁ L₂ U₁ U₂ : ℕ → ℝ)
    (hL₁ : PrimeCountingRealLowerEnvelope L₁)
    (hL₂ : PrimeCountingRealLowerEnvelope L₂)
    (hU₁ : PrimeCountingRealUpperEnvelope U₁)
    (hU₂ : PrimeCountingRealUpperEnvelope U₂)
    (hLower :
      ∀ R : ℕ, 4 ≤ R →
        vfMidOuterLowerCorner A R ≤ max (L₁ (R ^ 2)) (L₂ (R ^ 2)))
    (hUpper :
      ∀ R : ℕ, 4 ≤ R →
        min (U₁ (R ^ 2)) (U₂ (R ^ 2)) ≤ vfMidOuterUpperCorner A R) :
    VFMidOuterCornerEndpointBracket A := by
  apply vfMidOuterCornerEndpointBracket_of_realPrimeCount_envelopes
    (fun x => max (L₁ x) (L₂ x))
    (fun x => min (U₁ x) (U₂ x))
  · exact primeCountingRealLowerEnvelope_max hL₁ hL₂
  · exact primeCountingRealUpperEnvelope_min hU₁ hU₂
  · exact hLower
  · exact hUpper


/-- Any rigorous lower/upper prime-count envelopes that fit inside the two
outer VF corners force the required endpoint bracket.  This is the formal
"prove pi by inclusion between theoretical series" interface. -/
theorem vfMidOuterCornerEndpointBracket_of_primeCount_envelopes
    {A : ℝ}
    (L U : ℕ → ℕ)
    (hL : PrimeCountingLowerEnvelope L)
    (hU : PrimeCountingUpperEnvelope U)
    (hLower :
      ∀ R : ℕ, 4 ≤ R →
        vfMidOuterLowerCorner A R ≤ (L (R ^ 2) : ℝ))
    (hUpper :
      ∀ R : ℕ, 4 ≤ R →
        (U (R ^ 2) : ℝ) ≤ vfMidOuterUpperCorner A R) :
    VFMidOuterCornerEndpointBracket A := by
  intro R hR
  have hLreal :
      (L (R ^ 2) : ℝ) ≤ (Nat.primeCounting (R ^ 2) : ℝ) := by
    exact_mod_cast (hL (R ^ 2))
  have hUreal :
      (Nat.primeCounting (R ^ 2) : ℝ) ≤ (U (R ^ 2) : ℝ) := by
    exact_mod_cast (hU (R ^ 2))
  exact ⟨(hLower R hR).trans hLreal,
    hUreal.trans (hUpper R hR)⟩

/-- A theoretical prime-envelope bracket inside the canonical outer VF
corners closes the direct square-endpoint target. -/
theorem vfMidSquareEndpointVonKochBounded_of_primeCount_outerEnvelopes
    {A : ℝ} (hA : 0 ≤ A)
    (L U : ℕ → ℕ)
    (hL : PrimeCountingLowerEnvelope L)
    (hU : PrimeCountingUpperEnvelope U)
    (hLower :
      ∀ R : ℕ, 4 ≤ R →
        vfMidOuterLowerCorner A R ≤ (L (R ^ 2) : ℝ))
    (hUpper :
      ∀ R : ℕ, 4 ≤ R →
        (U (R ^ 2) : ℝ) ≤ vfMidOuterUpperCorner A R) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  apply vfMidSquareEndpointVonKochBounded_of_outerCornerBracket hA
  exact vfMidOuterCornerEndpointBracket_of_primeCount_envelopes
    L U hL hU hLower hUpper

end RHLean.Analysis
