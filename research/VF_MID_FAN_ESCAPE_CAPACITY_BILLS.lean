import Mathlib
import «research.VF_MID_OPTIMAL_BASE_FIRST_CROSSING_TRIGGER»

/-!
# Exact count-space escape bills for the solved radial fan

This file records the literal integer costs of escaping a count-space channel
from a fixed starting height.

There are two extremal mechanisms.

* Lower-wall escape by a horizontal prime-count segment:
  keep the count fixed and let the rising lower wall catch it.  The exact bill
  is the first horizontal displacement at which the lower wall lies strictly
  above the frozen count level.

* Upper-wall escape by clustered prime jumps:
  after a horizontal displacement, count how many unit jumps are required to
  lie strictly above the upper wall.  The exact bill is the least natural
  number of jumps that clears that wall.

These are capacity quantities.  They do not assume that actual primes already
lie in the solved fantasy cone and they do not assert that the required
composite run or prime cluster is impossible.  They are intended to be compared
with the repository's exact wheel/composite and survivor capacities.

For the existing normalized radial walls at square root R,

  lower(R) = VF_mid(R^2) - K R log R,
  upper(R) = VF_mid(R^2) + K R log R,

so a point exactly at the center has count-space distance

  H_R = K R log R

to either wall.

Numerical diagnostic only (not used by any theorem below): at K = 2 and
R = 5266,

  H_R ~= 90248.9854.

Using the exact VF square-band masses, the first later square endpoint at which
a completely frozen center height is overtaken by the lower radial wall occurs
at square-root offset 150, corresponding to

  5416^2 - 5266^2 = 1,602,300

integer sites.  At the next square endpoint, the upper-wall bill from the same
center is about 90,882.714 unit jumps, hence 90,883 prime jumps are required,
while the whole square block contains only

  5267^2 - 5266^2 = 10,533

integer sites.

Those figures are reference diagnostics, not kernel-checked numerical
certificates.  The formal objects below encode the exact bills to which any
future wheel/survivor capacity theorem can be compared.
-/

noncomputable section

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- A frozen count level has been overtaken by the lower wall after `h`
horizontal integer steps. -/
def VFMidLowerWallHorizontalHit
    (lower : ℕ → ℝ) (x0 : ℕ) (y0 : ℝ) (h : ℕ) : Prop :=
  y0 < lower (x0 + h)

/-- Exact first horizontal displacement at which the lower wall overtakes the
frozen count level.  If no such displacement exists, the convention is zero. -/
noncomputable def vfMidLowerWallCompositeRunBill
    (lower : ℕ → ℝ) (x0 : ℕ) (y0 : ℝ) : ℕ :=
  if hex : ∃ h : ℕ, VFMidLowerWallHorizontalHit lower x0 y0 h then
    Nat.find hex
  else
    0

/-- Whenever a lower-wall hit exists, the lower composite-run bill really
hits the wall. -/
theorem vfMidLowerWallCompositeRunBill_hits
    (lower : ℕ → ℝ) (x0 : ℕ) (y0 : ℝ)
    (hex : ∃ h : ℕ, VFMidLowerWallHorizontalHit lower x0 y0 h) :
    VFMidLowerWallHorizontalHit lower x0 y0
      (vfMidLowerWallCompositeRunBill lower x0 y0) := by
  unfold vfMidLowerWallCompositeRunBill
  rw [dif_pos hex]
  exact Nat.find_spec hex

/-- No shorter horizontal run can hit the lower wall. -/
theorem vfMidLowerWallCompositeRunBill_minimal
    (lower : ℕ → ℝ) (x0 : ℕ) (y0 : ℝ)
    (hex : ∃ h : ℕ, VFMidLowerWallHorizontalHit lower x0 y0 h)
    {h : ℕ}
    (hh : h < vfMidLowerWallCompositeRunBill lower x0 y0) :
    ¬ VFMidLowerWallHorizontalHit lower x0 y0 h := by
  unfold vfMidLowerWallCompositeRunBill at hh
  rw [dif_pos hex] at hh
  exact Nat.find_min hex hh

/-- `q` unit prime jumps across horizontal displacement `h` strictly clear
the upper wall. -/
def VFMidUpperWallPrimeJumpsBreak
    (upper : ℕ → ℝ) (x0 : ℕ) (y0 : ℝ) (h q : ℕ) : Prop :=
  upper (x0 + h) < y0 + (q : ℝ)

/-- There is always some finite number of unit jumps that clears a fixed
finite upper-wall height. -/
theorem vfMidUpperWallPrimeJumpsBreak_exists
    (upper : ℕ → ℝ) (x0 : ℕ) (y0 : ℝ) (h : ℕ) :
    ∃ q : ℕ, VFMidUpperWallPrimeJumpsBreak upper x0 y0 h q := by
  obtain ⟨q : ℕ, hq⟩ := exists_nat_gt (upper (x0 + h) - y0)
  refine ⟨q, ?_⟩
  unfold VFMidUpperWallPrimeJumpsBreak
  linarith

/-- Exact least number of unit prime jumps needed, after horizontal
displacement `h`, to strictly clear the upper wall.  This is the order-free
version of `floor(upper(x0+h)-y0)+1`. -/
noncomputable def vfMidUpperPrimeJumpBill
    (upper : ℕ → ℝ) (x0 : ℕ) (y0 : ℝ) (h : ℕ) : ℕ :=
  Nat.find (vfMidUpperWallPrimeJumpsBreak_exists upper x0 y0 h)

/-- The upper prime-jump bill strictly clears the wall. -/
theorem vfMidUpperPrimeJumpBill_breaks
    (upper : ℕ → ℝ) (x0 : ℕ) (y0 : ℝ) (h : ℕ) :
    VFMidUpperWallPrimeJumpsBreak upper x0 y0 h
      (vfMidUpperPrimeJumpBill upper x0 y0 h) := by
  exact Nat.find_spec (vfMidUpperWallPrimeJumpsBreak_exists upper x0 y0 h)

/-- Any smaller number of prime jumps fails to clear the upper wall. -/
theorem vfMidUpperPrimeJumpBill_minimal
    (upper : ℕ → ℝ) (x0 : ℕ) (y0 : ℝ) (h : ℕ)
    {q : ℕ}
    (hq : q < vfMidUpperPrimeJumpBill upper x0 y0 h) :
    ¬ VFMidUpperWallPrimeJumpsBreak upper x0 y0 h q := by
  exact Nat.find_min
    (vfMidUpperWallPrimeJumpsBreak_exists upper x0 y0 h) hq

/-- Generic capacity contradiction: if every admissible prime cluster has at
most `cap` jumps but `cap` is strictly below the upper-wall bill, then no
such cluster can break the upper wall. -/
theorem vfMidUpperWall_noBreak_of_capacity_lt_bill
    (upper : ℕ → ℝ) (x0 : ℕ) (y0 : ℝ) (h cap q : ℕ)
    (hcap : cap < vfMidUpperPrimeJumpBill upper x0 y0 h)
    (hq : q ≤ cap) :
    ¬ VFMidUpperWallPrimeJumpsBreak upper x0 y0 h q := by
  apply vfMidUpperPrimeJumpBill_minimal upper x0 y0 h
  exact lt_of_le_of_lt hq hcap

/-! ## Specialization to the repository's existing square-endpoint radial fan -/

/-- Center count of the normalized radial fan at square root `R`. -/
def vfMidRadialCenterCount (R : ℕ) : ℝ :=
  vfMid ((R : ℝ) ^ 2)

/-- Exact center-to-lower-wall count distance. -/
theorem vfMidRadialCenter_sub_lowerWall
    (K : ℝ) (R : ℕ) :
    vfMidRadialCenterCount R -
        vfMidSolvedFantasyRadialLowerCount K R =
      vfMidRadialWallWidth K R := by
  simp [vfMidRadialCenterCount, vfMidSolvedFantasyRadialLowerCount,
    vfMidRadialWallWidth]

/-- Exact center-to-upper-wall count distance. -/
theorem vfMidRadialUpperWall_sub_center
    (K : ℝ) (R : ℕ) :
    vfMidSolvedFantasyRadialUpperCount K R -
        vfMidRadialCenterCount R =
      vfMidRadialWallWidth K R := by
  simp [vfMidRadialCenterCount, vfMidSolvedFantasyRadialUpperCount,
    vfMidRadialWallWidth]

/-- First later square-root offset at which the lower radial wall overtakes a
count frozen at the center of square `A`.  This is a square-sampled version of
the horizontal lower-wall bill. -/
noncomputable def vfMidRadialLowerBlockBill
    (K : ℝ) (A : ℕ) : ℕ :=
  vfMidLowerWallCompositeRunBill
    (vfMidSolvedFantasyRadialLowerCount K) A (vfMidRadialCenterCount A)

/-- Number of integer sites traversed from `A^2` to `(A+s)^2`. -/
def vfMidSquareSpan (A s : ℕ) : ℕ :=
  (A + s) ^ 2 - A ^ 2

/-- Square-sampled composite-run bill corresponding to
`vfMidRadialLowerBlockBill`. -/
noncomputable def vfMidRadialLowerCompositeRunBill
    (K : ℝ) (A : ℕ) : ℕ :=
  vfMidSquareSpan A (vfMidRadialLowerBlockBill K A)

/-- If a future square lower-wall hit exists, the selected block bill hits it. -/
theorem vfMidRadialLowerBlockBill_hits
    (K : ℝ) (A : ℕ)
    (hex : ∃ s : ℕ,
      vfMidRadialCenterCount A <
        vfMidSolvedFantasyRadialLowerCount K (A + s)) :
    vfMidRadialCenterCount A <
      vfMidSolvedFantasyRadialLowerCount K
        (A + vfMidRadialLowerBlockBill K A) := by
  exact vfMidLowerWallCompositeRunBill_hits
    (vfMidSolvedFantasyRadialLowerCount K) A
    (vfMidRadialCenterCount A) hex

/-- Every smaller square-root offset remains on or below the frozen center
height. -/
theorem vfMidRadialLowerBlockBill_minimal
    (K : ℝ) (A : ℕ)
    (hex : ∃ s : ℕ,
      vfMidRadialCenterCount A <
        vfMidSolvedFantasyRadialLowerCount K (A + s))
    {s : ℕ}
    (hs : s < vfMidRadialLowerBlockBill K A) :
    ¬ (vfMidRadialCenterCount A <
      vfMidSolvedFantasyRadialLowerCount K (A + s)) := by
  exact vfMidLowerWallCompositeRunBill_minimal
    (vfMidSolvedFantasyRadialLowerCount K) A
    (vfMidRadialCenterCount A) hex hs

/-- Exact prime-jump bill to move from the center count at `A^2` above the
upper radial wall at `(A+s)^2`. -/
noncomputable def vfMidRadialUpperPrimeJumpBill
    (K : ℝ) (A s : ℕ) : ℕ :=
  vfMidUpperPrimeJumpBill
    (vfMidSolvedFantasyRadialUpperCount K)
    A (vfMidRadialCenterCount A) s

/-- The specialized radial upper bill really breaks the upper wall. -/
theorem vfMidRadialUpperPrimeJumpBill_breaks
    (K : ℝ) (A s : ℕ) :
    vfMidSolvedFantasyRadialUpperCount K (A + s) <
      vfMidRadialCenterCount A +
        (vfMidRadialUpperPrimeJumpBill K A s : ℝ) := by
  exact vfMidUpperPrimeJumpBill_breaks
    (vfMidSolvedFantasyRadialUpperCount K)
    A (vfMidRadialCenterCount A) s

/-- Any smaller prime cluster fails to break the radial upper wall. -/
theorem vfMidRadialUpperPrimeJumpBill_minimal
    (K : ℝ) (A s : ℕ) {q : ℕ}
    (hq : q < vfMidRadialUpperPrimeJumpBill K A s) :
    ¬ (vfMidSolvedFantasyRadialUpperCount K (A + s) <
      vfMidRadialCenterCount A + (q : ℝ)) := by
  exact vfMidUpperPrimeJumpBill_minimal
    (vfMidSolvedFantasyRadialUpperCount K)
    A (vfMidRadialCenterCount A) s hq

/-- At zero horizontal displacement, the exact upper prime-jump bill is
strictly larger than the center-to-wall width. -/
theorem vfMidRadialUpperPrimeJumpBill_zero_gt_width
    (K : ℝ) (R : ℕ) :
    vfMidRadialWallWidth K R <
      (vfMidRadialUpperPrimeJumpBill K R 0 : ℝ) := by
  have h := vfMidRadialUpperPrimeJumpBill_breaks K R 0
  simp only [Nat.add_zero] at h
  rw [vfMidSolvedFantasyRadialUpperCount_eq] at h
  unfold vfMidRadialCenterCount at h
  linarith

/-- Physical site-capacity contradiction for a square-sampled upper escape.
If even the number of available integer sites is smaller than the required
prime-jump bill, then no prime cluster in that span can cross the upper wall. -/
theorem vfMidRadialUpper_noBreak_of_squareSiteCapacity_lt_bill
    (K : ℝ) (A s q : ℕ)
    (hcap :
      vfMidSquareSpan A s <
        vfMidRadialUpperPrimeJumpBill K A s)
    (hq : q ≤ vfMidSquareSpan A s) :
    ¬ (vfMidSolvedFantasyRadialUpperCount K (A + s) <
      vfMidRadialCenterCount A + (q : ℝ)) := by
  exact vfMidUpperWall_noBreak_of_capacity_lt_bill
    (vfMidSolvedFantasyRadialUpperCount K)
    A (vfMidRadialCenterCount A) s
    (vfMidSquareSpan A s) q hcap hq

end RHLean.Analysis
