import Mathlib
import «research.LI_FLOOR_PRIME_COUNT_FANTASY»
import «research.VF_MID_ODD_FRACTIONAL_CLUSTER»

/-!
# Discrete floor-Li backlog on VF square blocks

This file puts the actual prime staircase and floor(Li) on the same integer
square-block coordinates used by the native VF owner mechanism.

Let

  Q_R = floor(Li(R^2)),
  F_R = Q_(R+1) - Q_R,
  E_R = pi(R^2) - Q_R.

Then F_R is an integer block demand and

  E_(R+1) = E_R + P_R - F_R

exactly.  The cumulative floor-Li block defect therefore telescopes to the
endpoint backlog.  On the parity-reduced VF carrier, the same block defect is
literally actual chronological composite removal minus the floor-Li composite
demand.

Finally, floor(Li) differs from continuous Li by at most one and VF differs
from Li by root scale.  Hence the deterministic floor-Li/VF bridge is root
scale.  This isolates the remaining arithmetic as the integer-valued backlog
between actual prime supply and floor-Li block demand, without changing the
already-compiled VF endpoint plumbing.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Integer floor-Li potential at the VF square endpoint R^2. -/
def vfMidFloorLiSquarePotential (R : ℕ) : ℤ :=
  ⌊vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)⌋

/-- The square potential is exactly the existing real-valued floor-Li proxy
after coercion. -/
theorem vfMidFloorLiSquarePotential_cast (R : ℕ) :
    ((vfMidFloorLiSquarePotential R : ℤ) : ℝ) =
      liFloorPrimeCountProxy ((R : ℝ) ^ 2) := by
  rfl

/-- Integer floor-Li demand assigned to one square block.  It is defined as a
difference of cumulative floors, not as the floor of a block integral. -/
def vfMidFloorLiBlockSupply (R : ℕ) : ℤ :=
  vfMidFloorLiSquarePotential (R + 1) -
    vfMidFloorLiSquarePotential R

/-- The floor-Li block demands telescope exactly. -/
theorem sum_vfMidFloorLiBlockSupply
    (A B : ℕ) (hAB : A ≤ B) :
    (∑ r ∈ Finset.Ico A B, vfMidFloorLiBlockSupply r) =
      vfMidFloorLiSquarePotential B -
        vfMidFloorLiSquarePotential A := by
  unfold vfMidFloorLiBlockSupply
  exact Finset.sum_Ico_sub vfMidFloorLiSquarePotential hAB

/-- Integer backlog of actual prime count against floor-Li at a square
endpoint. -/
def vfMidPrimeFloorLiBacklog (R : ℕ) : ℤ :=
  (Nat.primeCounting (R ^ 2) : ℤ) -
    vfMidFloorLiSquarePotential R

/-- The exact actual-prime block supply is the discrete derivative of the
integer prime-count square potential. -/
theorem vfMidIntegerBlockPrimeSupply_cast_int_eq_increment
    (R : ℕ) :
    (vfMidIntegerBlockPrimeSupply R : ℤ) =
      (Nat.primeCounting ((R + 1) ^ 2) : ℤ) -
        (Nat.primeCounting (R ^ 2) : ℤ) := by
  have h :=
    vfMidIntegerBlockPrimeSupply_add_primeCounting R
  have hZ :
      (vfMidIntegerBlockPrimeSupply R : ℤ) +
          (Nat.primeCounting (R ^ 2) : ℤ) =
        (Nat.primeCounting ((R + 1) ^ 2) : ℤ) := by
    exact_mod_cast h
  omega

/-- **Exact discrete backlog recurrence.**
The square-endpoint prime/floor-Li backlog moves by actual block supply minus
integer floor-Li block demand. -/
theorem vfMidPrimeFloorLiBacklog_succ
    (R : ℕ) :
    vfMidPrimeFloorLiBacklog (R + 1) =
      vfMidPrimeFloorLiBacklog R +
        ((vfMidIntegerBlockPrimeSupply R : ℤ) -
          vfMidFloorLiBlockSupply R) := by
  unfold vfMidPrimeFloorLiBacklog vfMidFloorLiBlockSupply
  rw [vfMidIntegerBlockPrimeSupply_cast_int_eq_increment]
  ring

/-- Signed integer floor-Li block defect, oriented like the native VF
composite tracking defect: model prime demand minus actual prime supply. -/
def vfMidFloorLiBlockPrimeDefect (R : ℕ) : ℤ :=
  vfMidFloorLiBlockSupply R -
    (vfMidIntegerBlockPrimeSupply R : ℤ)

/-- One floor-Li block defect is minus the increment of the endpoint backlog. -/
theorem vfMidFloorLiBlockPrimeDefect_eq_neg_backlog_increment
    (R : ℕ) :
    vfMidFloorLiBlockPrimeDefect R =
      -(vfMidPrimeFloorLiBacklog (R + 1) -
        vfMidPrimeFloorLiBacklog R) := by
  rw [vfMidPrimeFloorLiBacklog_succ]
  unfold vfMidFloorLiBlockPrimeDefect
  ring

/-- Cumulative integer floor-Li block defect over a square-root range. -/
def vfMidFloorLiDyadicPrimeDefect (A B : ℕ) : ℤ :=
  ∑ r ∈ Finset.Ico A B, vfMidFloorLiBlockPrimeDefect r

/-- **Exact dyadic telescope.**
The cumulative floor-Li block defect is exactly minus the endpoint backlog
increment. -/
theorem vfMidFloorLiDyadicPrimeDefect_eq_neg_backlog_increment
    (A B : ℕ) (hAB : A ≤ B) :
    vfMidFloorLiDyadicPrimeDefect A B =
      -(vfMidPrimeFloorLiBacklog B -
        vfMidPrimeFloorLiBacklog A) := by
  unfold vfMidFloorLiDyadicPrimeDefect
  calc
    (∑ r ∈ Finset.Ico A B, vfMidFloorLiBlockPrimeDefect r) =
        ∑ r ∈ Finset.Ico A B,
          (-(vfMidPrimeFloorLiBacklog (r + 1) -
            vfMidPrimeFloorLiBacklog r)) := by
          apply Finset.sum_congr rfl
          intro r _hr
          exact vfMidFloorLiBlockPrimeDefect_eq_neg_backlog_increment r
    _ = -(∑ r ∈ Finset.Ico A B,
          (vfMidPrimeFloorLiBacklog (r + 1) -
            vfMidPrimeFloorLiBacklog r)) := by
          rw [Finset.sum_neg_distrib]
    _ = -(vfMidPrimeFloorLiBacklog B -
          vfMidPrimeFloorLiBacklog A) := by
          rw [Finset.sum_Ico_sub vfMidPrimeFloorLiBacklog hAB]

/-! ## Native parity-owner realization -/

/-- Integer floor-Li composite demand on the exact post-parity carrier.
There are exactly R odd candidate seats, so the model composite demand is
R minus the integer floor-Li prime demand. -/
def vfMidOddFloorLiCompositeReference (R : ℕ) : ℤ :=
  (R : ℤ) - vfMidFloorLiBlockSupply R

/-- Actual parity-surviving composite population minus the floor-Li integer
composite demand. -/
def vfMidOddFloorLiCompositeDefect (R : ℕ) : ℤ :=
  ((vfMidSquareBandPrefixCompositeSurvivors 2 R).card : ℤ) -
    vfMidOddFloorLiCompositeReference R

/-- **Integer owner-carrier identity.**
Actual composite removal minus floor-Li composite demand is exactly floor-Li
prime demand minus actual prime supply. -/
theorem vfMidOddFloorLiCompositeDefect_eq_blockPrimeDefect
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddFloorLiCompositeDefect R =
      vfMidFloorLiBlockPrimeDefect R := by
  have hpart :=
    vfMidOddActualComposite_card_add_primeSupply R hR
  have hpartZ :
      ((vfMidSquareBandPrefixCompositeSurvivors 2 R).card : ℤ) +
          (vfMidIntegerBlockPrimeSupply R : ℤ) =
        (R : ℤ) := by
    exact_mod_cast hpart
  unfold vfMidOddFloorLiCompositeDefect
    vfMidOddFloorLiCompositeReference
    vfMidFloorLiBlockPrimeDefect
  omega

/-- The same integer defect written directly as the chronological least-prime
owner census minus the floor-Li composite demand. -/
theorem vfMidOddFloorLiCompositeDefect_eq_ownerCensus_sub_reference
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidOddFloorLiCompositeDefect R =
      (∑ p ∈ vfMidSquareBandLateOwnerPrimes 2 R,
        ((vfMidSquareBandCompositeOwner R p).card : ℤ)) -
      vfMidOddFloorLiCompositeReference R := by
  have howners :=
    vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards
      2 R hR
  have hownersZ :
      ((vfMidSquareBandPrefixCompositeSurvivors 2 R).card : ℤ) =
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes 2 R,
          ((vfMidSquareBandCompositeOwner R p).card : ℤ) := by
    exact_mod_cast howners
  unfold vfMidOddFloorLiCompositeDefect
  rw [hownersZ]

/-! ## Deterministic merge back to VF -/

/-- Deterministic floor-Li minus VF discrepancy at a square endpoint. -/
def vfMidFloorLiVFBridge (R : ℕ) : ℝ :=
  liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
    vfMid ((R : ℝ) ^ 2)

/-- The native VF prime error is exactly the integer floor-Li backlog plus the
deterministic floor-Li/VF bridge. -/
theorem vfMidPrimeError_sq_eq_floorLiBacklog_add_bridge
    (R : ℕ) :
    vfMidPrimeError ((R : ℝ) ^ 2) =
      (vfMidPrimeFloorLiBacklog R : ℝ) +
        vfMidFloorLiVFBridge R := by
  have hcount :
      vfMidPrimeCount ((R : ℝ) ^ 2) =
        (Nat.primeCounting (R ^ 2) : ℝ) := by
    have hfloor : ⌊(R : ℝ) ^ 2⌋₊ = R ^ 2 := by
      rw [show (R : ℝ) ^ 2 = ((R ^ 2 : ℕ) : ℝ) by norm_num]
      exact Nat.floor_natCast (R ^ 2)
    unfold vfMidPrimeCount
    rw [hfloor]
  unfold vfMidPrimeError vfMidPrimeFloorLiBacklog
    vfMidFloorLiVFBridge vfMidFloorLiSquarePotential
    liFloorPrimeCountProxy
  rw [hcount]
  push_cast
  ring

/-- **Flooring costs nothing asymptotically in the VF merge.**
At square endpoints, floor-Li differs from VF by at most one plus the already
proved root-scale VF/Li quadrature error. -/
theorem vfMidFloorLiVFBridge_root_bounded :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ R : ℕ, 2 ≤ R →
        |vfMidFloorLiVFBridge R| ≤
          1 + B * (R : ℝ) := by
  rcases vfMidLiRootBounded with ⟨B, hB0, hB⟩
  refine ⟨B, hB0, ?_⟩
  intro R hR
  have h4nat : 4 ≤ R ^ 2 := by nlinarith
  have h4 : (4 : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast h4nat
  have hli := hB ((R : ℝ) ^ 2) h4
  have hR0 : (0 : ℝ) ≤ R := by positivity
  rw [vfMidLiError, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hR0] at hli
  have hround :
      |liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
        vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)| ≤ 1 :=
    liFloorPrimeCountProxy_uniformBounded ((R : ℝ) ^ 2)
  unfold vfMidFloorLiVFBridge
  have hdecomp :
      liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
          vfMid ((R : ℝ) ^ 2) =
        (liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
          vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)) -
        (vfMid ((R : ℝ) ^ 2) -
          vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)) := by
    ring
  rw [hdecomp]
  calc
    |(liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
          vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)) -
        (vfMid ((R : ℝ) ^ 2) -
          vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2))|
        = |(liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
            vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)) +
          -(vfMid ((R : ℝ) ^ 2) -
            vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2))| := by ring
    _ ≤ |liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
            vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)| +
          |-(vfMid ((R : ℝ) ^ 2) -
            vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2))| :=
      abs_add_le _ _
    _ = |liFloorPrimeCountProxy ((R : ℝ) ^ 2) -
            vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)| +
          |vfMid ((R : ℝ) ^ 2) -
            vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)| := by
      rw [abs_neg]
    _ ≤ 1 + B * (R : ℝ) := add_le_add hround hli

/-- **Exact floor-Li/VF dyadic merge.**
The native VF tracking defect equals the integer floor-Li prime defect minus
only the deterministic endpoint bridge increment. -/
theorem vfMidDyadicVFTrackingDefect_eq_floorLiDefect_sub_bridgeIncrement
    {A B : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) (hAB : A ≤ B) :
    vfMidDyadicVFTrackingDefect A B =
      (vfMidFloorLiDyadicPrimeDefect A B : ℝ) -
        (vfMidFloorLiVFBridge B - vfMidFloorLiVFBridge A) := by
  rw [vfMidDyadicVFTrackingDefect_eq_neg_primeError_increment
      hA hB hAB,
    vfMidPrimeError_sq_eq_floorLiBacklog_add_bridge B,
    vfMidPrimeError_sq_eq_floorLiBacklog_add_bridge A]
  have hfloor :=
    vfMidFloorLiDyadicPrimeDefect_eq_neg_backlog_increment A B hAB
  have hfloorR :=
    congrArg (fun z : ℤ => (z : ℝ)) hfloor
  push_cast at hfloorR
  rw [hfloorR]
  ring

/-- Consequently the entire difference between native VF tracking and the
integer floor-Li defect is bounded by the two deterministic endpoint bridges. -/
theorem abs_vfMidDyadicVFTrackingDefect_sub_floorLiDefect_le
    {A B : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) (hAB : A ≤ B) :
    |vfMidDyadicVFTrackingDefect A B -
        (vfMidFloorLiDyadicPrimeDefect A B : ℝ)| ≤
      |vfMidFloorLiVFBridge A| + |vfMidFloorLiVFBridge B| := by
  rw [vfMidDyadicVFTrackingDefect_eq_floorLiDefect_sub_bridgeIncrement
      hA hB hAB]
  have hrewrite :
      (vfMidFloorLiDyadicPrimeDefect A B : ℝ) -
          (vfMidFloorLiVFBridge B - vfMidFloorLiVFBridge A) -
          (vfMidFloorLiDyadicPrimeDefect A B : ℝ) =
        vfMidFloorLiVFBridge A - vfMidFloorLiVFBridge B := by
    ring
  rw [hrewrite]
  calc
    |vfMidFloorLiVFBridge A - vfMidFloorLiVFBridge B|
        = |vfMidFloorLiVFBridge A +
            (-vfMidFloorLiVFBridge B)| := by ring
    _ ≤ |vfMidFloorLiVFBridge A| +
          |-vfMidFloorLiVFBridge B| := abs_add_le _ _
    _ = |vfMidFloorLiVFBridge A| +
          |vfMidFloorLiVFBridge B| := by rw [abs_neg]

/-- The discrepancy between the two tracking coordinates is therefore root
scale on any square-root range: no arithmetic hypothesis enters this bound. -/
theorem vfMidFloorLiVFTrackingCoordinate_root_bridge :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ A B' : ℕ, 2 ≤ A → 2 ≤ B' → A ≤ B' →
        |vfMidDyadicVFTrackingDefect A B' -
            (vfMidFloorLiDyadicPrimeDefect A B' : ℝ)| ≤
          2 + B * ((A : ℝ) + (B' : ℝ)) := by
  rcases vfMidFloorLiVFBridge_root_bounded with ⟨B, hB0, hB⟩
  refine ⟨B, hB0, ?_⟩
  intro A B' hA hB' hAB
  have h0 :=
    abs_vfMidDyadicVFTrackingDefect_sub_floorLiDefect_le hA hB' hAB
  have hA' := hB A hA
  have hB'' := hB B' hB'
  calc
    |vfMidDyadicVFTrackingDefect A B' -
        (vfMidFloorLiDyadicPrimeDefect A B' : ℝ)|
        ≤ |vfMidFloorLiVFBridge A| +
            |vfMidFloorLiVFBridge B'| := h0
    _ ≤ (1 + B * (A : ℝ)) +
          (1 + B * (B' : ℝ)) := add_le_add hA' hB''
    _ = 2 + B * ((A : ℝ) + (B' : ℝ)) := by ring

end RHLean.Analysis
