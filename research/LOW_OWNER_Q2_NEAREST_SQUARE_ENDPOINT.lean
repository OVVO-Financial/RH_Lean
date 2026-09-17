import Mathlib
import RHLean.Analysis.SquarePrefixMertensBridge
import RHLean.Proof.SignedTransportAmplificationAudit
import «research.LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE»

/-!
# Nearest-square reduction of the reciprocal q² daughter column

A literal q² daughter cutoff need not itself be a complete square endpoint.
The existing terminal route rounds every daughter downward and then pays a
one-sided shell after squaring.  This file instead uses the exact midpoint
geometry of one square block *before* squaring.

For an arbitrary integer `x`, put `s = floor(sqrt x)`.  The two adjacent
complete-square endpoints are

  s² - 1,   (s+1)² - 1.

The integer square block has odd length `2s+1`, so its midpoint is a
half-integer.  Hence there is a canonical nearest endpoint: use the lower
endpoint for `x < s²+s`, and the upper endpoint otherwise.  The chosen endpoint
is always within `s` integer steps.

Applied to `Y_q = floor((R²-1)/q²)`, the reciprocal daughter column therefore
splits exactly into

  reciprocal completed-square endpoints + reciprocal midpoint shells.

The shell is bounded at the amplitude level.  Combining the nearest-endpoint
radius with the already-compiled odd-prime reciprocal-square budget and the
rounded-root square budget gives

  ||shell|| <= R/4,

hence shell energy at most `R²/16`.  No Cauchy--Schwarz is applied to physical
first-owner cells and no clipped `C²` term is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Canonical completed-square endpoint nearest to `x`.  Because the square
block has odd integer length, the midpoint lies at a half-integer and there is
no tie. -/
def q2NearestSquareEndpoint (x : ℕ) : ℕ :=
  let s := Nat.sqrt x
  if x < s ^ 2 + s then squareRootEndpoint s
  else squareRootEndpoint (s + 1)

/-- Below the half-integer midpoint the nearest completed-square endpoint is the
lower one. -/
theorem q2NearestSquareEndpoint_eq_lower
    {x : ℕ}
    (hmid : x < (Nat.sqrt x) ^ 2 + Nat.sqrt x) :
    q2NearestSquareEndpoint x = squareRootEndpoint (Nat.sqrt x) := by
  simp [q2NearestSquareEndpoint, hmid]

/-- At or above the first integer after the midpoint the nearest endpoint is the
upper completed-square endpoint. -/
theorem q2NearestSquareEndpoint_eq_upper
    {x : ℕ}
    (hmid : (Nat.sqrt x) ^ 2 + Nat.sqrt x ≤ x) :
    q2NearestSquareEndpoint x = squareRootEndpoint (Nat.sqrt x + 1) := by
  simp [q2NearestSquareEndpoint, Nat.not_lt.mpr hmid]

/-- **Midpoint radius theorem.**  Mertens at an arbitrary integer prefix differs
from Mertens at its canonical nearest completed-square endpoint by at most the
square-block half-radius `floor(sqrt x)`. -/
theorem norm_mertensSummatory_sub_nearestSquareEndpoint_le_sqrt
    (x : ℕ) :
    ‖mertensSummatory x - mertensSummatory (q2NearestSquareEndpoint x)‖ ≤
      (Nat.sqrt x : ℝ) := by
  let s := Nat.sqrt x
  have hs2 : s ^ 2 ≤ x := by
    dsimp [s]
    exact Nat.sqrt_le' x
  by_cases hmid : x < s ^ 2 + s
  · have hend : q2NearestSquareEndpoint x = squareRootEndpoint s := by
      simp [q2NearestSquareEndpoint, s, hmid]
    rw [hend]
    have hlow : squareRootEndpoint s ≤ x := by
      unfold squareRootEndpoint
      exact (Nat.sub_le _ _).trans hs2
    have hgapNat : x - squareRootEndpoint s ≤ s := by
      unfold squareRootEndpoint
      omega
    have hgapReal : ((x - squareRootEndpoint s : ℕ) : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hgapNat
    have hvar := norm_mertensSummatory_sub_le (squareRootEndpoint s) x hlow
    exact hvar.trans hgapReal
  · have hmid' : s ^ 2 + s ≤ x := Nat.le_of_not_gt hmid
    have hend : q2NearestSquareEndpoint x = squareRootEndpoint (s + 1) := by
      simp [q2NearestSquareEndpoint, s, hmid]
    rw [hend]
    have hxlt : x < (s + 1) ^ 2 := by
      dsimp [s]
      exact Nat.lt_succ_sqrt' x
    have hupper : x ≤ squareRootEndpoint (s + 1) := by
      unfold squareRootEndpoint
      omega
    have hsquare : (s + 1) ^ 2 = s ^ 2 + 2 * s + 1 := by ring
    have hgapNat : squareRootEndpoint (s + 1) - x ≤ s := by
      unfold squareRootEndpoint
      rw [hsquare]
      omega
    have hgapReal :
        ((squareRootEndpoint (s + 1) - x : ℕ) : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hgapNat
    have hvar := norm_mertensSummatory_sub_le x (squareRootEndpoint (s + 1)) hupper
    rw [norm_sub_rev] at hvar
    exact hvar.trans hgapReal

/-- Completed-square endpoint amplitude attached to one literal q² daughter. -/
def lowOwnerNearestSquareMertensAmplitude (R q : ℕ) : ℂ :=
  (((mertensSummatoryInt
    (q2NearestSquareEndpoint (rawQ2ChildCutoff R q)) : ℤ) : ℂ))

/-- Oriented incomplete-square shell left after replacing a literal q² daughter
by its nearest completed-square endpoint. -/
def lowOwnerNearestSquareShellAtom (R q : ℕ) : ℂ :=
  lowOwnerRawMertensAmplitude R q -
    lowOwnerNearestSquareMertensAmplitude R q

/-- Reciprocal column of nearest completed-square daughter endpoints. -/
def lowOwnerNearestSquareReciprocalColumn (R : ℕ) : ℂ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    (1 / (q : ℂ)) * lowOwnerNearestSquareMertensAmplitude R q

/-- Reciprocal column of the oriented midpoint shells. -/
def lowOwnerNearestSquareReciprocalShell (R : ℕ) : ℂ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    (1 / (q : ℂ)) * lowOwnerNearestSquareShellAtom R q

/-- **Exact amplitude decomposition.**  The literal reciprocal daughter column
is the nearest completed-square endpoint column plus the signed midpoint shell,
before any norm or square is taken. -/
theorem lowOwnerReciprocalMertensColumn_eq_nearestSquare_add_shell
    (R : ℕ) :
    lowOwnerReciprocalMertensColumn R =
      lowOwnerNearestSquareReciprocalColumn R +
        lowOwnerNearestSquareReciprocalShell R := by
  unfold lowOwnerReciprocalMertensColumn
    lowOwnerNearestSquareReciprocalColumn
    lowOwnerNearestSquareReciprocalShell
    lowOwnerNearestSquareShellAtom
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  ring

/-- Every individual oriented midpoint shell has norm at most the rounded q²
child root. -/
theorem norm_lowOwnerNearestSquareShellAtom_le_roundedRoot
    (R q : ℕ) :
    ‖lowOwnerNearestSquareShellAtom R q‖ ≤
      (roundedQ2ChildRoot R q : ℝ) := by
  unfold lowOwnerNearestSquareShellAtom
    lowOwnerRawMertensAmplitude lowOwnerNearestSquareMertensAmplitude
  rw [mertensSummatoryInt_cast, mertensSummatoryInt_cast]
  simpa [roundedQ2ChildRoot, rawQ2ChildCutoff] using
    norm_mertensSummatory_sub_nearestSquareEndpoint_le_sqrt
      (rawQ2ChildCutoff R q)

/-- The odd-prime reciprocal-square budget restricted to the genuinely
recursive low-owner sector. -/
theorem lowOwnerReciprocalSquareBudgetReal_le_quarter (R : ℕ) :
    (∑ q ∈ canonicalRoughLowQ2Owners R,
      (1 : ℝ) / (q : ℝ) ^ 2) ≤ 1 / 4 := by
  have hsub : canonicalRoughLowQ2Owners R ⊆
      (primesUpTo (R - 1)).erase 2 := Finset.sdiff_subset
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 : ℝ) / (q : ℝ) ^ 2) ≤
        ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          (1 : ℝ) / (q : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q _hq _hnot
      positivity
    _ ≤ 1 / 4 := oddPrimeOwnerReciprocalSquareBudgetReal_le_quarter (R - 1)

/-- The rounded-root square budget also restricts monotonically to the low-owner
sector. -/
theorem lowOwnerRoundedQ2ChildRoot_sq_sum_le_seventeen_over_seventy_two
    (R : ℕ) :
    (∑ q ∈ canonicalRoughLowQ2Owners R,
      (roundedQ2ChildRoot R q : ℝ) ^ 2) ≤
        (17 : ℝ) / 72 * (R : ℝ) ^ 2 := by
  have hsub : canonicalRoughLowQ2Owners R ⊆
      (primesUpTo (R - 1)).erase 2 := Finset.sdiff_subset
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R,
        (roundedQ2ChildRoot R q : ℝ) ^ 2) ≤
        ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          (roundedQ2ChildRoot R q : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q _hq _hnot
      positivity
    _ ≤ (17 : ℝ) / 72 * (R : ℝ) ^ 2 :=
      sum_roundedQ2ChildRoot_sq_le_seventeen_over_seventy_two R

/-- **Nearest-square shell bound.**  Replacing every genuine reciprocal q²
daughter by its canonical nearest completed-square endpoint costs at most
`R/4` in amplitude. -/
theorem norm_lowOwnerNearestSquareReciprocalShell_le_quarter_root
    (R : ℕ) :
    ‖lowOwnerNearestSquareReciprocalShell R‖ ≤ (R : ℝ) / 4 := by
  have hsub : canonicalRoughLowQ2Owners R ⊆
      (primesUpTo (R - 1)).erase 2 := Finset.sdiff_subset
  have htri :
      ‖lowOwnerNearestSquareReciprocalShell R‖ ≤
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) * (roundedQ2ChildRoot R q : ℝ) := by
    unfold lowOwnerNearestSquareReciprocalShell
    calc
      ‖∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℂ)) * lowOwnerNearestSquareShellAtom R q‖ ≤
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          ‖(1 / (q : ℂ)) * lowOwnerNearestSquareShellAtom R q‖ :=
        norm_sum_le _ _
      _ ≤ ∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) * (roundedQ2ChildRoot R q : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqpos : 0 < q :=
          (mem_primesUpTo.mp (Finset.mem_erase.mp (hsub hq)).2).1.pos
        have hqnorm : ‖(1 / (q : ℂ))‖ = (1 : ℝ) / (q : ℝ) := by
          rw [norm_div, norm_one, Complex.norm_natCast]
        rw [norm_mul, hqnorm]
        exact mul_le_mul_of_nonneg_left
          (norm_lowOwnerNearestSquareShellAtom_le_roundedRoot R q)
          (by positivity)
  have hsum0 :
      0 ≤ ∑ q ∈ canonicalRoughLowQ2Owners R,
        ((1 : ℝ) / (q : ℝ)) * (roundedQ2ChildRoot R q : ℝ) := by
    apply Finset.sum_nonneg
    intro q hq
    have hqpos : 0 < q :=
      (mem_primesUpTo.mp (Finset.mem_erase.mp (hsub hq)).2).1.pos
    positivity
  have htriSq :
      ‖lowOwnerNearestSquareReciprocalShell R‖ ^ 2 ≤
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) * (roundedQ2ChildRoot R q : ℝ)) ^ 2 := by
    nlinarith [norm_nonneg (lowOwnerNearestSquareReciprocalShell R)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (R := ℝ) (canonicalRoughLowQ2Owners R)
    (fun q => (1 : ℝ) / (q : ℝ))
    (fun q => (roundedQ2ChildRoot R q : ℝ))
  have hbudget := lowOwnerReciprocalSquareBudgetReal_le_quarter R
  have hroot :=
    lowOwnerRoundedQ2ChildRoot_sq_sum_le_seventeen_over_seventy_two R
  have hroot0 :
      0 ≤ ∑ q ∈ canonicalRoughLowQ2Owners R,
        (roundedQ2ChildRoot R q : ℝ) ^ 2 := by positivity
  have hprod :
      (∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) ^ 2) *
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          (roundedQ2ChildRoot R q : ℝ) ^ 2) ≤
        (R : ℝ) ^ 2 / 16 := by
    have hbudget' :
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) ^ 2) ≤ 1 / 4 := by
      calc
        (∑ q ∈ canonicalRoughLowQ2Owners R,
            ((1 : ℝ) / (q : ℝ)) ^ 2) =
            ∑ q ∈ canonicalRoughLowQ2Owners R,
              (1 : ℝ) / (q : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro q _hq
          ring
        _ ≤ 1 / 4 := hbudget
    calc
      (∑ q ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) ^ 2) *
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          (roundedQ2ChildRoot R q : ℝ) ^ 2) ≤
        (1 / 4 : ℝ) *
          (∑ q ∈ canonicalRoughLowQ2Owners R,
            (roundedQ2ChildRoot R q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hbudget' hroot0
      _ ≤ (1 / 4 : ℝ) *
          ((17 : ℝ) / 72 * (R : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hroot (by norm_num)
      _ ≤ (R : ℝ) ^ 2 / 16 := by
        nlinarith [sq_nonneg (R : ℝ)]
  have hsq :
      ‖lowOwnerNearestSquareReciprocalShell R‖ ^ 2 ≤
        (R : ℝ) ^ 2 / 16 :=
    htriSq.trans (hcs.trans hprod)
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  nlinarith [norm_nonneg (lowOwnerNearestSquareReciprocalShell R)]

/-- Energy form of the preceding amplitude shell bound. -/
theorem norm_sq_lowOwnerNearestSquareReciprocalShell_le_root_sq_sixteen
    (R : ℕ) :
    ‖lowOwnerNearestSquareReciprocalShell R‖ ^ 2 ≤
      (R : ℝ) ^ 2 / 16 := by
  have h := norm_lowOwnerNearestSquareReciprocalShell_le_quarter_root R
  nlinarith [norm_nonneg (lowOwnerNearestSquareReciprocalShell R)]

end RHLean.Proof
