import Mathlib
import «research.CORR4_OAI_RELAXED_REMAINDER_20261024»
import «research.LOW_OWNER_Q2_NEAREST_SQUARE_ENDPOINT»

/-!
# CORR-4: true daughter-to-square rounding and all-integer interpolation

Use the EXISTING nearest-complete-square theorem on the genuine physical
q²-daughter cutoff.  It bounds each signed Mertens shell by sqrt(y), rather
than the looser 2R/q downward-rounding shell. No nontrivial Mobius estimate
is needed.

The square-to-all-integers theorem uses only the trivial |mu(n)|<=1
interval-variation bound. It closes the interpolation for ANY beta>=1/2
with a harmless +2 in the power-envelope constant.

IMPORTANT: the independent source inequality on the full physical B_R
remains OPEN.  This file proves the rounding and interpolation consumers,
not the unproved 9/4 daughter-energy estimate nor an RH improvement.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Genuine daughter energy after rounding the original q² cutoff to its
    *nearest* completed square endpoint; the owner set and source labels do
    not change. -/
def corr4NearestSquareDaughterEnergy (R : ℕ) : ℝ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    ‖lowOwnerNearestSquareMertensAmplitude R q‖ ^ 2

/-- Young inequality at the requested 37/36 split. -/
private theorem corr4_norm_add_sq_le_thirtySeven_thirtySix
    (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤
      (37 / 36 : ℝ) * ‖u‖ ^ 2 + 37 * ‖v‖ ^ 2 := by
  have ht := norm_add_le u v
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have huv := norm_nonneg (u + v)
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg (‖u‖ - 36 * ‖v‖)]

/-- Each actual daughter incurs at most its nearest-square midpoint radius.
    A full real or complex signed daughter remains on the RHS. -/
theorem corr4_daughter_round_to_nearest_square_pointwise
    (R q : ℕ) :
    rawQ2ChildEnergyReal R q ≤
      (37 / 36 : ℝ) * ‖lowOwnerNearestSquareMertensAmplitude R q‖ ^ 2 +
        37 * (roundedQ2ChildRoot R q : ℝ) ^ 2 := by
  have hraw :
      lowOwnerRawMertensAmplitude R q =
        lowOwnerNearestSquareMertensAmplitude R q +
          lowOwnerNearestSquareShellAtom R q := by
    unfold lowOwnerNearestSquareShellAtom
    ring
  have hy := corr4_norm_add_sq_le_thirtySeven_thirtySix
    (lowOwnerNearestSquareMertensAmplitude R q)
    (lowOwnerNearestSquareShellAtom R q)
  rw [← hraw, norm_sq_lowOwnerRawMertensAmplitude] at hy
  have hs := norm_lowOwnerNearestSquareShellAtom_le_roundedRoot R q
  have hs2 :
      ‖lowOwnerNearestSquareShellAtom R q‖ ^ 2 ≤
        (roundedQ2ChildRoot R q : ℝ) ^ 2 := by
    nlinarith [norm_nonneg (lowOwnerNearestSquareShellAtom R q)]
  nlinarith

/-- Exact 37/36 daughter rounding with a deterministic <=629/72 * R²
    price.  Since 629/72≈8.736, this beats the proposed 35 R²
    downward-rounding allowance by roughly a factor of four. -/
theorem corr4_daughter_round_to_square (R : ℕ) :
    canonicalRoughLowQ2DaughterEnergy R ≤
      (37 / 36 : ℝ) * corr4NearestSquareDaughterEnergy R +
        (629 / 72 : ℝ) * (R : ℝ) ^ 2 := by
  have hp :
      canonicalRoughLowQ2DaughterEnergy R ≤
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          ((37 / 36 : ℝ) *
              ‖lowOwnerNearestSquareMertensAmplitude R q‖ ^ 2 +
            37 * (roundedQ2ChildRoot R q : ℝ) ^ 2) := by
    unfold canonicalRoughLowQ2DaughterEnergy
    apply Finset.sum_le_sum
    intro q _hq
    exact corr4_daughter_round_to_nearest_square_pointwise R q
  have hsum :
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        ((37 / 36 : ℝ) *
            ‖lowOwnerNearestSquareMertensAmplitude R q‖ ^ 2 +
          37 * (roundedQ2ChildRoot R q : ℝ) ^ 2)) =
        (37 / 36 : ℝ) * corr4NearestSquareDaughterEnergy R +
          37 * (∑ q ∈ canonicalRoughLowQ2Owners R,
            (roundedQ2ChildRoot R q : ℝ) ^ 2) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  have hroot :=
    lowOwnerRoundedQ2ChildRoot_sq_sum_le_seventeen_over_seventy_two R
  rw [hsum] at hp
  nlinarith

/-- The actual integer Mertens prefix is at most 2R sites beyond the
    immediately preceding completed-square endpoint R²-1, with
    R=floor(sqrt(x+1)). This is unconditional. -/
theorem corr4_mertens_all_integer_shell
    (x : ℕ) :
    ‖mertensSummatory x‖ ≤
      ‖mertensSummatory
        (squareRootEndpoint (Nat.sqrt (x + 1)))‖ +
      2 * ((Nat.sqrt (x + 1) : ℕ) : ℝ) := by
  let R : ℕ := Nat.sqrt (x + 1)
  have hlo : R ^ 2 ≤ x + 1 := Nat.sqrt_le' (x + 1)
  have hhi : x + 1 < (R + 1) ^ 2 := Nat.lt_succ_sqrt' (x + 1)
  have hRpos : 1 ≤ R := by
    by_contra h
    have hz : R = 0 := by omega
    rw [hz] at hhi
    norm_num at hhi
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have he : squareRootEndpoint R + 1 = R ^ 2 := by
    unfold squareRootEndpoint
    omega
  have hend : squareRootEndpoint R ≤ x := by omega
  have hExpand : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
  rw [hExpand] at hhi
  have hgap : x - squareRootEndpoint R ≤ 2 * R := by omega
  have hgapReal :
      ((x - squareRootEndpoint R : ℕ) : ℝ) ≤
        2 * (R : ℝ) := by
    exact_mod_cast hgap
  have hvar :=
    norm_mertensSummatory_sub_le (squareRootEndpoint R) x hend
  change ‖mertensSummatory x‖ ≤
    ‖mertensSummatory (squareRootEndpoint R)‖ + 2 * (R : ℝ)
  calc
    ‖mertensSummatory x‖ =
        ‖(mertensSummatory x -
          mertensSummatory (squareRootEndpoint R)) +
          mertensSummatory (squareRootEndpoint R)‖ := by
            rw [sub_add_cancel]
    _ ≤ ‖mertensSummatory x -
          mertensSummatory (squareRootEndpoint R)‖ +
          ‖mertensSummatory (squareRootEndpoint R)‖ :=
      norm_add_le _ _
    _ ≤ ((x - squareRootEndpoint R : ℕ) : ℝ) +
          ‖mertensSummatory (squareRootEndpoint R)‖ :=
      add_le_add_right hvar _
    _ ≤ ‖mertensSummatory (squareRootEndpoint R)‖ +
          2 * (R : ℝ) := by linarith

/-- FULL all-integer transfer.  Any square-endpoint beta-power envelope
    automatically controls every integer, with only +2 on the constant
    when beta>=1/2.  This has no local-cancellation hypothesis. -/
theorem mertens_all_int_of_square_endpoint
    (β H : ℝ) (hβ : (1 / 2 : ℝ) ≤ β) (hH : 0 ≤ H)
    (hSq : ∀ R : ℕ, 1 ≤ R →
      ‖mertensSummatory (squareRootEndpoint R)‖ ≤
        H * Real.rpow ((R : ℝ) ^ 2) β)
    (x : ℕ) (hx : 1 ≤ x) :
    ‖mertensSummatory x‖ ≤
      (H + 2) * Real.rpow (((x + 1 : ℕ) : ℝ)) β := by
  let R : ℕ := Nat.sqrt (x + 1)
  have hlo : R ^ 2 ≤ x + 1 := Nat.sqrt_le' (x + 1)
  have hhi : x + 1 < (R + 1) ^ 2 := Nat.lt_succ_sqrt' (x + 1)
  have hR : 1 ≤ R := by
    by_contra h
    have hz : R = 0 := by omega
    rw [hz] at hhi
    norm_num at hhi
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hR2real : (1 : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
  have hnonneg : 0 ≤ β := by linarith
  have hRroot :
      (R : ℝ) ≤ Real.rpow ((R : ℝ) ^ 2) β := by
    have h := Real.rpow_le_rpow_of_exponent_le hR2real hβ
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ R)] at h
    exact h
  have hRcast : (R : ℝ) ^ 2 ≤ (((x + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hlo
  have hrootTop :
      Real.rpow ((R : ℝ) ^ 2) β ≤
        Real.rpow (((x + 1 : ℕ) : ℝ)) β :=
    Real.rpow_le_rpow (by positivity) hRcast hnonneg
  have hEnd := hSq R hR
  have hShell := corr4_mertens_all_integer_shell x
  change ‖mertensSummatory x‖ ≤
    ‖mertensSummatory (squareRootEndpoint R)‖ + 2 * (R : ℝ)
    at hShell
  have hPow0 : 0 ≤ Real.rpow ((R : ℝ) ^ 2) β :=
    Real.rpow_nonneg (sq_nonneg _) _
  calc
    ‖mertensSummatory x‖ ≤
        ‖mertensSummatory (squareRootEndpoint R)‖ +
          2 * (R : ℝ) := hShell
    _ ≤ (H + 2) * Real.rpow ((R : ℝ) ^ 2) β := by
      nlinarith [hRroot]
    _ ≤ (H + 2) * Real.rpow (((x + 1 : ℕ) : ℝ)) β := by
      exact mul_le_mul_of_nonneg_left hrootTop (by linarith)

/-- The rounded daughter frame remains strictly contractive, even after
    paying the original 37/36 Young step. -/
theorem corr4_rounded_recursive_coefficient_lt_one :
    ((886 / 225 : ℝ) * (37 / 36) * (211 / 900)) < 1 := by
  norm_num

#print axioms corr4_daughter_round_to_square
#print axioms corr4_mertens_all_integer_shell
#print axioms mertens_all_int_of_square_endpoint
#print axioms corr4_rounded_recursive_coefficient_lt_one

end RHLean.Proof
