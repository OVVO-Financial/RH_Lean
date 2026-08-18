import Mathlib
import RHLean.Analysis.DistinguishedPrimeTransitionSupport

/-!
# Physical centered distinguished-prime operator

The existing physical degree-one centering subtracts the row mean only on the
conditioned nonzero destination sector.  This file records the exact analogue
for the seven-state distinguished-prime support.

For a fixed large prime there is one inactive state and six active slot/sign
labels.  Arithmetic six-site uniqueness already forces every active source row
to vanish on all six active destinations.  Therefore centering *only the active
destination sector* commutes with the arithmetic support restriction: the row
mean of every active source is already zero, so the active-to-active block stays
identically zero.

This is deliberately different from centering the full seven-state constant
mode.  A full mass projection can refill the active-to-active block.  The
active-sector centering below is the normalization compatible with the existing
physical `N - rowMean` sign-sector architecture.

The module does not yet identify a canonical physical `(R,q)` raw coefficient
ledger.  Instead it proves the normalization theorem that such a raw restricted
kernel may use once that extraction is supplied.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RestrictedPrimeTransitionOperator

/-- Sum of one kernel row over the six active destination labels. -/
def restrictedPrimeActiveDestinationSum
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) : ℂ :=
  ∑ t : PrimeActiveLabel, K s (some t)

/-- Uniform row mean on the six active destination labels. -/
def restrictedPrimeActiveDestinationMean
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) : ℂ :=
  restrictedPrimeActiveDestinationSum K s / 6

/-- Center a kernel only on the active destination sector.  The inactive
column is untouched. -/
def centerRestrictedPrimeActiveDestinationSector
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ) :
    SignedPrimeHitState → SignedPrimeHitState → ℂ
  | s, none => K s none
  | s, some t => K s (some t) - restrictedPrimeActiveDestinationMean K s

/-- A restricted active source row has zero total mass on active destinations. -/
@[simp] theorem restrictedPrimeActiveDestinationSum_some_eq_zero
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (hK : IsRestrictedPrimeKernel K)
    (s : PrimeActiveLabel) :
    restrictedPrimeActiveDestinationSum K (some s) = 0 := by
  unfold restrictedPrimeActiveDestinationSum
  apply Finset.sum_eq_zero
  intro t ht
  exact hK s t

/-- Hence its active-sector row mean is exactly zero. -/
@[simp] theorem restrictedPrimeActiveDestinationMean_some_eq_zero
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (hK : IsRestrictedPrimeKernel K)
    (s : PrimeActiveLabel) :
    restrictedPrimeActiveDestinationMean K (some s) = 0 := by
  unfold restrictedPrimeActiveDestinationMean
  rw [restrictedPrimeActiveDestinationSum_some_eq_zero K hK s]
  norm_num

/-- **Centering-sparsity gate.**  Active-sector row centering preserves the exact
thirteen-entry distinguished-prime support. -/
theorem centerRestrictedPrimeActiveDestinationSector_isRestricted
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (hK : IsRestrictedPrimeKernel K) :
    IsRestrictedPrimeKernel
      (centerRestrictedPrimeActiveDestinationSector K) := by
  intro s t
  change
    K (some s) (some t) -
        restrictedPrimeActiveDestinationMean K (some s) = 0
  rw [hK s t, restrictedPrimeActiveDestinationMean_some_eq_zero K hK s]
  ring

/-- Sum of a constant over the six active labels. -/
private theorem sum_primeActiveLabel_const (z : ℂ) :
    (∑ _ : PrimeActiveLabel, z) = 6 * z := by
  classical
  simp [nsmul_eq_mul]

/-- Active-sector centering removes the active destination constant mode on
every source row, without any support assumption. -/
theorem restrictedPrimeActiveDestinationSum_center_eq_zero
    (K : SignedPrimeHitState → SignedPrimeHitState → ℂ)
    (s : SignedPrimeHitState) :
    restrictedPrimeActiveDestinationSum
      (centerRestrictedPrimeActiveDestinationSector K) s = 0 := by
  unfold restrictedPrimeActiveDestinationSum
  change
    (∑ t : PrimeActiveLabel,
      (K s (some t) - restrictedPrimeActiveDestinationMean K s)) = 0
  rw [Finset.sum_sub_distrib, sum_primeActiveLabel_const]
  unfold restrictedPrimeActiveDestinationMean restrictedPrimeActiveDestinationSum
  ring

/-- The kernel of every restricted operator satisfies the certified support. -/
theorem restrictedPrime_coeff_isRestricted
    (A : RestrictedPrimeTransitionOperator) :
    IsRestrictedPrimeKernel A.coeff := by
  intro s t
  rfl

/-- Mean of the six inactive-to-active coefficients. -/
def RestrictedPrimeTransitionOperator.activeDestinationMean
    (A : RestrictedPrimeTransitionOperator) : ℂ :=
  (∑ t : PrimeActiveLabel, A.inactiveToActive t) / 6

/-- Package active-sector centering back into the exact thirteen-coefficient
operator class.  Only the six inactive-to-active coefficients change. -/
def RestrictedPrimeTransitionOperator.activeSectorCentered
    (A : RestrictedPrimeTransitionOperator) :
    RestrictedPrimeTransitionOperator where
  inactiveInactive := A.inactiveInactive
  inactiveToActive := fun t => A.inactiveToActive t - A.activeDestinationMean
  activeToInactive := A.activeToInactive

@[simp] theorem RestrictedPrimeTransitionOperator.activeSectorCentered_inactiveInactive
    (A : RestrictedPrimeTransitionOperator) :
    A.activeSectorCentered.inactiveInactive = A.inactiveInactive := rfl

@[simp] theorem RestrictedPrimeTransitionOperator.activeSectorCentered_inactiveToActive
    (A : RestrictedPrimeTransitionOperator) (t : PrimeActiveLabel) :
    A.activeSectorCentered.inactiveToActive t =
      A.inactiveToActive t - A.activeDestinationMean := rfl

@[simp] theorem RestrictedPrimeTransitionOperator.activeSectorCentered_activeToInactive
    (A : RestrictedPrimeTransitionOperator) (s : PrimeActiveLabel) :
    A.activeSectorCentered.activeToInactive s = A.activeToInactive s := rfl

/-- The packaged operator is coefficient-for-coefficient equal to centering the
raw restricted kernel on the active destination sector. -/
theorem RestrictedPrimeTransitionOperator.activeSectorCentered_coeff_eq
    (A : RestrictedPrimeTransitionOperator)
    (s t : SignedPrimeHitState) :
    A.activeSectorCentered.coeff s t =
      centerRestrictedPrimeActiveDestinationSector A.coeff s t := by
  have hA : IsRestrictedPrimeKernel A.coeff :=
    restrictedPrime_coeff_isRestricted A
  rcases s with _ | s
  · rcases t with _ | t
    · rfl
    · change
        A.inactiveToActive t - A.activeDestinationMean =
          A.inactiveToActive t -
            restrictedPrimeActiveDestinationMean A.coeff none
      congr 1
      unfold RestrictedPrimeTransitionOperator.activeDestinationMean
        restrictedPrimeActiveDestinationMean
        restrictedPrimeActiveDestinationSum
  · rcases t with _ | t
    · rfl
    · change
        0 = A.coeff (some s) (some t) -
          restrictedPrimeActiveDestinationMean A.coeff (some s)
      rw [hA s t, restrictedPrimeActiveDestinationMean_some_eq_zero A.coeff hA s]
      ring

/-- The six centered inactive-to-active coefficients have exactly zero sum. -/
theorem RestrictedPrimeTransitionOperator.sum_activeSectorCentered_inactiveToActive_eq_zero
    (A : RestrictedPrimeTransitionOperator) :
    (∑ t : PrimeActiveLabel,
      A.activeSectorCentered.inactiveToActive t) = 0 := by
  change
    (∑ t : PrimeActiveLabel,
      (A.inactiveToActive t - A.activeDestinationMean)) = 0
  rw [Finset.sum_sub_distrib, sum_primeActiveLabel_const]
  unfold RestrictedPrimeTransitionOperator.activeDestinationMean
  ring

/-- Equivalently, the active constant input mode is killed before any norm is
taken. -/
theorem RestrictedPrimeTransitionOperator.activeSectorCentered_activeInputForm_const_eq_zero
    (A : RestrictedPrimeTransitionOperator) :
    A.activeSectorCentered.activeInputForm (fun _ => 1) = 0 := by
  unfold RestrictedPrimeTransitionOperator.activeInputForm
  simp only [mul_one]
  exact A.sum_activeSectorCentered_inactiveToActive_eq_zero

end RHLean.Analysis
