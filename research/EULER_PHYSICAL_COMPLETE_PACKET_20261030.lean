import Mathlib
import «research.EULER_ODD_DOUBLING_PACKET_20261030»

/-!
# Original Euler packets: completed ancestry, genuine activation, and principal debt

This module uses the original eulerMuQ and STRICT 1 ≤ a < b < R
factor-pair domain of eulerFractionOffQ; no random coefficients, frozen
high-product source, or positive-energy hypothesis are substituted.

It records the completed (d, 2*d) arithmetic packet, BOTH actual
moving coefficients, each unadmitted owner contribution, the centered
oscillation and the physical principal. A completed odd-doubling packet
cannot be used until its coefficient mismatch and both activation debts
are paid: the exact identities retain all three terms.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Actual unordered Möbius product coefficient at original cutoff R.
Every term is an ORIGINAL pair 1 ≤ a < b < R with a*b=d. -/
def eulerMovingProductCoeff (R d : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1),
    ∑ a ∈ Finset.Icc 1 (b - 1),
      if a * b = d then eulerMuQ b * eulerMuQ a else 0

/-- Completed unordered coefficient: all original factor pairs ab=d.
The upper root d+1 is sufficient for every positive d. -/
def eulerCompletedProductCoeff (d : ℕ) : ℚ :=
  eulerMovingProductCoeff (d + 1) d

/-- The signed mass absent because its larger original factor is not below R. -/
def eulerUnadmittedProductCoeff (R d : ℕ) : ℚ :=
  eulerCompletedProductCoeff d - eulerMovingProductCoeff R d

/-- The literal square-clock fractional column, retaining the actual endpoint. -/
def eulerPacketRemainder (R d : ℕ) : ℚ :=
  ((squareRootEndpoint R % d : ℕ) : ℚ) / (d : ℚ)

/-- Exact next-owner birth: the ONLY new pairs have larger factor b=R. -/
def eulerNewOwnerMass (R d : ℕ) : ℚ :=
  ∑ a ∈ Finset.Icc 1 (R - 1),
    if a * R = d then eulerMuQ R * eulerMuQ a else 0

theorem eulerMovingProductCoeff_succ
    (R d : ℕ) (hR : 1 ≤ R) :
    eulerMovingProductCoeff (R + 1) d =
      eulerMovingProductCoeff R d + eulerNewOwnerMass R d := by
  let F (b : ℕ) : ℚ :=
    ∑ a ∈ Finset.Icc 1 (b - 1),
      if a * b = d then eulerMuQ b * eulerMuQ a else 0
  change (∑ b ∈ Finset.Icc 1 ((R + 1) - 1), F b) =
    (∑ b ∈ Finset.Icc 1 (R - 1), F b) + F R
  have hindex : R + 1 - 1 = (R - 1) + 1 := by omega
  rw [hindex]
  exact Finset.sum_Icc_succ_top (by omega : 1 ≤ R - 1 + 1) F

/-- A modulus cannot acquire a new original pair once the larger factor R
already exceeds the entire product d. -/
theorem eulerNewOwnerMass_eq_zero_of_lt
    (R d : ℕ) (hdR : d < R) :
    eulerNewOwnerMass R d = 0 := by
  unfold eulerNewOwnerMass
  apply Finset.sum_eq_zero
  intro a ha
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have hmul : R ≤ a * R := by
    calc
      R = 1 * R := (one_mul _).symm
      _ ≤ a * R := Nat.mul_le_mul_right R ha1
  have hnot : a * R ≠ d := by omega
  simp [hnot]

theorem eulerMovingProductCoeff_succ_eq_of_lt
    (R d : ℕ) (hdR : d < R) :
    eulerMovingProductCoeff (R + 1) d =
      eulerMovingProductCoeff R d := by
  rw [eulerMovingProductCoeff_succ R d (by omega),
    eulerNewOwnerMass_eq_zero_of_lt R d hdR, add_zero]

/-- All original pairs for d are admitted once d<R. -/
theorem eulerMovingProductCoeff_eq_completed
    (R d : ℕ) (hdR : d < R) :
    eulerMovingProductCoeff R d = eulerCompletedProductCoeff d := by
  have hle : d + 1 ≤ R := by omega
  induction R, hle using Nat.le_induction with
  | base =>
      rfl
  | succ n hn ih =>
      rw [eulerMovingProductCoeff_succ_eq_of_lt n d (by omega)]
      exact ih

theorem eulerUnadmittedProductCoeff_eq_zero_of_lt
    (R d : ℕ) (hdR : d < R) :
    eulerUnadmittedProductCoeff R d = 0 := by
  unfold eulerUnadmittedProductCoeff
  rw [eulerMovingProductCoeff_eq_completed R d hdR]
  ring

/-- Every next-root admission removes exactly the corresponding true owner
mass from the unadmitted coefficient; there is no rounding remainder. -/
theorem eulerUnadmittedProductCoeff_succ
    (R d : ℕ) (hR : 1 ≤ R) :
    eulerUnadmittedProductCoeff (R + 1) d =
      eulerUnadmittedProductCoeff R d - eulerNewOwnerMass R d := by
  unfold eulerUnadmittedProductCoeff
  rw [eulerMovingProductCoeff_succ R d hR]
  ring

/-- Actual original modulus row: both the source weight and the admission
predicate come from eulerFractionOffQ. -/
def eulerOriginalProductRow (R d : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1),
    ∑ a ∈ Finset.Icc 1 (b - 1),
      if a * b = d then
        eulerMuQ b * (eulerMuQ a * eulerFractionQ R a b)
      else 0

/-- Each exact original row is the moving coefficient times the physical
square-clock remainder, even when d≥R. -/
theorem eulerOriginalProductRow_eq_moving
    (R d : ℕ) :
    eulerOriginalProductRow R d =
      eulerMovingProductCoeff R d * eulerPacketRemainder R d := by
  classical
  unfold eulerOriginalProductRow eulerMovingProductCoeff
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hab : a * b = d
  · have ha1 : 0 < a := (Finset.mem_Icc.mp ha).1
    have hb1 : 0 < b := (Finset.mem_Icc.mp hb).1
    simp only [if_pos hab]
    rw [eulerFractionQ_eq_mod_div ha1 hb1]
    simp only [eulerPacketRemainder, hab]
    ring
  · simp [hab]

/-- Physical two-modulus packet from genuine signed moving owners. -/
def eulerPhysicalOddPacket (R d : ℕ) : ℚ :=
  2 * eulerMovingProductCoeff R d * eulerPacketRemainder R d +
  2 * eulerMovingProductCoeff R (2 * d) *
    eulerPacketRemainder R (2 * d)

/-- Exact separation from the completed odd-doubling coefficient relation.
For an odd squareful square modulus the mismatch need not vanish, and so is
retained rather than silently discarding an extra factorization. -/
def eulerDoublingCoeffMismatch (d : ℕ) : ℚ :=
  eulerCompletedProductCoeff (2 * d) + 2 * eulerCompletedProductCoeff d

/-- True signed correction from the ORIGINAL not-yet-admitted factor pairs. -/
def eulerPacketActivationCorrection (R d : ℕ) : ℚ :=
  -2 * eulerUnadmittedProductCoeff R d * eulerPacketRemainder R d -
  2 * eulerUnadmittedProductCoeff R (2 * d) *
    eulerPacketRemainder R (2 * d)

/-- COMPLETE physical packet = odd-doubling binary packet + actual composite
coefficient exception + BOTH genuine moving-ancestry boundary corrections.
Holds for every R,d including squareful moduli. -/
theorem eulerPhysicalOddPacket_exact_decomposition (R d : ℕ) :
    eulerPhysicalOddPacket R d =
      nativeEulerOddDoublingPacket
        (eulerCompletedProductCoeff d) d R +
      2 * eulerDoublingCoeffMismatch d *
        eulerPacketRemainder R (2 * d) +
      eulerPacketActivationCorrection R d := by
  unfold eulerPhysicalOddPacket eulerDoublingCoeffMismatch
    eulerPacketActivationCorrection eulerUnadmittedProductCoeff
    nativeEulerOddDoublingPacket oddDoublingPacket eulerPacketRemainder
  ring

/-- The physical packet always retains its exact original source rows. -/
theorem eulerPhysicalOddPacket_eq_original_rows (R d : ℕ) :
    eulerPhysicalOddPacket R d =
      2 * eulerOriginalProductRow R d +
      2 * eulerOriginalProductRow R (2 * d) := by
  rw [eulerOriginalProductRow_eq_moving,
    eulerOriginalProductRow_eq_moving]
  unfold eulerPhysicalOddPacket
  ring

/-- For R>2d all original component owners are admitted, so there is no
moving-ancestry correction. Coefficient mismatch stays explicit. -/
theorem eulerPacketActivationCorrection_eq_zero
    (R d : ℕ) (hdR : 2 * d < R) :
    eulerPacketActivationCorrection R d = 0 := by
  unfold eulerPacketActivationCorrection
  rw [eulerUnadmittedProductCoeff_eq_zero_of_lt R d (by omega),
    eulerUnadmittedProductCoeff_eq_zero_of_lt R (2 * d) hdR]
  ring

/-! ## Physical principal and centered contributions -/

/-- Positive-root period average, avoiding the exceptional Nat root R=0. -/
def eulerPacketRootPrincipal (d : ℕ) : ℚ :=
  (∑ r ∈ Finset.Icc 1 d, eulerPacketRemainder r d) / (d : ℚ)

/-- Actual centered physical fractional column. -/
def eulerPacketCenteredColumn (R d : ℕ) : ℚ :=
  eulerPacketRemainder R d - eulerPacketRootPrincipal d

/-- True principal contribution with the moving factor-owner weights. -/
def eulerPhysicalPacketPrincipal (R d : ℕ) : ℚ :=
  2 * eulerMovingProductCoeff R d * eulerPacketRootPrincipal d +
  2 * eulerMovingProductCoeff R (2 * d) *
    eulerPacketRootPrincipal (2 * d)

/-- Actual centered packet contribution with the SAME moving weights. -/
def eulerPhysicalPacketCentered (R d : ℕ) : ℚ :=
  2 * eulerMovingProductCoeff R d *
    eulerPacketCenteredColumn R d +
  2 * eulerMovingProductCoeff R (2 * d) *
    eulerPacketCenteredColumn R (2 * d)

/-- Exact principal/centered reconstruction, with no averaging assumption for
the root-dependent coefficient beta_R(d). -/
theorem eulerPhysicalOddPacket_eq_principal_add_centered
    (R d : ℕ) :
    eulerPhysicalOddPacket R d =
      eulerPhysicalPacketPrincipal R d +
        eulerPhysicalPacketCentered R d := by
  unfold eulerPhysicalOddPacket eulerPhysicalPacketPrincipal
    eulerPhysicalPacketCentered eulerPacketCenteredColumn
  ring

/-- Completed physical principal including composite partners. -/
def eulerCompletedPacketPrincipal (d : ℕ) : ℚ :=
  2 * eulerCompletedProductCoeff d * eulerPacketRootPrincipal d +
  2 * eulerCompletedProductCoeff (2 * d) *
    eulerPacketRootPrincipal (2 * d)

/-- Principal payment retains BOTH missing-owner debts, not merely the
mean-zero fluctuation of the centered source. -/
theorem eulerPhysicalPacketPrincipal_exact_activation
    (R d : ℕ) :
    eulerPhysicalPacketPrincipal R d =
      eulerCompletedPacketPrincipal d -
      2 * eulerUnadmittedProductCoeff R d *
        eulerPacketRootPrincipal d -
      2 * eulerUnadmittedProductCoeff R (2 * d) *
        eulerPacketRootPrincipal (2 * d) := by
  unfold eulerPhysicalPacketPrincipal eulerCompletedPacketPrincipal
    eulerUnadmittedProductCoeff
  ring

/-- The residual principal of the binary completed packet, which vanishes
only after verifying the square-clock odd-doubling period identity. -/
def eulerCompletedPacketPrincipalDefect (d : ℕ) : ℚ :=
  eulerCompletedProductCoeff d *
    (2 * eulerPacketRootPrincipal d -
      4 * eulerPacketRootPrincipal (2 * d) + 1)

/-- Full composite principal conservation ledger, retaining both actual
coefficient mismatch and period-mean discrepancy if any. -/
theorem eulerCompletedPacketPrincipal_exact_ledger (d : ℕ) :
    eulerCompletedPacketPrincipal d =
      -eulerCompletedProductCoeff d +
      eulerCompletedPacketPrincipalDefect d +
      2 * eulerDoublingCoeffMismatch d *
        eulerPacketRootPrincipal (2 * d) := by
  unfold eulerCompletedPacketPrincipal eulerCompletedPacketPrincipalDefect
    eulerDoublingCoeffMismatch
  ring

/-- Pointwise binary energy of the completed packet; actual activation and
principal debts are separately retained in the preceding theorems. -/
theorem eulerCompletedOddPacket_conservation
    (d R : ℕ) (hd : 0 < d) :
    (nativeEulerOddDoublingPacket
      (eulerCompletedProductCoeff d) d R +
       eulerCompletedProductCoeff d) ^ 2 =
      eulerCompletedProductCoeff d ^ 2 := by
  exact nativeEulerOddDoublingPacket_centered_sq
    (eulerCompletedProductCoeff d) hd

#print axioms eulerMovingProductCoeff_succ
#print axioms eulerMovingProductCoeff_eq_completed
#print axioms eulerOriginalProductRow_eq_moving
#print axioms eulerPhysicalOddPacket_exact_decomposition
#print axioms eulerPhysicalOddPacket_eq_principal_add_centered
#print axioms eulerPhysicalPacketPrincipal_exact_activation
#print axioms eulerCompletedPacketPrincipal_exact_ledger

end RHLean.Proof
