import Mathlib
import RHLean.Analysis.NativePNTTransfer
import RHLean.Analysis.SquareRootShallowReciprocalCrossing
import RHLean.Proof.StableFarRenewalFinalMismatch

/-!
# Post-#787 macroscopic boundary obstruction

The #787 physical reassembly exposes a cancellation that must be preserved
before energy is taken.  Write, at the square endpoint X_R = R^2 - 1,

* C_R for the complete odd-owner ChildFar mass;
* D_R for the signed sum of the production physical boundary, the explicit
  owner-two centered tower, and the terminal remainder;
* I_R = C_R + D_R.

The exact repository identities imply

  squarePrefixMertens (R - 1) = I_R + finalCompensatedRootBoundary R.

Thus D_R is not an independent error term.  If C_R has a nonzero X/log X
main term while I_R is o(X/log X), then D_R carries the opposite main term.
The generic theorem below records the resulting no-go: no eventual estimate
D_R^2 <= B X_R can hold.

The actual ChildFar PNT asymptotic can be proved separately on its literal
carrier.  This module deliberately separates that arithmetic asymptotic from
the exact cancellation/no-go implication, so future work cannot accidentally
square C_R and D_R separately.
-/

noncomputable section

open Filter
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Complete odd-owner ChildFar signed mass. -/
def post787OddChildFarMass (R : ℕ) : ℂ :=
  ∑ q ∈ (primesUpTo (R - 1)).erase 2,
    ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
      canonicalMoebiusWeight dp.1

/-- The macroscopic signed counterterm that must remain coupled to ChildFar.
This is not a root-scale boundary. -/
def post787MacroscopicCounterterm (R : ℕ) : ℂ :=
  stableFarRenewalProductionSignedBoundaryMass R +
    stableFarRenewalOwnerTwoCenteredTower R +
    farFourTerminalRemainder R

/-- The cancellation-preserving post-#787 interior. -/
def post787CoupledInterior (R : ℕ) : ℂ :=
  post787OddChildFarMass R + post787MacroscopicCounterterm R

/-- Split the all-prime ChildFar column into owner two and the complete odd
owner column. -/
theorem squareEndpointQ2ChildFarSliceColumn_eq_two_add_post787Odd
    (R : ℕ) (hR : 3 ≤ R) :
    squareEndpointQ2ChildFarSliceColumn R =
      (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R 2,
        canonicalMoebiusWeight dp.1) +
      post787OddChildFarMass R := by
  have htwo : 2 ∈ primesUpTo (R - 1) :=
    mem_primesUpTo.mpr ⟨Nat.prime_two, by omega⟩
  have hsplit := Finset.sum_erase_add
    (s := primesUpTo (R - 1))
    (f := fun q =>
      ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
        canonicalMoebiusWeight dp.1) htwo
  unfold squareEndpointQ2ChildFarSliceColumn post787OddChildFarMass
  calc
    (∑ q ∈ primesUpTo (R - 1),
      ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
        canonicalMoebiusWeight dp.1) =
        (∑ q ∈ (primesUpTo (R - 1)).erase 2,
          ∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R q,
            canonicalMoebiusWeight dp.1) +
        (∑ dp ∈ lowWheelFarPrimeQ2ChildFarSlice R 2,
          canonicalMoebiusWeight dp.1) := hsplit.symm
    _ = _ := by ring

/-- Exact cancellation-preserving normal form.  The all-prime q^2
ChildFar column and the renewal/terminal chronology cancel their owner-two
copies, leaving exactly C_R + D_R plus the already root-scale boundary. -/
theorem squarePrefixMertens_eq_post787CoupledInterior_add_rootBoundary
    (R : ℕ) (hR : 56 ≤ R) :
    squarePrefixMertens (R - 1) =
      post787CoupledInterior R + finalCompensatedRootBoundary R := by
  have hfar :=
    squarePrefixMertens_eq_farPopulations_add_rootBoundary R hR
  have hchron :=
    stableFarRenewalColumn_add_terminal_eq_physicalBoundary_add_ownerTwo
      R (by omega)
  have hchild :=
    squareEndpointQ2ChildFarSliceColumn_eq_two_add_post787Odd R (by omega)
  unfold post787CoupledInterior post787MacroscopicCounterterm
  linear_combination hfar + hchron + hchild

/-- The only term separated from the coupled interior is genuinely root-scale. -/
theorem norm_post787RootBoundary_le_ten_root
    (R : ℕ) (hR : 56 ≤ R) :
    ‖finalCompensatedRootBoundary R‖ ≤ 10 * (R : ℝ) :=
  norm_finalCompensatedRootBoundary_le_ten_root R hR

/-- Real coordinates for asymptotic statements.  All three complex quantities
above are real-valued integer casts; taking the real part avoids introducing a
second integer census. -/
def post787OddChildFarReal (R : ℕ) : ℝ :=
  (post787OddChildFarMass R).re

def post787MacroscopicCountertermReal (R : ℕ) : ℝ :=
  (post787MacroscopicCounterterm R).re

def post787CoupledInteriorReal (R : ℕ) : ℝ :=
  post787OddChildFarReal R + post787MacroscopicCountertermReal R

/-- Natural X/log X scaling at the square endpoint. -/
def post787EndpointScale (R : ℕ) : ℝ :=
  Real.log (squareRootEndpoint R : ℝ) / (squareRootEndpoint R : ℝ)

/-- Named arithmetic input: the odd ChildFar column has a positive X/log X
main term.  The intended value is the positive Euler sum described in the
post-#787 PNT audit. -/
def Post787OddChildFarMainTerm (κ : ℝ) : Prop :=
  Tendsto
    (fun R : ℕ => post787OddChildFarReal R * post787EndpointScale R)
    atTop (𝓝 κ)

/-- Named cancellation input: the complete coupled interior has no X/log X
main term. -/
def Post787CoupledInteriorLogNegligible : Prop :=
  Tendsto
    (fun R : ℕ => post787CoupledInteriorReal R * post787EndpointScale R)
    atTop (𝓝 0)

/-- A separate root-energy bound for D_R; the theorem below proves this is
incompatible with a nonzero ChildFar main term plus cancellation in I_R. -/
def Post787CountertermLinearEnergy : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧
    (∀ᶠ R : ℕ in atTop,
      post787MacroscopicCountertermReal R ^ 2 ≤
        B * (squareRootEndpoint R : ℝ))

/-- The counterterm inherits the opposite X/log X main term from the exact
identity I_R = C_R + D_R. -/
theorem post787Counterterm_scaled_tendsto_neg
    {κ : ℝ}
    (hC : Post787OddChildFarMainTerm κ)
    (hI : Post787CoupledInteriorLogNegligible) :
    Tendsto
      (fun R : ℕ =>
        post787MacroscopicCountertermReal R * post787EndpointScale R)
      atTop (𝓝 (-κ)) := by
  have h := hI.sub hC
  convert h using 1
  · funext R
    unfold post787CoupledInteriorReal
    ring
  · ring

/-- Generic analytic no-go used by the post-#787 obstruction: if D*w has a
nonzero limit while X*w^2 tends to zero, D^2 cannot be eventually O(X). -/
theorem no_eventual_linear_energy_of_nonzero_scaled_limit
    (X D w : ℕ → ℝ) {κ : ℝ}
    (hκ : κ ≠ 0)
    (hscaled : Tendsto (fun n => D n * w n) atTop (𝓝 κ))
    (hvanish : Tendsto (fun n => X n * (w n) ^ 2) atTop (𝓝 0)) :
    ¬ (∃ B : ℝ, 0 ≤ B ∧
      (∀ᶠ n : ℕ in atTop, D n ^ 2 ≤ B * X n)) := by
  rintro ⟨B, hB, hbound⟩
  have hleft :
      Tendsto (fun n => (D n * w n) ^ 2) atTop (𝓝 (κ ^ 2)) :=
    hscaled.pow 2
  have hright :
      Tendsto (fun n => B * (X n * (w n) ^ 2)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hvanish)
  have hdiff :
      Tendsto
        (fun n => (D n * w n) ^ 2 - B * (X n * (w n) ^ 2))
        atTop (𝓝 (κ ^ 2)) := by
    simpa using hleft.sub hright
  have hnonpos : κ ^ 2 ≤ 0 := by
    apply le_of_tendsto hdiff
    filter_upwards [hbound] with n hn
    have hw : 0 ≤ w n ^ 2 := sq_nonneg (w n)
    have hmul := mul_le_mul_of_nonneg_right hn hw
    calc
      (D n * w n) ^ 2 - B * (X n * w n ^ 2) ≤ 0 := by
        rw [mul_pow]
        nlinarith [hmul]
  have hpos : 0 < κ ^ 2 := by
    positivity
  exact (not_lt_of_ge hnonpos) hpos

private theorem post787_log_sq_div_natCast_atTop :
    Tendsto
      (fun N : ℕ => (Real.log (N : ℝ)) ^ 2 / (N : ℝ))
      atTop (𝓝 0) := by
  have h := RHLean.Analysis.nativeLog_div_sqrt_natCast_atTop
  have hsq := h.mul h
  rw [zero_mul] at hsq
  refine hsq.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  rw [div_mul_div_comm, Real.mul_self_sqrt hNnonneg]
  ring

/-- The square-endpoint normalization used by the obstruction has vanishing
linear-energy scale: X_R * (log X_R / X_R)^2 -> 0. -/
theorem post787EndpointScale_square_vanish :
    Tendsto
      (fun R : ℕ =>
        (squareRootEndpoint R : ℝ) * post787EndpointScale R ^ 2)
      atTop (𝓝 0) := by
  have h :=
    post787_log_sq_div_natCast_atTop.comp
      squareRootEndpoint_tendsto_atTop
  refine h.congr' ?_
  filter_upwards
      [squareRootEndpoint_tendsto_atTop.eventually_ge_atTop 1]
      with R hX
  have hXne : (squareRootEndpoint R : ℝ) ≠ 0 := by
    positivity
  unfold post787EndpointScale
  field_simp [hXne]
  ring

/-- Post-#787 boundary no-go.  Once the actual ChildFar column has a
nonzero X/log X main term and the coupled interior cancels that main term, the
physical-boundary/owner-two/terminal group cannot have squared amplitude O(X). -/
theorem not_post787CountertermLinearEnergy
    {κ : ℝ} (hκ : 0 < κ)
    (hC : Post787OddChildFarMainTerm κ)
    (hI : Post787CoupledInteriorLogNegligible) :
    ¬ Post787CountertermLinearEnergy := by
  apply no_eventual_linear_energy_of_nonzero_scaled_limit
    (X := fun R => (squareRootEndpoint R : ℝ))
    (D := post787MacroscopicCountertermReal)
    (w := post787EndpointScale)
    (κ := -κ)
  · linarith
  · exact post787Counterterm_scaled_tendsto_neg hC hI
  · exact post787EndpointScale_square_vanish

end RHLean.Proof
