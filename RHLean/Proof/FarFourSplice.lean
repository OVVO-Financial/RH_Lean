import Mathlib
import RHLean.Proof.StableFarWallUnitRenewalCentering
import RHLean.Proof.PhysicalQ2ExceptionalTerminalSynthesis
import RHLean.Proof.PostRootPartnerMellinInterpolation
import RHLean.Proof.LogSquareCorrectionQ2Tower

/-!
# FAR-4 splice after LOG-MATCH

This file puts the post-#685 conclusion into the exact shape consumed by the
terminal q^2 energy theorem.

There are three deliberately separate layers.

1. `FarFourSplice C` is the literal factor-four inequality on the physical
   frozen/top/far residual.  It is definitionally the quantified body of the
   existing `FrozenTopFarFourEnergyStatement`.
2. Before any norm, the complete stable-far chronology is rewritten as one
   centered q^2-descended carrier plus one explicit terminal remainder.  The
   nonunit strict-crossing renewal is already known to have depth one, so every
   such return lands on the same q^2-descended carrier.  Unit returns are
   centered against the existing far-unit terminal copy.
3. `FarFourQ2TowerEnergySupport C` is the quantitative support interface: the
   centered q^2 tower is charged to the genuine raw q^2 Mertens daughter energy,
   while the explicit terminal remainder is root-scale.  A two-vector
   inequality then gives the exact factor four required by the terminal
   consumer.

Thus the final consumer wiring is a direct corollary.  No triangle inequality
is taken until after the signed carrier normal form has been compiled.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The centered q^2-descended carrier left after every nonunit strict crossing
is routed to its unique next child.  Every occurrence multiplicity is retained
exactly. -/
def farFourQ2CenteredTower (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
    (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
      canonicalMoebiusWeight y.2.1

/-- The only part of the stable-far census not living on the q^2-descended
carrier after one-generation renewal: centered unit returns together with the
already-owned terminal products. -/
def farFourTerminalRemainder (R : ℕ) : ℂ :=
  (∑ p ∈ lowWheelFarPrimeUnitProducts R,
      ((lowWheelFarPrimeQ2UnitCrossingMultiplicity R p : ℂ) - 1)) +
    ∑ n ∈ lowWheelFrozenTopFarOwnedProducts R,
      canonicalMoebiusWeight n

/-- The terminal-product census is the disjoint union of the far-unit baseline
and the already-owned products. -/
theorem lowWheelFarWallTerminalProducts_mass_eq_unit_add_owned (R : ℕ) :
    (∑ n ∈ lowWheelFarWallTerminalProducts R,
        canonicalMoebiusWeight n) =
      (∑ p ∈ lowWheelFarPrimeUnitProducts R,
        canonicalMoebiusWeight p) +
      ∑ n ∈ lowWheelFrozenTopFarOwnedProducts R,
        canonicalMoebiusWeight n := by
  unfold lowWheelFarWallTerminalProducts
  rw [Finset.sum_union (lowWheelFarPrimeUnitProducts_disjoint_owned R)]

/-- **Signed q^2-tower carrier normal form.**

Every nonunit strict crossing has already been proved to descend at its next
canonical owner.  Combining that depth-one renewal with the unit-return
centering gives an exact decomposition of the full frozen/top/far residual:
all nonterminal chronology is supported on the existing q^2-descended carrier,
and every term not on that carrier is displayed explicitly in
`farFourTerminalRemainder`.

No norm, absolute value, density estimate, or Mertens bound occurs here. -/
theorem lowWheelFrozenTopFarResidual_eq_neg_q2CenteredTower_sub_terminal
    (R : ℕ) (hR : 56 ≤ R) :
    lowWheelFrozenTopFarResidual R =
      -farFourQ2CenteredTower R - farFourTerminalRemainder R := by
  have hfar :=
    lowWheelFrozenTopFarResidual_eq_neg_childFarSlices_sub_stableRenewal_sub_terminal
      R hR
  have hcenter :=
    lowWheelFarPrimeChildFar_add_crossingRenewal_add_unitTerminal_eq_centered R
  have hterminal := lowWheelFarWallTerminalProducts_mass_eq_unit_add_owned R
  unfold farFourQ2CenteredTower farFourTerminalRemainder
  rw [hterminal] at hfar
  linear_combination hfar + hcenter

/-- Literal FAR-4 splice with the root-envelope constant exposed as a parameter.
This is the exact shape requested by the terminal consumer. -/
def FarFourSplice (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
      4 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
        rawQ2ChildEnergyReal R q +
      C * (R : ℝ) ^ 2 * K

/-- `FarFourSplice` is not a new criterion: it is exactly the quantified body
of the existing FAR-4 terminal statement. -/
theorem frozenTopFarFourEnergy_iff_exists_nonneg_farFourSplice :
    FrozenTopFarFourEnergyStatement ↔
      ∃ C : ℝ, 0 ≤ C ∧ FarFourSplice C := by
  rfl

/-- Quantitative support interface for the exact carrier normal form.  The first
bound says that the surviving centered chronology is genuinely q^2-recursive;
the second says that the explicitly isolated terminal complement is root-scale.
Neither condition mentions the parent Mertens endpoint. -/
def FarFourQ2TowerEnergySupport (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    ‖farFourQ2CenteredTower R‖ ^ 2 ≤
      2 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
        rawQ2ChildEnergyReal R q ∧
    ‖farFourTerminalRemainder R‖ ^ 2 ≤
      C * (R : ℝ) ^ 2 * K

private theorem norm_add_sq_le_two (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hnorm := norm_add_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u + v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- **Consumer composition.**  Once the surviving signed chronology has q^2
energy support and the terminal complement is root-scale, the literal FAR-4
splice follows immediately.  The factor four comes only from the final
2-vector synthesis after signed reassembly. -/
theorem farFourQ2TowerEnergySupport_implies_splice
    {C : ℝ} (hC : 0 ≤ C)
    (hsupport : FarFourQ2TowerEnergySupport C) :
    FarFourSplice (2 * C) := by
  intro R K hR hK
  rcases hsupport R K hR hK with ⟨hTower, hTerminal⟩
  have hdecomp :=
    lowWheelFrozenTopFarResidual_eq_neg_q2CenteredTower_sub_terminal R hR
  have hnorm := norm_add_sq_le_two
    (farFourQ2CenteredTower R) (farFourTerminalRemainder R)
  have hnorm' :
      ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
        2 * ‖farFourQ2CenteredTower R‖ ^ 2 +
          2 * ‖farFourTerminalRemainder R‖ ^ 2 := by
    rw [hdecomp]
    have heq :
        -farFourQ2CenteredTower R - farFourTerminalRemainder R =
          -(farFourQ2CenteredTower R + farFourTerminalRemainder R) := by ring
    rw [heq, norm_neg]
    exact hnorm
  calc
    ‖lowWheelFrozenTopFarResidual R‖ ^ 2 ≤
        2 * ‖farFourQ2CenteredTower R‖ ^ 2 +
          2 * ‖farFourTerminalRemainder R‖ ^ 2 := hnorm'
    _ ≤ 2 *
          (2 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
            rawQ2ChildEnergyReal R q) +
        2 * (C * (R : ℝ) ^ 2 * K) := by
          gcongr
    _ = 4 * ∑ q ∈ (primesUpTo (R - 1)).erase 2,
          rawQ2ChildEnergyReal R q +
        (2 * C) * (R : ℝ) ^ 2 * K := by ring

/-- The support theorem therefore instantiates the pre-existing FAR-4 terminal
statement. -/
theorem farFourQ2TowerEnergySupport_implies_frozenTopFarFourEnergy
    {C : ℝ} (hC : 0 ≤ C)
    (hsupport : FarFourQ2TowerEnergySupport C) :
    FrozenTopFarFourEnergyStatement := by
  refine ⟨2 * C, by positivity, ?_⟩
  exact farFourQ2TowerEnergySupport_implies_splice hC hsupport

/-- And the already-compiled terminal engine closes RH from that support
interface.  No additional analytic theorem is inserted here. -/
theorem riemannHypothesis_of_farFourQ2TowerEnergySupport
    {C : ℝ} (hC : 0 ≤ C)
    (hsupport : FarFourQ2TowerEnergySupport C) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_frozenTopFarFourEnergy
    (farFourQ2TowerEnergySupport_implies_frozenTopFarFourEnergy hC hsupport)

/-- Pin the arithmetic commutator used by the splice next to the terminal
consumer. -/
theorem farFour_logMatch : LOG_MATCH := log_match

end RHLean.Proof
