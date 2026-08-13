import Mathlib
import RHLean.Analysis.PrimeSieveReciprocalChildVariance

/-!
# Classical dyadic quadratic variation route for the reciprocal prime discrepancy

The child-interval variance route isolates the remaining base-eight packet input
as a sign-blind local `L2` statement.  This module removes the last reciprocal
sum notation from that premise.

Write

`D(d) = pi(max y (floor (x / d))) - Li(max y (floor (x / d)))`.

At every midpoint node `[a,b)` with split `m`, the child-interval variance is
exactly

`(b-a) * (||D(a)-D(m)||^2 + ||D(m)-D(b)||^2)`.

Iterating this identity down the same midpoint tree identifies the complete
base-eight child-variance square function with a classical dyadic quadratic
variation of `pi-Li` along the reciprocal lattice.  Thus the analytic premise
can be stated without packet residuals, reciprocal interval sums, or Mobius
weights.

No prime-distribution estimate is proved here.  The contribution is an exact
change of coordinates and the resulting independent entrances into the existing
packet, chord, Abel, and RH architectures.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Recursive dyadic quadratic variation of the clipped classical discrepancy
`D(d) = pi(max y (x/d)) - Li(max y (x/d))` over the midpoint tree. -/
def primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation
    (y x : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0, _a, _b => 0
  | depth + 1, a, b =>
      if a + 1 < b then
        let m := dyadicPacketMidpoint a b
        ((b - a : ℕ) : ℝ) *
            (‖primeSieveDyadicClippedDiscrepancy y x a -
                primeSieveDyadicClippedDiscrepancy y x m‖ ^ 2 +
              ‖primeSieveDyadicClippedDiscrepancy y x m -
                primeSieveDyadicClippedDiscrepancy y x b‖ ^ 2) +
          primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation
            y x depth a m +
          primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation
            y x depth m b
      else 0

/-- On every reciprocal-support interval, the recursive sign-blind child
variance is exactly the classical clipped-discrepancy quadratic variation. -/
theorem primeSieveReciprocalLowFrequencyChildIntervalVariance_eq_clippedQuadraticVariation
    (y x depth a b : ℕ)
    (ha : 1 ≤ a)
    (hb : b ≤ x / (y + 1) + 1) :
    primeSieveReciprocalLowFrequencyChildIntervalVariance y x depth a b =
      primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation
        y x depth a b := by
  induction depth generalizing a b with
  | zero => rfl
  | succ depth ih =>
      by_cases hsplit : a + 1 < b
      · let m := dyadicPacketMidpoint a b
        have hm : a < m ∧ m < b := by
          dsimp [m, dyadicPacketMidpoint]
          omega
        have hm1 : 1 ≤ m := ha.trans hm.1.le
        have hmB : m ≤ x / (y + 1) + 1 := hm.2.le.trans hb
        have hnode :=
          primeSieveReciprocalChildIntervalVariance_eq_clippedDiscrepancyDrops
            (y := y) (x := x) (a := a) (m := m) (b := b)
            ha hm.1.le hm.2.le hb
        have hleft := ih a m ha hmB
        have hright := ih m b hm1 hb
        simp only [primeSieveReciprocalLowFrequencyChildIntervalVariance,
          primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation,
          hsplit, if_true]
        change
          primeSieveReciprocalChildIntervalVariance y x a m b +
              primeSieveReciprocalLowFrequencyChildIntervalVariance
                y x depth a m +
              primeSieveReciprocalLowFrequencyChildIntervalVariance
                y x depth m b =
            ((b - a : ℕ) : ℝ) *
                (‖primeSieveDyadicClippedDiscrepancy y x a -
                    primeSieveDyadicClippedDiscrepancy y x m‖ ^ 2 +
                  ‖primeSieveDyadicClippedDiscrepancy y x m -
                    primeSieveDyadicClippedDiscrepancy y x b‖ ^ 2) +
              primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation
                y x depth a m +
              primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation
                y x depth m b
        rw [hnode, hleft, hright]
      · simp [primeSieveReciprocalLowFrequencyChildIntervalVariance,
          primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation, hsplit]

/-- Global dyadic quadratic variation through depth `J`, summed over all
occupied reciprocal dyadic blocks. -/
def primeSieveClippedDiscrepancyLowFrequencyQuadraticVariationSquareFunction
    (y x J : ℕ) : ℝ :=
  ∑ j ∈ primeSieveDyadicBlockIndices y x,
    primeSieveClippedDiscrepancyLowFrequencyQuadraticVariation y x (min J j)
      (primeSieveDyadicBlockLeft j)
      (primeSieveDyadicBlockRight y x j + 1)

/-- The global classical quadratic variation is exactly the child-interval
variance square function. -/
theorem primeSieveClippedDiscrepancyLowFrequencyQuadraticVariationSquareFunction_eq_childIntervalVariance
    (y x J : ℕ) :
    primeSieveClippedDiscrepancyLowFrequencyQuadraticVariationSquareFunction
        y x J =
      primeSieveReciprocalLowFrequencyChildIntervalVarianceSquareFunction
        y x J := by
  unfold primeSieveClippedDiscrepancyLowFrequencyQuadraticVariationSquareFunction
    primeSieveReciprocalLowFrequencyChildIntervalVarianceSquareFunction
  apply Finset.sum_congr rfl
  intro j _hj
  have hleft1 : 1 ≤ primeSieveDyadicBlockLeft j := by
    simpa [primeSieveDyadicBlockLeft] using (Nat.one_le_pow' j 1)
  have hright :
      primeSieveDyadicBlockRight y x j + 1 ≤ x / (y + 1) + 1 := by
    unfold primeSieveDyadicBlockRight
    exact Nat.add_le_add_right
      (min_le_left (x / (y + 1)) (2 ^ (j + 1) - 1)) 1
  exact
    (primeSieveReciprocalLowFrequencyChildIntervalVariance_eq_clippedQuadraticVariation
      y x (min J j) (primeSieveDyadicBlockLeft j)
        (primeSieveDyadicBlockRight y x j + 1) hleft1 hright).symm

/-- Base-eight successor version of the classical clipped-discrepancy quadratic
variation square function. -/
def primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction
    (k x : ℕ) : ℝ :=
  primeSieveClippedDiscrepancyLowFrequencyQuadraticVariationSquareFunction
    (primorialPNTPrimeSieveCutoff k) x
    (dyadicPacketBaseEightCutoff k x + 1)

/-- At the base-eight successor cutoff the classical quadratic variation is
literally the sign-blind child-interval variance square function from #332. -/
theorem primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction_eq_childIntervalVariance
    (k x : ℕ) :
    primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction k x =
      primeSieveBaseEightChildIntervalVarianceSquareFunction k x := by
  simpa [primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction,
    primeSieveBaseEightChildIntervalVarianceSquareFunction] using
    primeSieveClippedDiscrepancyLowFrequencyQuadraticVariationSquareFunction_eq_childIntervalVariance
      (primorialPNTPrimeSieveCutoff k) x
      (dyadicPacketBaseEightCutoff k x + 1)

/-- Critical block-uniform bound for the classical reciprocal-lattice dyadic
quadratic variation of `pi-Li`. -/
def DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k x : ℕ),
        2 ≤ k →
        primorialBlockLower k ≤ x →
        x ≤ primorialBlockUpper k →
        primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction
            k x ≤
          C * Real.rpow ((x : ℝ) + 1) (1 + ε)

/-- The classical `pi-Li` dyadic-variation premise is exactly equivalent to the
sign-blind child-interval variance premise. -/
theorem dyadicPrimeClippedDiscrepancyQuadraticVariationBlockBounded_iff_childIntervalVariance :
    DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement ↔
      DyadicPrimeReciprocalLowFrequencyChildIntervalVarianceBlockBoundedStatement := by
  constructor
  · intro hQ ε hε
    obtain ⟨C, hC, hQb⟩ := hQ ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    have h := hQb k x hk hlow hup
    rw [primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction_eq_childIntervalVariance]
      at h
    exact h
  · intro hV ε hε
    obtain ⟨C, hC, hVb⟩ := hV ε hε
    refine ⟨C, hC, ?_⟩
    intro k x hk hlow hup
    have h := hVb k x hk hlow hup
    rw [primeSieveBaseEightClippedDiscrepancyQuadraticVariationSquareFunction_eq_childIntervalVariance]
    exact h

/-- A classical `pi-Li` dyadic-variation estimate therefore controls the full
base-eight recursive packet tree. -/
theorem dyadicPacketTreeEnergyBlockBounded_of_baseEightClippedDiscrepancyQuadraticVariation
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (k x : ℕ),
          2 ≤ k →
          primorialBlockLower k ≤ x →
          x ≤ primorialBlockUpper k →
          primeSieveDyadicPacketTreeEnergy
              (primorialPNTPrimeSieveCutoff k) x ≤
            C * Real.rpow ((x : ℝ) + 1) (1 + ε) :=
  dyadicPacketTreeEnergyBlockBounded_of_baseEightReciprocalChildIntervalVariance
    (dyadicPrimeClippedDiscrepancyQuadraticVariationBlockBounded_iff_childIntervalVariance.mp hQ)

/-- The same classical variation premise implies the older dyadic chord-energy
criterion for `pi-Li`. -/
theorem dyadicPrimeDiscrepancyChordEnergyBlockBounded_of_baseEightClippedDiscrepancyQuadraticVariation
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement) :
    DyadicPrimeDiscrepancyChordEnergyBlockBoundedStatement :=
  dyadicPrimeDiscrepancyChordEnergyBlockBounded_of_baseEightReciprocalChildIntervalVariance
    (dyadicPrimeClippedDiscrepancyQuadraticVariationBlockBounded_iff_childIntervalVariance.mp hQ)

/-- The same classical variation premise also implies the boundary-free Abel
potential energy criterion. -/
theorem dyadicAbelPotentialEnergyBlockBounded_of_baseEightClippedDiscrepancyQuadraticVariation
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement) :
    DyadicAbelPotentialEnergyBlockBoundedStatement :=
  dyadicAbelPotentialEnergyBlockBounded_of_baseEightReciprocalChildIntervalVariance
    (dyadicPrimeClippedDiscrepancyQuadraticVariationBlockBounded_iff_childIntervalVariance.mp hQ)

/-- RH entrance through the direct base-eight packet route, with the only packet
input stated as classical dyadic quadratic variation of `pi-Li`. -/
theorem riemannHypothesis_of_baseEightClippedDiscrepancyQuadraticVariationPackage
    (hC : DyadicCoherentChannelRHScale)
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement :=
  riemannHypothesis_of_baseEightReciprocalChildIntervalVariancePackage hC
    (dyadicPrimeClippedDiscrepancyQuadraticVariationBlockBounded_iff_childIntervalVariance.mp hQ)
    hD

/-- Independent RH entrance through the older chord/Abel route, driven by the
same classical `pi-Li` dyadic quadratic variation premise. -/
theorem riemannHypothesis_of_baseEightClippedDiscrepancyQuadraticVariationChordPackage
    (hC : DyadicCoherentChannelRHScale)
    (hQ : DyadicPrimeClippedDiscrepancyQuadraticVariationBlockBoundedStatement)
    (hD : DyadicMobiusDispersionBlockBoundedStatement) :
    RiemannHypothesisStatement :=
  riemannHypothesis_of_baseEightReciprocalChildIntervalVarianceChordPackage hC
    (dyadicPrimeClippedDiscrepancyQuadraticVariationBlockBounded_iff_childIntervalVariance.mp hQ)
    hD

end RHLean.Analysis
