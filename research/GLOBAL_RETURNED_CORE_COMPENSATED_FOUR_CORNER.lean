import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNED_CELL_TELESCOPE»
import «research.GLOBAL_RETURNED_CORE_WEIGHTED_GRAM»

/-!
# Compensated owner square as the actual AMP four-corner mass

The signed cell telescope leaves one positive-looking complete term,
`CompensatedInterior^2`.  This file does not estimate it.  Instead it expands
that square on the admitted p-free parent fibre and identifies every ordered
atom with the already-compiled complete fresh-prime four-corner mass of the
actual AMP site weight.

Thus the complete term is not a new energy object: it is literally the physical
owner-square object whose one-dimensional factors are

  daughterCrossing - rootCrossing.

No Cauchy--Schwarz, triangle inequality, independence, or packetwise norm is
introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- One signed compensated site on the admitted p-free parent fibre. -/
def lowOwnerFirstOwnerCompensatedSite
    (R p a : ℕ) : ℝ :=
  (lowOwnerDaughterCrossingWeight R p a -
      lowOwnerRootCrossingIndicator R p a) * realMoebiusStep a

/-- The compensated interior amplitude is the sum of its literal signed sites. -/
theorem lowOwnerFirstOwnerCompensatedInteriorAmplitude_eq_sum_sites
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerCompensatedInteriorAmplitude R p sig =
      ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerFirstOwnerCompensatedSite R p a := by
  rfl

/-- Every admitted base site is p-free. -/
theorem lowOwnerFirstOwnerAdmittedBase_not_dvd
    {R p a : ℕ} {sig : Finset ℕ}
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig) :
    ¬ p ∣ a := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2.2

/-- **Atomic identification.**  The product of two compensated signed parent
sites is exactly the complete fresh-prime four-corner mass of the actual AMP
weight. -/
theorem lowOwnerFirstOwnerCompensatedSite_mul_eq_fourCornerMass
    {R p a b : ℕ} (hp : p.Prime)
    (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) :
    lowOwnerFirstOwnerCompensatedSite R p a *
        lowOwnerFirstOwnerCompensatedSite R p b =
      weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerZeroFrequencyMobiusWeight R) p a b := by
  rw [lowOwnerZeroFrequencyFreshPrimeFourCorner_eq_crossingProduct hp ha hb]
  unfold lowOwnerFirstOwnerCompensatedSite
  simp only [postRootZeroTargetPairExcess_eq_weight]
  ring

/-- **Exact complete-square Fubini.**  The compensated square of one actual
first-owner cell is the ordered sum of the physical AMP four-corner masses over
its admitted p-free parents. -/
theorem lowOwnerFirstOwnerCompensatedInterior_sq_eq_sum_fourCornerMass
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerCompensatedInteriorAmplitude R p sig ^ 2 =
      ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        ∑ b ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
          weightedMoebiusFreshPrimeFourCornerMass
            (lowOwnerZeroFrequencyMobiusWeight R) p a b := by
  rw [lowOwnerFirstOwnerCompensatedInteriorAmplitude_eq_sum_sites]
  calc
    (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerFirstOwnerCompensatedSite R p a) ^ 2 =
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerFirstOwnerCompensatedSite R p a) *
      (∑ b ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerFirstOwnerCompensatedSite R p b) := by ring
    _ = ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        ∑ b ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
          lowOwnerFirstOwnerCompensatedSite R p a *
            lowOwnerFirstOwnerCompensatedSite R p b := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
    _ = ∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        ∑ b ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
          weightedMoebiusFreshPrimeFourCornerMass
            (lowOwnerZeroFrequencyMobiusWeight R) p a b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact lowOwnerFirstOwnerCompensatedSite_mul_eq_fourCornerMass hp
        (lowOwnerFirstOwnerAdmittedBase_not_dvd ha)
        (lowOwnerFirstOwnerAdmittedBase_not_dvd hb)

/-- Pointwise expansion of the complete compensated atom into the exact
`daughter-daughter - daughter-root - root-daughter + root-root` quadratic form.
This is the local algebraic shape of the user's joint `S/E` interaction. -/
theorem lowOwnerFirstOwnerCompensatedSite_mul_eq_crossingQuadratic
    (R p a b : ℕ) :
    lowOwnerFirstOwnerCompensatedSite R p a *
        lowOwnerFirstOwnerCompensatedSite R p b =
      realMoebiusStep a * realMoebiusStep b *
        (lowOwnerDaughterCrossingWeight R p a *
            lowOwnerDaughterCrossingWeight R p b -
          lowOwnerDaughterCrossingWeight R p a *
            lowOwnerRootCrossingIndicator R p b -
          lowOwnerRootCrossingIndicator R p a *
            lowOwnerDaughterCrossingWeight R p b +
          lowOwnerRootCrossingIndicator R p a *
            lowOwnerRootCrossingIndicator R p b) := by
  unfold lowOwnerFirstOwnerCompensatedSite
  ring

end RHLean.Proof
