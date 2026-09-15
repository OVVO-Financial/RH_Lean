import Mathlib
import RHLean.Proof.StableFarWallCrossingOwnerWindow
import RHLean.Proof.StableFarWallQ2ChildFarSlice

/-!
# Reciprocal stable-far owner Fubini

The unweighted stable-far renewal has coefficient `1 - multiplicity` on each
returned q^2 child.  For the amplitude-first route the natural coordinate is
reciprocal in the owner prime.  This file performs exactly that weighted finite
Fubini before any norm.

For one descended child `y = (r,(e,p))`, the baseline q^2 child carries weight
`1/r`.  Every strict-crossing old owner `q` returning to the same child carries
the opposite Mobius sign and reciprocal weight `1/q`.  Hence the complete
nonunit returned fibre has coefficient

  1/r - sum_{q in O_y} 1/q,

where `O_y` is the already-compiled exact crossing-owner window.  No estimate,
PNT input, or endpoint Mertens factorization is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Reciprocal weight of all old crossing owners returning to one descended
child. -/
def lowWheelFarPrimeQ2CrossingNextReciprocalWeight
    (R : ℕ) (y : ℕ × (ℕ × ℕ)) : ℂ :=
  ∑ t ∈ lowWheelFarPrimeQ2CrossingNextFiber R y,
    (1 : ℂ) / (t.1 : ℂ)

/-- The reciprocal crossing weight is literally the reciprocal sum over the
solved old-owner set. -/
theorem lowWheelFarPrimeQ2CrossingNextReciprocalWeight_eq_ownerSet
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingNextReciprocalWeight R y =
      ∑ q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R y,
        (1 : ℂ) / (q : ℂ) := by
  unfold lowWheelFarPrimeQ2CrossingNextReciprocalWeight
  have himage := lowWheelFarPrimeQ2CrossingNextFiber_fst_image_eq_ownerSet hy
  have hinj := lowWheelFarPrimeQ2CrossingNextFiber_fst_injOn R y
  calc
    (∑ t ∈ lowWheelFarPrimeQ2CrossingNextFiber R y,
        (1 : ℂ) / (t.1 : ℂ)) =
      ∑ q ∈ (lowWheelFarPrimeQ2CrossingNextFiber R y).image Prod.fst,
        (1 : ℂ) / (q : ℂ) := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          exact hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
    _ = ∑ q ∈ lowWheelFarPrimeQ2CrossingOuterOwnerSet R y,
        (1 : ℂ) / (q : ℂ) := by rw [himage]

/-- The same coefficient on the explicit solved prime interval. -/
theorem lowWheelFarPrimeQ2CrossingNextReciprocalWeight_eq_primeInterval
    {R : ℕ} {y : ℕ × (ℕ × ℕ)}
    (hy : y ∈ lowWheelFarPrimeQ2DescendedTriples R) :
    lowWheelFarPrimeQ2CrossingNextReciprocalWeight R y =
      ∑ q ∈ (Finset.Ioc (lowWheelFarPrimeQ2CrossingOwnerLower R y)
          (lowWheelFarPrimeQ2CrossingOwnerUpper R y)).filter Nat.Prime,
        (1 : ℂ) / (q : ℂ) := by
  rw [lowWheelFarPrimeQ2CrossingNextReciprocalWeight_eq_ownerSet hy,
    lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_primeInterval hy]

/-- Reciprocal baseline carried by the complete descended q^2 child-far packet. -/
def lowWheelFarPrimeQ2ReciprocalDescendedMass (R : ℕ) : ℂ :=
  ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
    ((1 : ℂ) / (y.1 : ℂ)) * canonicalMoebiusWeight y.2.1

/-- Reciprocal weighting of every nonunit strict-crossing renewal occurrence by
its original old owner. -/
def lowWheelFarPrimeQ2ReciprocalNonUnitRenewalMass (R : ℕ) : ℂ :=
  ∑ t ∈ lowWheelFarPrimeQ2NonUnitCrossingTriples R,
    ((1 : ℂ) / (t.1 : ℂ)) *
      lowWheelFullTaggedPhysicalWeight
        ((∅ : Finset ℕ), (t.2.1, t.2.2))

/-- Pointwise sign reversal converts the reciprocal renewal to the negative
reciprocal next-child incidence. -/
theorem lowWheelFarPrimeQ2ReciprocalNonUnitRenewalMass_eq_neg_incidence
    (R : ℕ) :
    lowWheelFarPrimeQ2ReciprocalNonUnitRenewalMass R =
      -∑ t ∈ lowWheelFarPrimeQ2NonUnitCrossingTriples R,
        ((1 : ℂ) / (t.1 : ℂ)) *
          canonicalMoebiusWeight (canonicalCofactor t.2.1) := by
  unfold lowWheelFarPrimeQ2ReciprocalNonUnitRenewalMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rcases t with ⟨q, ⟨d, p⟩⟩
  rcases Finset.mem_filter.mp ht with ⟨hcross, hd⟩
  rw [lowWheelFarPrimeQ2Crossing_returnedWeight_eq_neg_nextChildWeight
    hcross hd]
  ring

/-- **Weighted finite Fubini.**  Forgetting the old crossing owner turns its
reciprocal incidence into the exact reciprocal-owner sum on each returned
child. -/
theorem lowWheelFarPrimeQ2ReciprocalNextChildIncidence_eq_fiberWeights
    (R : ℕ) :
    (∑ t ∈ lowWheelFarPrimeQ2NonUnitCrossingTriples R,
        ((1 : ℂ) / (t.1 : ℂ)) *
          canonicalMoebiusWeight (canonicalCofactor t.2.1)) =
      ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
        lowWheelFarPrimeQ2CrossingNextReciprocalWeight R y *
          canonicalMoebiusWeight y.2.1 := by
  have hmaps : ∀ t ∈ lowWheelFarPrimeQ2NonUnitCrossingTriples R,
      lowWheelFarPrimeQ2CrossingNextChild t ∈
        lowWheelFarPrimeQ2DescendedTriples R := by
    intro t ht
    exact lowWheelFarPrimeQ2CrossingNextChild_mem_descended ht
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := lowWheelFarPrimeQ2NonUnitCrossingTriples R)
    (t := lowWheelFarPrimeQ2DescendedTriples R)
    (g := lowWheelFarPrimeQ2CrossingNextChild) hmaps
    (fun t => ((1 : ℂ) / (t.1 : ℂ)) *
      canonicalMoebiusWeight (canonicalCofactor t.2.1))
  rw [hfiber.symm]
  apply Finset.sum_congr rfl
  intro y hy
  calc
    (∑ t ∈ lowWheelFarPrimeQ2NonUnitCrossingTriples R with
        lowWheelFarPrimeQ2CrossingNextChild t = y,
        (1 : ℂ) / (t.1 : ℂ) *
          canonicalMoebiusWeight (canonicalCofactor t.2.1)) =
      ∑ t ∈ lowWheelFarPrimeQ2CrossingNextFiber R y,
        ((1 : ℂ) / (t.1 : ℂ)) * canonicalMoebiusWeight y.2.1 := by
          apply Finset.sum_congr rfl
          intro t ht
          have heq := (Finset.mem_filter.mp ht).2
          have hc := congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.1) heq
          simpa [lowWheelFarPrimeQ2CrossingNextFiber,
            lowWheelFarPrimeQ2CrossingNextChild] using
            congrArg (fun z : ℂ => ((1 : ℂ) / (t.1 : ℂ)) * z)
              (congrArg canonicalMoebiusWeight hc)
    _ = lowWheelFarPrimeQ2CrossingNextReciprocalWeight R y *
          canonicalMoebiusWeight y.2.1 := by
      unfold lowWheelFarPrimeQ2CrossingNextReciprocalWeight
      rw [Finset.sum_mul]

/-- The reciprocal renewal is therefore the negative reciprocal-owner incidence
on the existing descended child carrier. -/
theorem lowWheelFarPrimeQ2ReciprocalNonUnitRenewalMass_eq_neg_fiberWeights
    (R : ℕ) :
    lowWheelFarPrimeQ2ReciprocalNonUnitRenewalMass R =
      -∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
        lowWheelFarPrimeQ2CrossingNextReciprocalWeight R y *
          canonicalMoebiusWeight y.2.1 := by
  rw [lowWheelFarPrimeQ2ReciprocalNonUnitRenewalMass_eq_neg_incidence,
    lowWheelFarPrimeQ2ReciprocalNextChildIncidence_eq_fiberWeights]

/-- **Reciprocal centered stable-far normal form.**  The weighted descended
baseline and all weighted nonunit returns combine to the coefficient
`1/r - sum_{q in O_y} 1/q` on every actual q^2 child state. -/
theorem lowWheelFarPrimeQ2ReciprocalDescended_add_nonUnitRenewal_eq_centered
    (R : ℕ) :
    lowWheelFarPrimeQ2ReciprocalDescendedMass R +
        lowWheelFarPrimeQ2ReciprocalNonUnitRenewalMass R =
      ∑ y ∈ lowWheelFarPrimeQ2DescendedTriples R,
        ((1 : ℂ) / (y.1 : ℂ) -
          lowWheelFarPrimeQ2CrossingNextReciprocalWeight R y) *
            canonicalMoebiusWeight y.2.1 := by
  rw [lowWheelFarPrimeQ2ReciprocalNonUnitRenewalMass_eq_neg_fiberWeights]
  unfold lowWheelFarPrimeQ2ReciprocalDescendedMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  ring

end RHLean.Proof
