import Mathlib
import «research.STABLE_FAR_RETURNED_RECIPROCAL_PHYSICAL_BRIDGE»
import RHLean.Proof.PostRootPartnerLogAlignment

/-!
# Global returned-coordinate Fubini for the centered q² tower

The stable-far renewal has already been centered on the literal descended child
carrier.  The fixed returned-coordinate theorem then identifies one `(r,p)`
fibre with its physical reciprocal packet and its `(1-1/owner)` Euler-memory
packet.

This file performs only the missing finite Fubini between those layers.  It
regroups the complete centered q² tower by the actual returned coordinates
`(r,p)` occurring in the descended carrier.  No norm, estimate, PNT input, or
RH-scale hypothesis is introduced.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Returned `(r,p)` coordinates which actually occur in the descended q²
carrier.  Using the image of the physical carrier keeps the global Fubini exact
without enlarging the far-prime range. -/
def stableFarReturnedCoordinatePairs (R : ℕ) : Finset (ℕ × ℕ) :=
  (lowWheelFarPrimeQ2DescendedTriples R).image fun y => (y.1, y.2.2)

/-- A descended triple is exactly a returned smooth cofactor together with the
prime/root conditions on its returned coordinates. -/
theorem mem_lowWheelFarPrimeQ2DescendedTriples_iff_returnedCofactor
    {R r e p : ℕ} :
    (r, (e, p)) ∈ lowWheelFarPrimeQ2DescendedTriples R ↔
      r.Prime ∧ r < R ∧ p.Prime ∧ R + 8 ≤ p ∧
        e ∈ stableFarReturnedDescendedCofactors R r p := by
  constructor
  · intro hdesc
    have hbase : (r, (e, p)) ∈ lowWheelFarPrimeLowCofactorTriples R :=
      (Finset.mem_filter.mp hdesc).1
    have hq2 := (Finset.mem_filter.mp hdesc).2
    rcases lowWheelFarPrimeLowCofactorTriple_data hbase with
      ⟨hr, hrR, he1, hp, hpR, heSq, her, _hcut⟩
    have hdenPos : 0 < r * r * p :=
      Nat.mul_pos (Nat.mul_pos hr.pos hr.pos) hp.pos
    have heCut : e ≤ squareRootEndpoint R / (r * r * p) := by
      apply (Nat.le_div_iff_mul_le hdenPos).2
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq2
    refine ⟨hr, hrR, hp, hpR, ?_⟩
    exact mem_squareRootLowPrimeGoSmoothCofactors.mpr
      ⟨he1, heCut, heSq, her⟩
  · rintro ⟨hr, hrR, hp, hpR, he⟩
    exact stableFarReturnedDescendedCofactor_mem_physical
      hr hrR hp hpR he

/-- Arithmetic data attached to every actually occupied returned coordinate. -/
theorem stableFarReturnedCoordinatePair_data
    {R : ℕ} {rp : ℕ × ℕ}
    (hrp : rp ∈ stableFarReturnedCoordinatePairs R) :
    rp.1.Prime ∧ rp.1 < R ∧ rp.2.Prime ∧ R + 8 ≤ rp.2 := by
  rcases Finset.mem_image.mp hrp with ⟨y, hy, hcoord⟩
  rcases y with ⟨r, ⟨e, p⟩⟩
  have hdata :=
    (mem_lowWheelFarPrimeQ2DescendedTriples_iff_returnedCofactor).1 hy
  have hrEq : r = rp.1 := congrArg Prod.fst hcoord
  have hpEq : p = rp.2 := congrArg Prod.snd hcoord
  simpa [hrEq, hpEq] using ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2.1⟩

/-- Fibre of the descended carrier over one returned coordinate pair. -/
def stableFarReturnedCoordinateFiber
    (R : ℕ) (rp : ℕ × ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (lowWheelFarPrimeQ2DescendedTriples R).filter fun y =>
    (y.1, y.2.2) = rp

/-- On an occupied coordinate pair, the physical fibre is precisely the image
of the returned smooth-cofactor carrier. -/
theorem stableFarReturnedCoordinateFiber_eq_cofactorImage
    {R : ℕ} {rp : ℕ × ℕ}
    (hrp : rp ∈ stableFarReturnedCoordinatePairs R) :
    stableFarReturnedCoordinateFiber R rp =
      (stableFarReturnedDescendedCofactors R rp.1 rp.2).image
        (fun e => (rp.1, (e, rp.2))) := by
  have hdata := stableFarReturnedCoordinatePair_data hrp
  ext y
  rcases y with ⟨r, ⟨e, p⟩⟩
  constructor
  · intro hy
    rcases Finset.mem_filter.mp hy with ⟨hdesc, hcoord⟩
    have hrEq : r = rp.1 := congrArg Prod.fst hcoord
    have hpEq : p = rp.2 := congrArg Prod.snd hcoord
    subst r
    subst p
    have he :=
      (mem_lowWheelFarPrimeQ2DescendedTriples_iff_returnedCofactor).1 hdesc
    exact Finset.mem_image.mpr ⟨e, he.2.2.2.2, rfl⟩
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨e', he', heq⟩
    have hdesc : (rp.1, (e', rp.2)) ∈ lowWheelFarPrimeQ2DescendedTriples R :=
      (mem_lowWheelFarPrimeQ2DescendedTriples_iff_returnedCofactor).2
        ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2, he'⟩
    subst y
    exact Finset.mem_filter.mpr ⟨hdesc, rfl⟩

/-- Complex form of the literal physical centered mass at fixed returned
coordinates. -/
def stableFarReturnedPhysicalCenteredMass
    (R r p : ℕ) : ℂ :=
  ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
    (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R (r, (e, p)) : ℂ)) *
      canonicalMoebiusWeight e

/-- The complex fibre sum is exactly the unit-centered physical packet from the
fixed-coordinate bridge. -/
theorem stableFarReturnedPhysicalCenteredMass_eq_unitCentered
    (R r p : ℕ) :
    stableFarReturnedPhysicalCenteredMass R r p =
      stableFarReturnedPhysicalUnitCenteredMass R r p := by
  unfold stableFarReturnedPhysicalCenteredMass
    stableFarReturnedPhysicalUnitCenteredMass
    stableFarReturnedPhysicalCenteredMassInt
    canonicalMoebiusWeight
  push_cast
  rfl

/-- One descended coordinate fibre is exactly its fixed returned physical
centered packet. -/
theorem stableFarReturnedCoordinateFiber_centeredMass
    {R : ℕ} {rp : ℕ × ℕ}
    (hrp : rp ∈ stableFarReturnedCoordinatePairs R) :
    (∑ y ∈ stableFarReturnedCoordinateFiber R rp,
      (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
        canonicalMoebiusWeight y.2.1) =
      stableFarReturnedPhysicalUnitCenteredMass R rp.1 rp.2 := by
  rw [stableFarReturnedCoordinateFiber_eq_cofactorImage hrp]
  rw [Finset.sum_image]
  · rw [← stableFarReturnedPhysicalCenteredMass_eq_unitCentered]
    unfold stableFarReturnedPhysicalCenteredMass
    apply Finset.sum_congr rfl
    intro e _he
    rfl
  · intro a _ha b _hb hab
    exact congrArg (fun y : ℕ × (ℕ × ℕ) => y.2.1) hab

/-- **Global returned-coordinate Fubini.**  The already-centered q² tower is
exactly the sum of the literal centered physical packets over the actual
returned `(r,p)` coordinates. -/
theorem farFourQ2CenteredTower_eq_sum_returnedPhysicalCenteredMass
    (R : ℕ) :
    farFourQ2CenteredTower R =
      ∑ rp ∈ stableFarReturnedCoordinatePairs R,
        stableFarReturnedPhysicalUnitCenteredMass R rp.1 rp.2 := by
  let S := lowWheelFarPrimeQ2DescendedTriples R
  let T := stableFarReturnedCoordinatePairs R
  let g : ℕ × (ℕ × ℕ) → ℕ × ℕ := fun y => (y.1, y.2.2)
  let f : ℕ × (ℕ × ℕ) → ℂ := fun y =>
    (1 - (lowWheelFarPrimeQ2CrossingNextMultiplicity R y : ℂ)) *
      canonicalMoebiusWeight y.2.1
  have hmaps : ∀ y ∈ S, g y ∈ T := by
    intro y hy
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := g) hmaps f
  have hraw :
      (∑ y ∈ S, f y) =
        ∑ rp ∈ T, ∑ y ∈ S with g y = rp, f y := hfiber.symm
  unfold farFourQ2CenteredTower
  change (∑ y ∈ S, f y) =
    ∑ rp ∈ T,
      stableFarReturnedPhysicalUnitCenteredMass R rp.1 rp.2
  rw [hraw]
  apply Finset.sum_congr rfl
  intro rp hrp
  have hfiberEq :
      (∑ y ∈ S with g y = rp, f y) =
        ∑ y ∈ stableFarReturnedCoordinateFiber R rp, f y := by
    rfl
  rw [hfiberEq]
  simpa [f] using stableFarReturnedCoordinateFiber_centeredMass hrp

/-- **Global reciprocal/memory split of the centered q² tower.**  After the
finite Fubini, every returned packet splits exactly into the physical reciprocal
packet plus its Euler-memory normalization correction. -/
theorem farFourQ2CenteredTower_eq_sum_reciprocal_add_memory
    (R : ℕ) :
    farFourQ2CenteredTower R =
      (∑ rp ∈ stableFarReturnedCoordinatePairs R,
        stableFarReturnedPhysicalReciprocalCenteredMass R rp.1 rp.2) +
      ∑ rp ∈ stableFarReturnedCoordinatePairs R,
        stableFarReturnedPhysicalEulerMemoryMass R rp.1 rp.2 := by
  rw [farFourQ2CenteredTower_eq_sum_returnedPhysicalCenteredMass]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rp _hrp
  unfold stableFarReturnedPhysicalEulerMemoryMass
  ring

end RHLean.Proof
