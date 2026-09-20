import Mathlib
import RHLean.Analysis.SquareRootTransportRealization

/-!
# Exact smooth/high joint packet on the top odd dyadic annulus

The complete square-prefix Mertens value is already compressed by Möbius
doubling to the single odd dyadic boundary

    X_R / 2 < m <= X_R,  m odd,

with X_R = R^2 - 1.  The correct local Item-87 carrier is therefore this one
top annulus, partitioned before any norm according to whether the canonical
largest prime lies below or above R.

This file proves only exact finite algebra:

* the top annulus is the disjoint smooth/high filter partition;
* the resulting joint packet is exactly the square-prefix Mertens value;
* the original smooth-minus-transport amplitude is exactly the same packet;
* after the existing dyadic transport compression, the same packet is
  positive-smooth + born-smooth + the canonical high source boundary.

No quantitative estimate, triangle inequality, or contraction is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Smooth part of the top odd dyadic annulus. -/
def squareRootDyadicAnnulusSmoothSet (R : ℕ) : Finset ℕ :=
  (dyadicCofactorBoundary (squareRootEndpoint R)).filter fun m =>
    canonicalLargestPrimeFactor m ≤ R

/-- High-largest-prime part of the same top odd dyadic annulus. -/
def squareRootDyadicAnnulusHighSet (R : ℕ) : Finset ℕ :=
  (dyadicCofactorBoundary (squareRootEndpoint R)).filter fun m =>
    R < canonicalLargestPrimeFactor m

/-- Native Möbius mass of the smooth part of the top dyadic annulus. -/
def squareRootDyadicAnnulusSmoothMass (R : ℕ) : ℂ :=
  ∑ m ∈ squareRootDyadicAnnulusSmoothSet R, canonicalMoebiusWeight m

/-- Native Möbius mass of the high part of the top dyadic annulus. -/
def squareRootDyadicAnnulusHighMass (R : ℕ) : ℂ :=
  ∑ m ∈ squareRootDyadicAnnulusHighSet R, canonicalMoebiusWeight m

/-- The exact signed joint packet.  The two orientations remain assembled. -/
def squareRootDyadicJointPacket (R : ℕ) : ℂ :=
  squareRootDyadicAnnulusSmoothMass R + squareRootDyadicAnnulusHighMass R

/-- The complement of the smooth filter is exactly the high filter. -/
theorem squareRootDyadicAnnulus_filter_not_smooth_eq_high
    (R : ℕ) :
    (dyadicCofactorBoundary (squareRootEndpoint R)).filter
        (fun m => ¬ canonicalLargestPrimeFactor m ≤ R) =
      squareRootDyadicAnnulusHighSet R := by
  ext m
  simp [squareRootDyadicAnnulusHighSet]

/-- Exact pre-norm partition of the complete odd dyadic annulus. -/
theorem squareRootDyadicAnnulusMass_eq_smooth_add_high
    (R : ℕ) :
    dyadicCofactorBoundaryMass (squareRootEndpoint R) =
      squareRootDyadicAnnulusSmoothMass R +
        squareRootDyadicAnnulusHighMass R := by
  classical
  unfold dyadicCofactorBoundaryMass squareRootDyadicAnnulusSmoothMass
    squareRootDyadicAnnulusSmoothSet squareRootDyadicAnnulusHighMass
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := dyadicCofactorBoundary (squareRootEndpoint R))
    (p := fun m => canonicalLargestPrimeFactor m ≤ R)
    (f := canonicalMoebiusWeight)]
  rw [squareRootDyadicAnnulus_filter_not_smooth_eq_high R]

/-- The joint packet is the complete top odd dyadic annulus. -/
theorem squareRootDyadicJointPacket_eq_annulusMass
    (R : ℕ) :
    squareRootDyadicJointPacket R =
      dyadicCofactorBoundaryMass (squareRootEndpoint R) := by
  rw [squareRootDyadicAnnulusMass_eq_smooth_add_high R]
  rfl

/-- At a genuine square root, the manuscript endpoint is the physical endpoint. -/
private theorem squarePrefixEndpoint_pred_eq_squareRootEndpoint_joint
    (R : ℕ) (hR : 1 ≤ R) :
    RHLean.Analysis.squarePrefixEndpoint (R - 1) =
      squareRootEndpoint R := by
  unfold RHLean.Analysis.squarePrefixEndpoint squareRootEndpoint
  rw [Nat.sub_add_cancel hR]

/-- **Global Fubini splice.**  The shell-local joint packet is exactly the
square-prefix Mertens value.  No sum over multiple dyadic scales is needed:
Möbius doubling has already compressed the whole prefix to this single top
annulus. -/
theorem squareRootDyadicJointPacket_eq_squarePrefixMertens
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootDyadicJointPacket R =
      RHLean.Analysis.squarePrefixMertens (R - 1) := by
  rw [squareRootDyadicJointPacket_eq_annulusMass]
  rw [← squarePrefixDyadicAnnulusMass_eq_squarePrefixMertens (R - 1)]
  unfold squarePrefixDyadicAnnulusMass
  rw [squarePrefixEndpoint_pred_eq_squareRootEndpoint_joint R hR]

/-- The original physical smooth-minus-transport amplitude lands on exactly the
same shell-local packet. -/
theorem squareRoot_positive_add_born_sub_transport_eq_dyadicJointPacket
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootPositiveSmoothMass R + squareRootBornSmoothMass R -
        squareRootTransportCofactorFirst R =
      squareRootDyadicJointPacket R := by
  have hsplit := squarePrefixMertens_eq_positiveSmooth_add_matched R hR
  rw [squareRootMatchedBornSmoothTransport_eq_bornSmooth_sub_transport R] at hsplit
  calc
    squareRootPositiveSmoothMass R + squareRootBornSmoothMass R -
        squareRootTransportCofactorFirst R =
      squareRootPositiveSmoothMass R +
        (squareRootBornSmoothMass R - squareRootTransportCofactorFirst R) := by ring
    _ = RHLean.Analysis.squarePrefixMertens (R - 1) := hsplit.symm
    _ = squareRootDyadicJointPacket R :=
      (squareRootDyadicJointPacket_eq_squarePrefixMertens R hR).symm

/-- After exact dyadic compression of the high transport, the same joint packet
is smooth mass plus the canonical source-signed high boundary. -/
theorem squareRoot_positive_add_born_add_dyadicHigh_eq_dyadicJointPacket
    (R : ℕ) (hR : 1 ≤ R) :
    squareRootPositiveSmoothMass R + squareRootBornSmoothMass R +
        dyadicCanonicalHighSourceMass R =
      squareRootDyadicJointPacket R := by
  have h :=
    squareRoot_positive_add_born_sub_transport_eq_dyadicJointPacket R hR
  rw [squareRootTransportCofactorFirst_eq_neg_dyadicCanonicalHighSourceMass R] at h
  simpa only [sub_neg_eq_add] using h

/-- Every individual canonical high source produced by dyadic transport
compression lies on the same top odd annulus.  This is the pointwise support
certificate behind the global splice. -/
theorem isDyadicCanonicalHighSource_product_mem_topAnnulus
    {R c q : ℕ} (hR : 2 ≤ R)
    (h : IsDyadicCanonicalHighSource R c q) :
    c * q ∈ dyadicCofactorBoundary (squareRootEndpoint R) := by
  rcases arithmetic_of_isDyadicCanonicalHighSource (by omega : 0 < R) h with
    ⟨hqPrime, hRq, _hqX, hc1, _hcR, _hcq, hcOdd, hupper, hlower⟩
  have hqOdd : Odd q := hqPrime.odd_of_ne_two (by omega)
  have hcPos : 0 < c := by omega
  have hprodPos : 0 < c * q := Nat.mul_pos hcPos hqPrime.pos
  exact mem_dyadicCofactorBoundary.mpr
    ⟨Nat.succ_le_iff.mpr hprodPos, hupper, hcOdd.mul hqOdd, hlower⟩

end RHLean.Proof
