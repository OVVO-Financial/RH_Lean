import Mathlib
import «research.DYADIC_LONG_RANGE_TETHER_AUDIT»
import RHLean.Proof.PrefixCarrierOthelloWalls
import RHLean.Proof.VanishingTransitionRelevanceBase
import RHLean.Analysis.SquareRootPrimeCountGap

/-!
# Dyadic Buchstab/Othello splice: the joint packet is already an escape wall

The prime-two Othello involution acts on the complete prefix (0,B].
Every interior two-cycle cancels with opposite Mobius sign, every fixed
square-hit carries zero Mobius mass, and the only surviving cutoff wall is

    B / 2 < n <= B, n odd.

That wall is exactly dyadicCofactorBoundary B.

Thus the top odd dyadic annulus introduced by the smooth/high joint packet is
not a fresh bulk region whose whole interior still has to be cancelled: it is
already the prime-two Othello escape wall left after the complete prefix has
played out.

The wall can then be played again with any finite list of distinguished primes.
The signed mass remains unchanged while every new interior two-cycle cancels.
The surviving iteratedPrimeEscapePart is the exact finite glider boundary.

This file also records the sign-correct Buchstab splice. The ordered replication
response has the paper transport orientation, hence it enters with a minus sign
against the native high-source orientation.

No norm, cardinality estimate, asymptotic input, or RH hypothesis is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-! ## Prime two turns the whole prefix into the odd dyadic wall -/

/-- The lower anchor wall is empty for the full prefix (0,B]. -/
theorem primeTwoAnchorWall_zero (B : ℕ) :
    primeCarrierAnchorWall 2 0 B = ∅ := by
  ext n
  simp [primeCarrierAnchorWall]

/-- The prime-two cutoff wall of (0,B] is literally the odd dyadic annulus. -/
theorem primeTwoCutoffWall_eq_dyadicCofactorBoundary (B : ℕ) :
    primeCarrierCutoffWall 2 0 B = dyadicCofactorBoundary B := by
  ext n
  constructor
  · intro hn
    rcases mem_primeCarrierCutoffWall.mp hn with
      ⟨hnIoc, h2n, hcut⟩
    have hodd : Odd n := by
      rcases Nat.even_or_odd n with heven | hodd
      · exfalso
        apply h2n
        rcases heven with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        omega
      · exact hodd
    exact mem_dyadicCofactorBoundary.mpr
      ⟨by omega, hnIoc.2, hodd, by simpa [Nat.mul_comm] using hcut⟩
  · intro hn
    rcases mem_dyadicCofactorBoundary.mp hn with
      ⟨hn1, hnB, hodd, hcut⟩
    have h2n : ¬ 2 ∣ n := by
      intro hd
      rcases hd with ⟨k, hk⟩
      rcases hodd with ⟨j, hj⟩
      omega
    exact mem_primeCarrierCutoffWall.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega, hnB⟩, h2n,
        by simpa [Nat.mul_comm] using hcut⟩

/-- Prime-two glider set: the entire escape part of (0,B] is exactly the odd
dyadic annulus. -/
theorem primeEscapePart_two_Ioc_zero_eq_dyadicCofactorBoundary (B : ℕ) :
    primeEscapePart 2 (Finset.Ioc 0 B) = dyadicCofactorBoundary B := by
  rw [primeEscapePart_Ioc_eq_walls Nat.prime_two 0 B,
    primeTwoAnchorWall_zero, Finset.empty_union,
    primeTwoCutoffWall_eq_dyadicCofactorBoundary]

/-- Integer form of the Game-of-Life statement: the whole prefix interior has
cancelled and only the prime-two escape wall carries the signed mass. -/
theorem sum_moebius_Ioc_zero_eq_dyadicEscapeWall (B : ℕ) :
    (∑ n ∈ Finset.Ioc 0 B, μ n) =
      ∑ n ∈ dyadicCofactorBoundary B, μ n := by
  rw [sum_moebius_eq_sum_primeEscapePart Nat.prime_two (Finset.Ioc 0 B),
    primeEscapePart_two_Ioc_zero_eq_dyadicCofactorBoundary]

/-! ## Replaying the game on the surviving wall -/

/-- Complex-scalar version of the iterated global Othello theorem. -/
theorem sum_canonicalMoebiusWeight_eq_sum_iteratedPrimeEscapePart
    (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime) (S : Finset ℕ) :
    (∑ n ∈ S, canonicalMoebiusWeight n) =
      ∑ n ∈ iteratedPrimeEscapePart ps S, canonicalMoebiusWeight n := by
  have h := sum_moebius_eq_sum_iteratedPrimeEscapePart ps hps S
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hc
  simpa [canonicalMoebiusWeight] using hc

/-- The iterated survivor/glider boundary obtained by replaying Othello on the
prime-two dyadic wall. -/
def dyadicJointGliderBoundary (ps : List ℕ) (B : ℕ) : Finset ℕ :=
  iteratedPrimeEscapePart ps (dyadicCofactorBoundary B)

/-- Exact glider-boundary theorem. The signed smooth/high joint packet at
boundary scale B is carried entirely by the iterated Othello boundary after any
finite list of prime peels. Every complementary interior two-cycle has already
cancelled before this equality is read. -/
theorem dyadicJointPacketAt_eq_iteratedGliderBoundaryMass
    (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime) (R B : ℕ) :
    dyadicJointPacketAt R B =
      ∑ n ∈ dyadicJointGliderBoundary ps B, canonicalMoebiusWeight n := by
  rw [dyadicJointPacketAt_eq_boundaryMass]
  unfold dyadicCofactorBoundaryMass dyadicJointGliderBoundary
  exact sum_canonicalMoebiusWeight_eq_sum_iteratedPrimeEscapePart
    ps hps (dyadicCofactorBoundary B)

/-- Top-endpoint specialization of the exact glider-boundary theorem. -/
theorem squareRootDyadicJointPacket_eq_iteratedGliderBoundaryMass
    (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime) (R : ℕ) :
    squareRootDyadicJointPacket R =
      ∑ n ∈ dyadicJointGliderBoundary ps (squareRootEndpoint R),
        canonicalMoebiusWeight n := by
  rw [squareRootDyadicJointPacket_eq_at_top]
  exact dyadicJointPacketAt_eq_iteratedGliderBoundaryMass
    ps hps R (squareRootEndpoint R)

/-! ## Sign-correct smooth/high Buchstab splice -/

/-- The ordered root-weighted replication response has paper transport sign,
which is the negative of the canonical high-source sign on the dyadic wall. -/
theorem orderedPrimeReplicationResponse_eq_neg_dyadicCanonicalHighSourceMass
    (R : ℕ) (hR : 3 ≤ R) :
    orderedPrimeReplicationResponse R =
      -dyadicCanonicalHighSourceMass R := by
  rw [orderedPrimeReplicationResponse_eq_transport R hR,
    squareRootTransportCofactorFirst_eq_neg_dyadicCanonicalHighSourceMass]

/-- Exact pre-norm Buchstab splice. Smooth mass and ordered replication response
must enter with opposite paper orientations. Their assembled value is the same
top dyadic joint packet from the previous layer. -/
theorem squareRoot_positive_add_born_sub_orderedResponse_eq_dyadicJointPacket
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootPositiveSmoothMass R + squareRootBornSmoothMass R -
        orderedPrimeReplicationResponse R =
      squareRootDyadicJointPacket R := by
  rw [orderedPrimeReplicationResponse_eq_transport R hR]
  exact squareRoot_positive_add_born_sub_transport_eq_dyadicJointPacket
    R (by omega)

/-- The sign-correct physical smooth/response amplitude can therefore be played
by any finite Othello prime list and read entirely on the resulting glider
boundary. -/
theorem squareRoot_positive_add_born_sub_orderedResponse_eq_gliderBoundaryMass
    (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime)
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootPositiveSmoothMass R + squareRootBornSmoothMass R -
        orderedPrimeReplicationResponse R =
      ∑ n ∈ dyadicJointGliderBoundary ps (squareRootEndpoint R),
        canonicalMoebiusWeight n := by
  rw [squareRoot_positive_add_born_sub_orderedResponse_eq_dyadicJointPacket
    R hR]
  exact squareRootDyadicJointPacket_eq_iteratedGliderBoundaryMass ps hps R

/-! ## The active middle is not an automatic zero -/

/-- Existing exact middle/top chronology restated as a guardrail for the glider
picture. The intermediate-prime residual is the negative full Mertens value, so
a theorem that it vanishes identically would be strictly too strong. -/
theorem squareRootActiveMiddleResidual_eq_neg_fullMertens
    (R : ℕ) (hR : 3 ≤ R) :
    squareRootMiddleCancellationResidual R =
      -squarePrefixMertens (R - 1) :=
  squareRootMiddleCancellationResidual_eq_neg_mertens R hR

end RHLean.Proof
