import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalInternalMate
import RHLean.Analysis.SquareRootMatchedTransport

/-!
# Exact far physical / far-prime transport identity

The preceding face/quotient Othello reduction proves that the literal far
physical carrier has the same signed mass as its stable states, and that those
stable states are exactly empty-face states `(∅,(c,q))` with squarefree low
cofactor `1 <= c < R`, far prime `R+8 <= q <= R^2-1`, and `c*q <= R^2-1`.

This file performs the remaining finite reindexing back to the already-existing
far prime transform.  Non-squarefree cofactors may be restored because their
Möbius weight is exactly zero.  No norm or estimate is taken.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Canonical low-cofactor / far-prime pair carrier. -/
def lowWheelFarPrimePairSet (R : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico 1 R).product
      (Finset.Icc (R + 8) (squareRootEndpoint R))).filter fun cq =>
    cq.2.Prime ∧ cq.1 * cq.2 ≤ squareRootEndpoint R

@[simp] theorem mem_lowWheelFarPrimePairSet
    {R c q : ℕ} :
    (c, q) ∈ lowWheelFarPrimePairSet R ↔
      c ∈ Finset.Ico 1 R ∧
        q ∈ Finset.Icc (R + 8) (squareRootEndpoint R) ∧
        q.Prime ∧ c * q ≤ squareRootEndpoint R := by
  simp [lowWheelFarPrimePairSet, and_assoc]

/-- Physical stable pairs are the squarefree part of the same pair carrier. -/
def lowWheelFarPrimeSquarefreePairSet (R : ℕ) : Finset (ℕ × ℕ) :=
  (lowWheelFarPrimePairSet R).filter fun cq => Squarefree cq.1

@[simp] theorem mem_lowWheelFarPrimeSquarefreePairSet
    {R c q : ℕ} :
    (c, q) ∈ lowWheelFarPrimeSquarefreePairSet R ↔
      (c, q) ∈ lowWheelFarPrimePairSet R ∧ Squarefree c := by
  simp [lowWheelFarPrimeSquarefreePairSet]

/-- Empty-face embedding of a low-cofactor / far-prime pair into the literal
physical carrier. -/
def lowWheelFarPrimePairTag (cq : ℕ × ℕ) :
    LowWheelFullTaggedPhysicalState :=
  ((∅ : Finset ℕ), cq)

/-- The empty-face tag loses no pair information. -/
theorem lowWheelFarPrimePairTag_injective :
    Function.Injective lowWheelFarPrimePairTag := by
  intro a b hab
  simpa [lowWheelFarPrimePairTag] using congrArg Prod.snd hab

/-- **Exact stable-carrier identification.**  The Othello-stable far physical
states are precisely the squarefree low-cofactor / far-prime pairs. -/
theorem lowWheelFarTaggedPhysicalStableCarrier_eq_pairImage
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelFarTaggedPhysicalStableCarrier R =
      (lowWheelFarPrimeSquarefreePairSet R).image lowWheelFarPrimePairTag := by
  ext z
  constructor
  · intro hz
    rcases lowWheelFarTaggedPhysicalStable_geometry hR hz with
      ⟨hface, hqPrime, hqFar, hqX, hc, hsq, hcq⟩
    have hpair : (z.2.1, z.2.2) ∈ lowWheelFarPrimePairSet R :=
      mem_lowWheelFarPrimePairSet.mpr
        ⟨hc, Finset.mem_Icc.mpr ⟨hqFar, hqX⟩, hqPrime, hcq⟩
    have hpairSq :
        (z.2.1, z.2.2) ∈ lowWheelFarPrimeSquarefreePairSet R :=
      mem_lowWheelFarPrimeSquarefreePairSet.mpr ⟨hpair, hsq⟩
    apply Finset.mem_image.mpr
    refine ⟨(z.2.1, z.2.2), hpairSq, ?_⟩
    exact Prod.ext hface.symm rfl
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨cq, hcq, rfl⟩
    rcases cq with ⟨c, q⟩
    rcases mem_lowWheelFarPrimeSquarefreePairSet.mp hcq with
      ⟨hpair, hsq⟩
    rcases mem_lowWheelFarPrimePairSet.mp hpair with
      ⟨hc, hqRange, hqPrime, hprod⟩
    rcases Finset.mem_Icc.mp hqRange with ⟨hqFar, hqX⟩
    exact lowWheelFarTaggedPhysicalStable_of_prime
      hR hc hsq hqPrime hqFar hqX hprod

/-- Signed mass of the squarefree far-prime pair carrier. -/
def lowWheelFarPrimeSquarefreePairMass (R : ℕ) : ℂ :=
  ∑ cq ∈ lowWheelFarPrimeSquarefreePairSet R,
    canonicalMoebiusWeight cq.1

/-- The stable physical weight is exactly the low-cofactor Möbius weight. -/
theorem sum_lowWheelFarTaggedPhysicalStableCarrier_eq_squarefreePairMass
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ z ∈ lowWheelFarTaggedPhysicalStableCarrier R,
        lowWheelFullTaggedPhysicalWeight z) =
      lowWheelFarPrimeSquarefreePairMass R := by
  rw [lowWheelFarTaggedPhysicalStableCarrier_eq_pairImage R hR]
  unfold lowWheelFarPrimeSquarefreePairMass
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro cq hcq
    simp [lowWheelFarPrimePairTag, lowWheelFullTaggedPhysicalWeight,
      booleanCubeSign]
  · intro a ha b hb hab
    exact lowWheelFarPrimePairTag_injective hab

/-- Signed mass of the same pair carrier without the redundant squarefree
filter. -/
def lowWheelFarPrimePairMass (R : ℕ) : ℂ :=
  ∑ cq ∈ lowWheelFarPrimePairSet R,
    canonicalMoebiusWeight cq.1

/-- Restoring non-squarefree cofactors changes no signed mass because their
Möbius weights vanish exactly. -/
theorem lowWheelFarPrimeSquarefreePairMass_eq_pairMass
    (R : ℕ) :
    lowWheelFarPrimeSquarefreePairMass R = lowWheelFarPrimePairMass R := by
  unfold lowWheelFarPrimeSquarefreePairMass lowWheelFarPrimeSquarefreePairSet
    lowWheelFarPrimePairMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro cq hcq
  by_cases hsq : Squarefree cq.1
  · simp [hsq]
  · have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    simp [hsq, canonicalMoebiusWeight, hmu]

/-- The pair mass is exactly the existing far-prime Mertens transform. -/
theorem lowWheelFarPrimePairMass_eq_farPrimeTransport
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelFarPrimePairMass R = squareRootFarPrimeTransport R := by
  unfold lowWheelFarPrimePairMass lowWheelFarPrimePairSet
  rw [Finset.sum_filter]
  calc
    (∑ cq ∈ (Finset.Ico 1 R).product
        (Finset.Icc (R + 8) (squareRootEndpoint R)),
        if cq.2.Prime ∧ cq.1 * cq.2 ≤ squareRootEndpoint R then
          canonicalMoebiusWeight cq.1 else 0) =
      ∑ c ∈ Finset.Ico 1 R,
        ∑ q ∈ Finset.Icc (R + 8) (squareRootEndpoint R),
          if q.Prime ∧ c * q ≤ squareRootEndpoint R then
            canonicalMoebiusWeight c else 0 := by
      simpa only using
        (Finset.sum_product
          (s := Finset.Ico 1 R)
          (t := Finset.Icc (R + 8) (squareRootEndpoint R))
          (f := fun cq : ℕ × ℕ =>
            if cq.2.Prime ∧ cq.1 * cq.2 ≤ squareRootEndpoint R then
              canonicalMoebiusWeight cq.1 else 0))
    _ = ∑ q ∈ Finset.Icc (R + 8) (squareRootEndpoint R),
        ∑ c ∈ Finset.Ico 1 R,
          if q.Prime ∧ c * q ≤ squareRootEndpoint R then
            canonicalMoebiusWeight c else 0 := by
      exact Finset.sum_comm
    _ = ∑ q ∈ Finset.Icc (R + 8) (squareRootEndpoint R),
        if q.Prime then primeDilatedLowCofactorMass R q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hprime : q.Prime
      · simp [hprime, primeDilatedLowCofactorMass]
      · simp [hprime]
    _ = squareRootFarPrimeTransport R := by
      unfold squareRootFarPrimeTransport
      apply Finset.sum_congr rfl
      intro q hqMem
      by_cases hprime : q.Prime
      · have hRq : R < q := by
          have hqLow := (Finset.mem_Icc.mp hqMem).1
          omega
        have hmass := primeDilatedLowCofactorMass_eq_mertensSummatory
          R q (by omega) hRq hprime.pos
        simp [hprime, hmass]
      · simp [hprime]

/-- **Far physical transport identity.**  The literal far tagged physical
ledger is exactly the already-existing far-prime Mertens transform.  Thus the
#618 subtraction can now be moved onto one literal physical carrier without
changing signed mass. -/
theorem lowWheelFarTaggedPhysicalLedger_eq_farPrimeTransport
    (R : ℕ) (hR : 2 ≤ R) :
    lowWheelFarTaggedPhysicalLedger R = squareRootFarPrimeTransport R := by
  calc
    lowWheelFarTaggedPhysicalLedger R =
        ∑ z ∈ lowWheelFarTaggedPhysicalStableCarrier R,
          lowWheelFullTaggedPhysicalWeight z :=
      lowWheelFarTaggedPhysicalLedger_eq_stable R
    _ = lowWheelFarPrimeSquarefreePairMass R :=
      sum_lowWheelFarTaggedPhysicalStableCarrier_eq_squarefreePairMass R hR
    _ = lowWheelFarPrimePairMass R :=
      lowWheelFarPrimeSquarefreePairMass_eq_pairMass R
    _ = squareRootFarPrimeTransport R :=
      lowWheelFarPrimePairMass_eq_farPrimeTransport R hR

end RHLean.Proof
