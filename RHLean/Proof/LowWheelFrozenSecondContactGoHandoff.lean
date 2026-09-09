import Mathlib
import RHLean.Proof.LowWheelFrozenSecondContactDescent
import RHLean.Proof.SquareRootLowPrimeFirstOwnerWallRecurrence

/-!
# Frozen second-contact descent is a native Go predecessor window

`LowWheelFrozenSecondContactDescent` gives a sign-preserving injection

`y |-> (q,V)`

from the genuine frozen second-contact population, with

`q * P(V) <= X < q^2 * P(V)`

and every prime of `V` strictly below `q`.

This file identifies that independently-defined target with the existing frozen
predecessor window used by the Go recursion:

`X/q^2 < P(V) <= X/q`.

Consequently the complete fixed-owner target has exact signed mass

`F_{q^-}(X/q) - F_{q^-}(X/q^2)`.

This is a genuine handoff to an already-compiled smaller-scale signed object;
no norm, counting estimate, PNT input, or Mertens hypothesis is introduced.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The native frozen predecessor window at one second-contact owner. -/
def lowWheelFrozenSecondContactOwnerWindow
    (R q : ℕ) : Finset (Finset ℕ) :=
  frozenPrimeUniverseWindowFaces
    (primesUpTo (q - 1))
    (squareRootEndpoint R / (q * q))
    (squareRootEndpoint R / q)

/-- **Carrier identification.**  At a genuine prime owner below the root, the
independently-defined target from #627 is exactly the native frozen Go window. -/
theorem mem_lowWheelFrozenSecondContactParentCarrier_iff_ownerWindow
    {R q : ℕ} {V : Finset ℕ}
    (hq : q.Prime) (hqR : q < R) :
    (q, V) ∈ lowWheelFrozenSecondContactParentCarrier R ↔
      V ∈ lowWheelFrozenSecondContactOwnerWindow R q := by
  constructor
  · intro hz
    rcases mem_lowWheelFrozenSecondContactParentCarrier.mp hz with
      ⟨_hqRange, _hVR, _hqPrime, hpred, hupperMul, hlowerMul⟩
    apply mem_frozenPrimeUniverseWindowFaces.mpr
    refine ⟨hpred, ?_, ?_⟩
    · apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hq.pos hq.pos)).2
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlowerMul
    · apply (Nat.le_div_iff_mul_le hq.pos).2
      simpa [Nat.mul_comm] using hupperMul
  · intro hV
    rcases mem_frozenPrimeUniverseWindowFaces.mp hV with
      ⟨hpred, hlower, hupper⟩
    have hqRange : q ∈ Finset.Icc 2 (R - 1) :=
      Finset.mem_Icc.mpr ⟨hq.two_le, by omega⟩
    have hVR : V ∈ (primesUpTo R).powerset := by
      apply Finset.mem_powerset.mpr
      intro r hr
      have hrPred := (Finset.mem_powerset.mp hpred) hr
      rcases mem_primesUpTo.mp hrPred with ⟨hrPrime, hrq⟩
      exact mem_primesUpTo.mpr ⟨hrPrime, by omega⟩
    have hupperMul : q * primeFaceProduct V ≤ squareRootEndpoint R := by
      have h := (Nat.le_div_iff_mul_le hq.pos).1 hupper
      simpa [Nat.mul_comm] using h
    have hlowerMul : squareRootEndpoint R < q * q * primeFaceProduct V := by
      have h := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hq.pos hq.pos)).1 hlower
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
    apply mem_lowWheelFrozenSecondContactParentCarrier.mpr
    exact ⟨hqRange, hVR, hq, hpred, hupperMul, hlowerMul⟩

/-- Every actual frozen second-contact source lands directly in the native Go
owner window, not merely in a newly named carrier. -/
theorem lowWheelFrozenSecondContactParentFace_mem_ownerWindow
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    lowWheelFrozenSecondContactParentFace y ∈
      lowWheelFrozenSecondContactOwnerWindow R
        (lowWheelFrozenCofactorTopPrime y) := by
  have hparent := lowWheelFrozenSecondContactParentMap_mem hy
  have hdata := mem_lowWheelFrozenSecondContactParentCarrier.mp hparent
  have hqPrime : (lowWheelFrozenCofactorTopPrime y).Prime := hdata.2.2.1
  have hqR : lowWheelFrozenCofactorTopPrime y < R := by
    have hqRange := Finset.mem_Icc.mp hdata.1
    omega
  apply (mem_lowWheelFrozenSecondContactParentCarrier_iff_ownerWindow
    hqPrime hqR).mp
  simpa [lowWheelFrozenSecondContactParentMap] using hparent

/-- Exact signed mass of the complete native owner window. -/
def lowWheelFrozenSecondContactOwnerWindowMass (R q : ℕ) : ℤ :=
  frozenPrimeUniverseWindowMass
    (primesUpTo (q - 1))
    (squareRootEndpoint R / (q * q))
    (squareRootEndpoint R / q)

/-- **Strict lower-scale signed handoff.**  One complete owner window is exactly
the difference of two frozen predecessor states, at the two cutoffs exposed by
#627. -/
theorem lowWheelFrozenSecondContactOwnerWindowMass_eq_frozenDifference
    {R q : ℕ} (hq : q.Prime) :
    lowWheelFrozenSecondContactOwnerWindowMass R q =
      frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / q) -
        frozenPrimeUniverseMass (primesUpTo (q - 1))
          (squareRootEndpoint R / (q * q)) := by
  unfold lowWheelFrozenSecondContactOwnerWindowMass
  apply frozenPrimeUniverseWindowMass_eq_sub
  exact Nat.div_le_div_left (by nlinarith [hq.two_le]) hq.pos

/-- The inherited one-prime cutoff is strictly below the source endpoint. -/
theorem lowWheelFrozenSecondContactOwnerWindow_upper_strict
    {R q : ℕ} (hX : 0 < squareRootEndpoint R) (hq : q.Prime) :
    squareRootEndpoint R / q < squareRootEndpoint R :=
  Nat.div_lt_self hX hq.one_lt

/-- The square-dilated cutoff is strictly below the inherited one-prime cutoff
whenever that inherited cutoff is nonzero. -/
theorem lowWheelFrozenSecondContactOwnerWindow_lower_strict
    {R q : ℕ} (hq : q.Prime)
    (hpos : 0 < squareRootEndpoint R / q) :
    squareRootEndpoint R / (q * q) < squareRootEndpoint R / q := by
  have hdrop :
      (squareRootEndpoint R / q) / q < squareRootEndpoint R / q :=
    Nat.div_lt_self hpos hq.one_lt
  simpa [Nat.div_div_eq_div_mul] using hdrop

end RHLean.Proof
