import Mathlib
import RHLean.Analysis.NNSFiniteSelmerFourierIntegral

/-!
# Alpöge's actual number-field class-group characters in NNS

This is a literal translation of Alpöge's primeCl/ClDual source in
Mk0IdMapCongr.lean, using real number-field ideal classes and every
prime class in a specified finite S.

Alpöge's separate theorem Kum.shaZm connects these class-group
characters to actual ShaZm D r 0 for the same field under PTCase.
That imported theorem is NOT assumed or imported in RHLean.
No RH-strength bound is asserted here.
-/

noncomputable section
open NumberField IsDedekindDomain
open scoped BigOperators

namespace RHLean.Analysis

/-- Actual ideal class of a height-one prime of a number field. -/
def alpogeNativePrimeCl {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

/-- Exact Alpöge ClDual relations at finite torsion modulus:
homomorphism condition and vanishing at selected prime ideals.
The source is actual number-field ideal classes, not a generic matrix. -/
def alpogeNativeClDualConstraint
    (K : Type*) [Field K] [NumberField K]
    (q : Nat) [NeZero q]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (theta : ClassGroup (𝓞 K) -> ZMod q) :
    ((ClassGroup (𝓞 K) × ClassGroup (𝓞 K)) -> ZMod q) ×
      (S -> ZMod q) :=
  (fun ab => theta (ab.1 * ab.2) - theta ab.1 - theta ab.2,
   fun v => theta (alpogeNativePrimeCl v.1))

/-- Exactly the original ClDual carrier, with no weakened local test. -/
theorem alpogeNativeClDualConstraint_zero_iff
    (K : Type*) [Field K] [NumberField K]
    (q : Nat) [NeZero q]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (theta : ClassGroup (𝓞 K) -> ZMod q) :
    alpogeNativeClDualConstraint K q S theta = 0 ↔
      (∀ a b, theta (a * b) = theta a + theta b) ∧
      (∀ v ∈ S, theta (alpogeNativePrimeCl v) = 0) := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    constructor
    · intro a b
      have h1' := congrFun h1 (a, b)
      change theta (a * b) - theta a - theta b = 0 at h1'
      have heq : theta (a * b) - (theta a + theta b) = 0 := by
        calc
          theta (a * b) - (theta a + theta b) =
              theta (a * b) - theta a - theta b := by abel
          _ = 0 := h1'
      exact sub_eq_zero.mp heq
    · intro v hv
      have hv' := congrFun h2 ⟨v, hv⟩
      simpa [alpogeNativeClDualConstraint] using hv'
  · rintro ⟨h1, h2⟩
    apply Prod.ext
    · funext ab
      change theta (ab.1 * ab.2) - theta ab.1 - theta ab.2 = 0
      rw [h1]
      abel
    · funext v
      change theta (alpogeNativePrimeCl v.1) = 0
      exact h2 v.1 v.2

/-
`ClassGroup (𝓞 K)` is finite (`NumberField.RingOfIntegers.instFintypeClassGroup`)
but carries no computable `DecidableEq`, so the finite function space
`ClassGroup (𝓞 K) → ZMod q` is a `Fintype` only classically. The statements
below therefore elaborate with classical decidability in scope; the `classical`
tactic inside a proof comes too late for instances needed by the statement.
-/

open scoped Classical in
/-- Exact NNS UPM1/LPM1 decomposition of this field's class characters. -/
theorem alpogeNativeClDualNNS_exact
    (K : Type*) [Field K] [NumberField K]
    (q : Nat) [NeZero q]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (target : Real) :
    nnsFiniteRelationMass (alpogeNativeClDualConstraint K q S) =
      upperPartialMass (Finset.univ : Finset (ClassGroup (𝓞 K) -> ZMod q))
          (fun theta =>
            nnsFiniteRelationIndicator
              (alpogeNativeClDualConstraint K q S) theta - target) -
      lowerPartialMass (Finset.univ : Finset (ClassGroup (𝓞 K) -> ZMod q))
          (fun theta =>
            nnsFiniteRelationIndicator
              (alpogeNativeClDualConstraint K q S) theta - target) +
      (Fintype.card (ClassGroup (𝓞 K) -> ZMod q) : Real) * target := by
  classical
  exact nnsFiniteRelationMass_eq_UPM_sub_LPM_target
    (alpogeNativeClDualConstraint K q S) target

open scoped Classical in
/-- Same field, same constraint: exactly complete character orthogonality. -/
theorem alpogeNativeClDualFourier_exact
    (K : Type*) [Field K] [NumberField K]
    (q : Nat) [NeZero q]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∑ theta : ClassGroup (𝓞 K) -> ZMod q,
      ∑ psi : AddChar
          (((ClassGroup (𝓞 K) × ClassGroup (𝓞 K)) -> ZMod q) ×
            (S -> ZMod q)) Complex,
        psi (alpogeNativeClDualConstraint K q S theta)) =
      (Fintype.card
          (((ClassGroup (𝓞 K) × ClassGroup (𝓞 K)) -> ZMod q) ×
            (S -> ZMod q)) : Complex) *
        (∑ theta : ClassGroup (𝓞 K) -> ZMod q,
          if alpogeNativeClDualConstraint K q S theta = 0
          then (1 : Complex) else 0) := by
  classical
  exact nnsFiniteRelation_fullCharacterDetector
    (alpogeNativeClDualConstraint K q S)

/-- The ACTUAL finite character set from Alpöge's ClDual predicate.
It is not an arbitrary finite-source certificate.
It lives in the universe of `K`, and is reducible so that instance search sees
the underlying subtype (and hence its `Fintype` structure). -/
abbrev alpogeNativeClDualMembers
    (K : Type*) [Field K] [NumberField K]
    (q : Nat) [NeZero q]
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Type _ :=
  {theta : ClassGroup (𝓞 K) -> ZMod q //
    (∀ a b, theta (a * b) = theta a + theta b) ∧
    (∀ v ∈ S, theta (alpogeNativePrimeCl v) = 0)}

open scoped Classical in
/-- The NNS relation integral counts EXACTLY the field-specific
ClDual characters, not merely an unrelated Fourier witness.
No determinant is used. -/
theorem alpogeNativeClDualMass_eq_char_card
    (K : Type*) [Field K] [NumberField K]
    (q : Nat) [NeZero q]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    nnsFiniteRelationMass (alpogeNativeClDualConstraint K q S) =
      (Fintype.card (alpogeNativeClDualMembers K q S) : Real) := by
  rw [Fintype.card_subtype, Finset.natCast_card_filter]
  unfold nnsFiniteRelationMass nnsFiniteRelationIndicator
  refine Finset.sum_congr rfl fun theta _ => ?_
  by_cases h : alpogeNativeClDualConstraint K q S theta = 0
  · rw [ite_eq_left h, ite_eq_left ((alpogeNativeClDualConstraint_zero_iff K q S theta).1 h)]
  · rw [ite_eq_right h, ite_eq_right (mt (alpogeNativeClDualConstraint_zero_iff K q S theta).2 h)]


end RHLean.Analysis
