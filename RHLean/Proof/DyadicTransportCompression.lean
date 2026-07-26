import Mathlib
import RHLean.Arithmetic.MoebiusDoubling
import RHLean.Proof.TwoABPrimeDilation

/-!
# Exact dyadic compression of canonical transport packets

This module isolates the exact cancellation supplied by Möbius doubling.  For an
odd lower cofactor `c` and an odd upper prime `q`, the channels `(c,q)` and
`(2c,q)` have opposite Möbius weights, the same transition index `q-1`, and
nested entry indices.  Their common transport suffix therefore cancels
identically, leaving only the boundary packet between the two entry scales.

All statements in this file are finite identities.  No cancellation estimate or
RH implication is asserted.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The finite-horizon endpoint for a transport channel.  Stages are restricted
to `0,...,N`, while the intrinsic transition endpoint is `q-1`. -/
def finiteTransportUpper (N q : ℕ) : ℕ :=
  min (q - 1) (N + 1)

/-- A raw prime-cofactor transport channel is active at stage `t` exactly between
its square-root entry and its finite-horizon endpoint. -/
def IsFiniteTransportActive (N c q t : ℕ) : Prop :=
  Nat.sqrt (c * q) ≤ t ∧ t < finiteTransportUpper N q

instance instDecidableIsFiniteTransportActive (N c q t : ℕ) :
    Decidable (IsFiniteTransportActive N c q t) := by
  unfold IsFiniteTransportActive finiteTransportUpper
  infer_instance

/-- Raw Möbius-weighted transport contribution of one factor channel. -/
def finiteTransportContribution (N c q t : ℕ) : ℂ :=
  if IsFiniteTransportActive N c q t then
    canonicalMoebiusWeight (c * q)
  else
    0

/-- The doubled cofactor channel. -/
def dyadicChildCofactor (c : ℕ) : ℕ :=
  2 * c

/-- Endpoint of the exact residual boundary packet after parent-child
cancellation. -/
def dyadicBoundaryUpper (N c q : ℕ) : ℕ :=
  min (Nat.sqrt (dyadicChildCofactor c * q)) (finiteTransportUpper N q)

/-- The residual dyadic boundary packet. -/
def IsDyadicBoundaryActive (N c q t : ℕ) : Prop :=
  Nat.sqrt (c * q) ≤ t ∧ t < dyadicBoundaryUpper N c q

instance instDecidableIsDyadicBoundaryActive (N c q t : ℕ) :
    Decidable (IsDyadicBoundaryActive N c q t) := by
  unfold IsDyadicBoundaryActive dyadicBoundaryUpper finiteTransportUpper
  infer_instance

/-- Möbius-weighted contribution of the residual boundary packet. -/
def dyadicBoundaryContribution (N c q t : ℕ) : ℂ :=
  if IsDyadicBoundaryActive N c q t then
    canonicalMoebiusWeight (c * q)
  else
    0

/-- Doubling the cofactor can only move the square-root entry weakly later. -/
theorem sqrt_mul_le_sqrt_dyadicChild_mul (c q : ℕ) :
    Nat.sqrt (c * q) ≤ Nat.sqrt (dyadicChildCofactor c * q) := by
  apply Nat.sqrt_le_sqrt
  exact Nat.mul_le_mul_right q (by omega : c ≤ dyadicChildCofactor c)

/-- Möbius doubling flips the full source weight when the parent product is odd. -/
theorem canonicalMoebiusWeight_dyadicChild
    {c q : ℕ} (hc : Odd c) (hq : Odd q) :
    canonicalMoebiusWeight (dyadicChildCofactor c * q) =
      -canonicalMoebiusWeight (c * q) := by
  have hodd : Odd (c * q) := hc.mul hq
  have hμ := RHLean.Arithmetic.moebius_two_mul_of_odd (c * q) hodd
  simpa [dyadicChildCofactor, canonicalMoebiusWeight, Nat.mul_assoc] using
    congrArg (fun z : ℤ => (z : ℂ)) hμ

/-- Prime-specialized form of the dyadic Möbius sign flip. -/
theorem canonicalMoebiusWeight_dyadicChild_of_prime
    {c q : ℕ} (hc : Odd c) (hq : q.Prime) (hq2 : q ≠ 2) :
    canonicalMoebiusWeight (dyadicChildCofactor c * q) =
      -canonicalMoebiusWeight (c * q) :=
  canonicalMoebiusWeight_dyadicChild hc (hq.odd_of_ne_two hq2)

/-- Activity of the doubled child implies activity of the parent channel. -/
theorem finiteTransportActive_parent_of_child
    {N c q t : ℕ}
    (h : IsFiniteTransportActive N (dyadicChildCofactor c) q t) :
    IsFiniteTransportActive N c q t := by
  exact ⟨(sqrt_mul_le_sqrt_dyadicChild_mul c q).trans h.1, h.2⟩

/-- The explicit boundary interval is exactly the active part of the parent not
shared by the doubled child. -/
theorem dyadicBoundaryActive_iff_parent_and_not_child
    (N c q t : ℕ) :
    IsDyadicBoundaryActive N c q t ↔
      IsFiniteTransportActive N c q t ∧
        ¬IsFiniteTransportActive N (dyadicChildCofactor c) q t := by
  constructor
  · intro h
    have hlt := (lt_min_iff.mp h.2)
    refine ⟨⟨h.1, hlt.2⟩, ?_⟩
    intro hchild
    exact (not_lt_of_ge hchild.1) hlt.1
  · rintro ⟨hparent, hnotChild⟩
    have hltChild : t < Nat.sqrt (dyadicChildCofactor c * q) := by
      by_contra hnot
      apply hnotChild
      exact ⟨Nat.le_of_not_gt hnot, hparent.2⟩
    exact ⟨hparent.1, lt_min hltChild hparent.2⟩

/-- Exact pointwise cancellation of an odd parent with its doubled child. -/
theorem finiteTransportContribution_add_dyadicChild
    (N c q t : ℕ) (hc : Odd c) (hq : Odd q) :
    finiteTransportContribution N c q t +
        finiteTransportContribution N (dyadicChildCofactor c) q t =
      dyadicBoundaryContribution N c q t := by
  rw [canonicalMoebiusWeight_dyadicChild hc hq]
  unfold finiteTransportContribution dyadicBoundaryContribution
  rw [dyadicBoundaryActive_iff_parent_and_not_child]
  by_cases hp : IsFiniteTransportActive N c q t
  · by_cases hchild : IsFiniteTransportActive N (dyadicChildCofactor c) q t <;>
      simp [hp, hchild]
  · have hchild : ¬IsFiniteTransportActive N (dyadicChildCofactor c) q t := by
      intro h
      exact hp (finiteTransportActive_parent_of_child h)
    simp [hp, hchild]

/-- Finite raw transport packet of one channel. -/
def finiteTransportPacket (N c q : ℕ) : ℂ :=
  ∑ t ∈ Finset.range (N + 1), finiteTransportContribution N c q t

/-- Finite residual dyadic boundary packet. -/
def dyadicBoundaryPacket (N c q : ℕ) : ℂ :=
  ∑ t ∈ Finset.range (N + 1), dyadicBoundaryContribution N c q t

/-- Exact packet-level dyadic compression identity. -/
theorem finiteTransportPacket_add_dyadicChild
    (N c q : ℕ) (hc : Odd c) (hq : Odd q) :
    finiteTransportPacket N c q +
        finiteTransportPacket N (dyadicChildCofactor c) q =
      dyadicBoundaryPacket N c q := by
  unfold finiteTransportPacket dyadicBoundaryPacket
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact finiteTransportContribution_add_dyadicChild N c q t hc hq

/-- Uncompressed finite transport amplitude of a family indexed by odd parent
cofactors. -/
def dyadicUncompressedTransportFamily
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ) (N t : ℕ) : ℂ :=
  ∑ i ∈ U,
    (finiteTransportContribution N (c i) (q i) t +
      finiteTransportContribution N (dyadicChildCofactor (c i)) (q i) t)

/-- Compressed dyadic boundary amplitude of the same family. -/
def dyadicCompressedTransportFamily
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ) (N t : ℕ) : ℂ :=
  ∑ i ∈ U, dyadicBoundaryContribution N (c i) (q i) t

/-- Exact finite-family compression. -/
theorem dyadicUncompressedTransportFamily_eq_compressed
    {ι : Type*} (U : Finset ι) (c q : ι → ℕ) (N t : ℕ)
    (hc : ∀ i ∈ U, Odd (c i))
    (hq : ∀ i ∈ U, Odd (q i)) :
    dyadicUncompressedTransportFamily U c q N t =
      dyadicCompressedTransportFamily U c q N t := by
  unfold dyadicUncompressedTransportFamily dyadicCompressedTransportFamily
  apply Finset.sum_congr rfl
  intro i hi
  exact finiteTransportContribution_add_dyadicChild N (c i) (q i) t
    (hc i hi) (hq i hi)

/-- The doubled child has no active stage in the finite horizon exactly when its
entry lies beyond the horizon or at/after its intrinsic transition. -/
theorem no_finiteTransportActive_dyadicChild_iff
    (N c q : ℕ) :
    (¬∃ t, IsFiniteTransportActive N (dyadicChildCofactor c) q t) ↔
      N < Nat.sqrt (dyadicChildCofactor c * q) ∨
        q - 1 ≤ Nat.sqrt (dyadicChildCofactor c * q) := by
  constructor
  · intro hnone
    by_contra hnot
    push_neg at hnot
    have hentryHorizon : Nat.sqrt (dyadicChildCofactor c * q) ≤ N :=
      Nat.le_of_not_gt hnot.1
    have hentryTransition :
        Nat.sqrt (dyadicChildCofactor c * q) < q - 1 :=
      Nat.lt_of_not_ge hnot.2
    apply hnone
    refine ⟨Nat.sqrt (dyadicChildCofactor c * q), ?_⟩
    constructor
    · exact le_rfl
    · unfold finiteTransportUpper
      exact lt_min hentryTransition (by omega)
  · rintro (hHorizon | hTransition) ⟨t, ht⟩
    · have htUpper := (lt_min_iff.mp ht.2).2
      omega
    · have htUpper := (lt_min_iff.mp ht.2).1
      omega

/-- Every unmatched doubled child is therefore an explicit finite-horizon or
born-smooth boundary, with no unclassified third case. -/
def IsDyadicFiniteHorizonBoundary (N c q : ℕ) : Prop :=
  N < Nat.sqrt (dyadicChildCofactor c * q)

/-- The doubled child has already lost its transport interval before entry. -/
def IsDyadicBornSmoothBoundary (c q : ℕ) : Prop :=
  q - 1 ≤ Nat.sqrt (dyadicChildCofactor c * q)

/-- Exact classification of absent child packets. -/
theorem no_finiteTransportActive_dyadicChild_iff_boundary
    (N c q : ℕ) :
    (¬∃ t, IsFiniteTransportActive N (dyadicChildCofactor c) q t) ↔
      IsDyadicFiniteHorizonBoundary N c q ∨
        IsDyadicBornSmoothBoundary c q := by
  exact no_finiteTransportActive_dyadicChild_iff N c q

end RHLean.Proof
