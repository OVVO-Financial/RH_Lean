import Mathlib
import RHLean.Analysis.DyadicTransportCompression

/-!
# Exact prime-dilate compression of canonical transport packets

This module generalizes the dyadic cancellation theorem from the pairing
`(c,q) <-> (2c,q)` to the prime-dilate pairing

`(c,q) <-> (p*c,q)`.

For distinct primes `p` and `q`, with `p ∤ c`, the two channels have opposite
Möbius weights, the same transition index `q - 1`, and nested square-root entry
indices. Their common transport suffix therefore cancels identically. The only
surviving packet is the boundary between the parent entry `sqrt(cq)` and the
child entry `sqrt(pcq)`.

At a square endpoint `X = R^2 - 1`, writing

`B = floor(X / q)`,

the same boundary is exactly the reciprocal shell

`B / p < c <= B`.

Equivalently, up to the integer floor already built into `B`, this is the
`1/p` shell

`X / (p*q) < c <= X / q`.

All statements below are exact finite identities. No cancellation estimate or
RH implication is asserted.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- The `p`-dilated child cofactor. -/
def primeDilateChildCofactor (p c : ℕ) : ℕ := p * c

/-- Endpoint of the residual boundary packet after prime-dilate cancellation. -/
def primeDilateBoundaryUpper (N p c q : ℕ) : ℕ :=
  min (Nat.sqrt (primeDilateChildCofactor p c * q)) (finiteTransportUpper N q)

/-- The parent channel is active but its `p`-dilated child has not yet entered. -/
def IsPrimeDilateBoundaryActive (N p c q t : ℕ) : Prop :=
  Nat.sqrt (c * q) ≤ t ∧ t < primeDilateBoundaryUpper N p c q

instance instDecidableIsPrimeDilateBoundaryActive (N p c q t : ℕ) :
    Decidable (IsPrimeDilateBoundaryActive N p c q t) := by
  unfold IsPrimeDilateBoundaryActive primeDilateBoundaryUpper finiteTransportUpper
  infer_instance

/-- Möbius-weighted contribution of the residual prime-dilate boundary packet. -/
def primeDilateBoundaryContribution (N p c q t : ℕ) : ℂ :=
  if IsPrimeDilateBoundaryActive N p c q t then
    canonicalMoebiusWeight (c * q)
  else
    0

/-- Prime dilation can only move the square-root entry weakly later. -/
theorem sqrt_mul_le_sqrt_primeDilateChild_mul
    (p c q : ℕ) (hp : p.Prime) :
    Nat.sqrt (c * q) ≤ Nat.sqrt (primeDilateChildCofactor p c * q) := by
  apply Nat.sqrt_le_sqrt
  unfold primeDilateChildCofactor
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp.ne_zero
  have hc : c ≤ p * c := by
    simpa using Nat.mul_le_mul_right c hp1
  exact Nat.mul_le_mul_right q hc

/-- Multiplication by a genuinely new prime flips the full Möbius source weight. -/
theorem canonicalMoebiusWeight_primeDilateChild
    {p c q : ℕ} (hp : p.Prime) (hnew : ¬ p ∣ c * q) :
    canonicalMoebiusWeight (primeDilateChildCofactor p c * q) =
      -canonicalMoebiusWeight (c * q) := by
  have hcop : Nat.Coprime p (c * q) := hp.coprime_iff_not_dvd.mpr hnew
  have hmu : μ (p * (c * q)) = -μ (c * q) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
    rw [ArithmeticFunction.moebius_apply_prime hp]
    simp
  simpa [primeDilateChildCofactor, canonicalMoebiusWeight, Nat.mul_assoc] using
    congrArg (fun z : ℤ => (z : ℂ)) hmu

/-- If `p` and `q` are distinct primes and `p ∤ c`, then `p` is a genuinely new
prime factor of the source `c*q`. -/
theorem canonicalMoebiusWeight_primeDilateChild_of_distinct_primes
    {p c q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpc : ¬ p ∣ c) :
    canonicalMoebiusWeight (primeDilateChildCofactor p c * q) =
      -canonicalMoebiusWeight (c * q) := by
  apply canonicalMoebiusWeight_primeDilateChild hp
  intro hdiv
  rcases hp.dvd_mul.mp hdiv with hdivc | hdivq
  · exact hpc hdivc
  · have heq : p = q :=
      ((Nat.dvd_prime hq).mp hdivq).resolve_left hp.ne_one
    exact hpq heq

/-- Activity of the prime-dilated child implies activity of the parent channel. -/
theorem finiteTransportActive_parent_of_primeDilateChild
    {N p c q t : ℕ} (hp : p.Prime)
    (h : IsFiniteTransportActive N (primeDilateChildCofactor p c) q t) :
    IsFiniteTransportActive N c q t := by
  exact ⟨(sqrt_mul_le_sqrt_primeDilateChild_mul p c q hp).trans h.1, h.2⟩

/-- The explicit residual interval is exactly the active part of the parent not
shared by the `p`-dilated child. -/
theorem primeDilateBoundaryActive_iff_parent_and_not_child
    (N p c q t : ℕ) :
    IsPrimeDilateBoundaryActive N p c q t ↔
      IsFiniteTransportActive N c q t ∧
        ¬IsFiniteTransportActive N (primeDilateChildCofactor p c) q t := by
  constructor
  · intro h
    have hlt := lt_min_iff.mp h.2
    refine ⟨⟨h.1, hlt.2⟩, ?_⟩
    intro hchild
    exact (not_lt_of_ge hchild.1) hlt.1
  · rintro ⟨hparent, hnotChild⟩
    have hltChild : t < Nat.sqrt (primeDilateChildCofactor p c * q) := by
      by_contra hnot
      apply hnotChild
      exact ⟨Nat.le_of_not_gt hnot, hparent.2⟩
    exact ⟨hparent.1, lt_min hltChild hparent.2⟩

/-- Exact pointwise cancellation of a parent channel with its distinct-prime
`p`-dilated child. The common suffix vanishes identically; only the entry
boundary remains. -/
theorem finiteTransportContribution_add_primeDilateChild
    (N p c q t : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpc : ¬ p ∣ c) :
    finiteTransportContribution N c q t +
        finiteTransportContribution N (primeDilateChildCofactor p c) q t =
      primeDilateBoundaryContribution N p c q t := by
  have hweight :=
    canonicalMoebiusWeight_primeDilateChild_of_distinct_primes hp hq hpq hpc
  by_cases hparent : IsFiniteTransportActive N c q t
  · by_cases hchild :
        IsFiniteTransportActive N (primeDilateChildCofactor p c) q t <;>
      simp [finiteTransportContribution, primeDilateBoundaryContribution,
        hparent, hchild, hweight,
        primeDilateBoundaryActive_iff_parent_and_not_child N p c q t]
  · have hchild :
        ¬IsFiniteTransportActive N (primeDilateChildCofactor p c) q t := by
      intro h
      exact hparent (finiteTransportActive_parent_of_primeDilateChild hp h)
    simp [finiteTransportContribution, primeDilateBoundaryContribution,
      hparent, hchild,
      primeDilateBoundaryActive_iff_parent_and_not_child N p c q t]

/-- Finite residual packet left after exact prime-dilate cancellation. -/
def primeDilateBoundaryPacket (N p c q : ℕ) : ℂ :=
  ∑ t ∈ Finset.range (N + 1), primeDilateBoundaryContribution N p c q t

/-- Exact packet-level prime-dilate compression identity. -/
theorem finiteTransportPacket_add_primeDilateChild
    (N p c q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpc : ¬ p ∣ c) :
    finiteTransportPacket N c q +
        finiteTransportPacket N (primeDilateChildCofactor p c) q =
      primeDilateBoundaryPacket N p c q := by
  unfold finiteTransportPacket primeDilateBoundaryPacket
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact finiteTransportContribution_add_primeDilateChild
    N p c q t hp hq hpq hpc

/-! ## Exact `1/p` reciprocal boundary at a square endpoint -/

/-- Reciprocal cofactor cutoff in the prime-first `q`-fiber at `X = R^2 - 1`. -/
def primeDilateReciprocalCutoff (R q : ℕ) : ℕ :=
  squareRootEndpoint R / q

/-- Geometric boundary condition saying the parent source is inside the square
prefix while its `p`-dilated child is outside. -/
def IsPrimeDilateSquareBoundary (p R q c : ℕ) : Prop :=
  c * q ≤ squareRootEndpoint R ∧
    squareRootEndpoint R < primeDilateChildCofactor p c * q

/-- The square-prefix parent/child boundary is exactly the `1/p` reciprocal
cofactor shell. If `B = floor((R^2-1)/q)`, then

`parent inside, p-child outside  <->  B/p < c <= B`.
-/
theorem primeDilateSquareBoundary_iff_reciprocalShell
    (p R q c : ℕ) (hp : p.Prime) (hq : 0 < q) :
    IsPrimeDilateSquareBoundary p R q c ↔
      c ≤ primeDilateReciprocalCutoff R q ∧
        primeDilateReciprocalCutoff R q / p < c := by
  unfold IsPrimeDilateSquareBoundary primeDilateReciprocalCutoff
  constructor
  · rintro ⟨hparent, hchild⟩
    have hcB : c ≤ squareRootEndpoint R / q :=
      (Nat.le_div_iff_mul_le hq).2 hparent
    have hBltpc : squareRootEndpoint R / q < p * c := by
      apply (Nat.div_lt_iff_lt_mul hq).2
      simpa [primeDilateChildCofactor, Nat.mul_assoc] using hchild
    have hshell : (squareRootEndpoint R / q) / p < c := by
      apply (Nat.div_lt_iff_lt_mul hp.pos).2
      simpa [Nat.mul_comm] using hBltpc
    exact ⟨hcB, hshell⟩
  · rintro ⟨hcB, hshell⟩
    have hparent : c * q ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hq).1 hcB
    have hBltcp : squareRootEndpoint R / q < c * p :=
      (Nat.div_lt_iff_lt_mul hp.pos).1 hshell
    have hBltpc : squareRootEndpoint R / q < p * c := by
      simpa [Nat.mul_comm] using hBltcp
    have hchild : squareRootEndpoint R < (p * c) * q :=
      (Nat.div_lt_iff_lt_mul hq).1 hBltpc
    exact ⟨hparent, by simpa [primeDilateChildCofactor] using hchild⟩

/-- The literal finite `1/p` shell in a prime-first `q`-fiber. -/
def primeDilateReciprocalShell (p R q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (primeDilateReciprocalCutoff R q)).filter fun c =>
    ¬ p ∣ c ∧ primeDilateReciprocalCutoff R q / p < c

@[simp] theorem mem_primeDilateReciprocalShell
    {p R q c : ℕ} :
    c ∈ primeDilateReciprocalShell p R q ↔
      1 ≤ c ∧ c ≤ primeDilateReciprocalCutoff R q ∧
        ¬ p ∣ c ∧ primeDilateReciprocalCutoff R q / p < c := by
  simp [primeDilateReciprocalShell, and_assoc]

/-- With the new-prime condition `p ∤ c`, membership in the finite reciprocal
shell is exactly the source-level condition that `(c,q)` is present but
`(p*c,q)` lies beyond the square boundary. -/
theorem mem_primeDilateReciprocalShell_iff_squareBoundary
    (p R q c : ℕ) (hp : p.Prime) (hq : 0 < q) :
    c ∈ primeDilateReciprocalShell p R q ↔
      1 ≤ c ∧ ¬ p ∣ c ∧ IsPrimeDilateSquareBoundary p R q c := by
  rw [mem_primeDilateReciprocalShell,
    primeDilateSquareBoundary_iff_reciprocalShell p R q c hp hq]
  aesop

end RHLean.Proof
