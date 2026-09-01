import Mathlib
import RHLean.Arithmetic.SignedBuchstabRecursion
import RHLean.Proof.SquareRootLowPrimeNoLibertyBoundaryHome
import RHLean.Proof.SquareRootLowPrimeFirstOwnerFalloutWidth
import RHLean.Proof.SquareRootLowPrimeProcessedSeatCarrier
import RHLean.Proof.SquareRootLowPrimeSequentialDissipation

/-!
# Born-partner coordinate change for the no-liberty embedding

The no-liberty closure needs an actual
`SquareRootLowPrimeDescendingBoundaryWeightEmbedding`: a weight-preserving
injection from the descending processed-seat frontier into the four tagged
endpoint homes.  Source and target are stated in different coordinates, and
that mismatch is the first thing any classifier has to cross.

* A processed seat is `(c, s)` with `s` an **index**,
  `s < squareRootLowPrimeCombinedFreshResponse R K j c`, and real weight
  `-mu c`.
* A born endpoint is `(c, q)` with `q` an actual **prime partner**,
  `q ∈ squareRootBornPartnerSet R c`, and real weight
  `mu (squareRootLowPrimeBadAtomChild (c,q)) = mu (c * q)`.

This file builds that coordinate change and proves it is exactly weight
preserving, which is what the `weight_eq` field of the embedding demands.

## What is proved

* `squareRootLowPrimeSeatBornPartner` sends a seat index below
  `squareRootBornPartnerCount R c` to the corresponding born partner prime, in
  increasing order.  It lands in `squareRootBornPartnerSet R c`
  (`squareRootLowPrimeSeatBornPartner_mem`) and is injective in the index
  (`squareRootLowPrimeSeatBornPartner_injOn`).

* `moebius_mul_squareRootLowPrimeSeatBornPartner`: `mu (c * q) = - mu c` for the
  enumerated partner, because a born partner is prime and strictly above the
  canonical largest prime factor of `c`, hence fresh.

* `squareRootLowPrimeNoLibertyBoundaryWeight_bornSeat`: the born endpoint weight
  of the image equals the processed-seat weight of the source, in the exact
  form the embedding's `weight_eq` field asks for.  The born home is therefore
  weight-compatible with the seat carrier by arithmetic, not by convention.

* `squareRootLowPrimeBornSeatHome_injOn`: the resulting home map is injective on
  seats whose index is in born range.

## What this does not yet give, stated exactly

Two obligations remain before these pieces assemble into the embedding, and
neither is an estimate:

1. *No-successor membership.*  The target is
   `squareRootLowPrimeBornNoSuccessorAtoms`, not the full born atom set, so a
   stable seat must additionally satisfy
   `squareRootLowPrimeBadAtomChild (c,q) ∉ squareRootLowPrimeOwnedResponseCofactors R K U`.

2. *The complementary index range.*  The born coordinate change is defined only
   for `s < squareRootBornPartnerCount R c`.
   `squareRootLowPrimeSeat_lt_root_of_not_bornRange` proves that every seat
   outside that range has `c ≤ R - 1`: the uncovered seats are exactly the
   post-tail high-response seats, and they all sit below the root.  Whether a
   stable such seat always has a partial-packet or Go-root-equality home is the
   remaining classification question, and a stable seat with none would be the
   fifth geometry the four-home split omits.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-! ## Enumerating the born partners of one cofactor -/

/-- Increasing enumeration of the born partner primes of `c`. -/
def squareRootLowPrimeBornPartnerEnum (R c : ℕ) :
    Fin (squareRootBornPartnerCount R c) ↪o ℕ :=
  (squareRootBornPartnerSet R c).orderEmbOfFin rfl

/-- The born partner prime named by one processed-seat index.  Outside born
range the value is irrelevant and set to zero. -/
def squareRootLowPrimeSeatBornPartner (R c s : ℕ) : ℕ :=
  if h : s < squareRootBornPartnerCount R c then
    squareRootLowPrimeBornPartnerEnum R c ⟨s, h⟩
  else 0

/-- A born-range seat index names an actual born partner. -/
theorem squareRootLowPrimeSeatBornPartner_mem
    {R c s : ℕ} (hs : s < squareRootBornPartnerCount R c) :
    squareRootLowPrimeSeatBornPartner R c s ∈ squareRootBornPartnerSet R c := by
  unfold squareRootLowPrimeSeatBornPartner squareRootLowPrimeBornPartnerEnum
  rw [dif_pos hs]
  exact Finset.orderEmbOfFin_mem _ _ _

/-- Distinct born-range seat indices name distinct partners. -/
theorem squareRootLowPrimeSeatBornPartner_injOn
    {R c s t : ℕ}
    (hs : s < squareRootBornPartnerCount R c)
    (ht : t < squareRootBornPartnerCount R c)
    (h : squareRootLowPrimeSeatBornPartner R c s =
      squareRootLowPrimeSeatBornPartner R c t) :
    s = t := by
  unfold squareRootLowPrimeSeatBornPartner at h
  rw [dif_pos hs, dif_pos ht] at h
  have hfin : (⟨s, hs⟩ : Fin (squareRootBornPartnerCount R c)) = ⟨t, ht⟩ :=
    (squareRootLowPrimeBornPartnerEnum R c).injective h
  simpa using congrArg Fin.val hfin

/-! ## Arithmetic of the coordinate change -/

/-- The enumerated partner is prime. -/
theorem squareRootLowPrimeSeatBornPartner_prime
    {R c s : ℕ} (hs : s < squareRootBornPartnerCount R c) :
    (squareRootLowPrimeSeatBornPartner R c s).Prime :=
  (Finset.mem_filter.mp (squareRootLowPrimeSeatBornPartner_mem hs)).2.1

/-- The enumerated partner is strictly above the canonical largest prime factor
of the cofactor, so it is a genuinely fresh coordinate. -/
theorem squareRootLowPrimeSeatBornPartner_rough
    {R c s : ℕ} (hs : s < squareRootBornPartnerCount R c) :
    canonicalLargestPrimeFactor c < squareRootLowPrimeSeatBornPartner R c s :=
  (Finset.mem_filter.mp (squareRootLowPrimeSeatBornPartner_mem hs)).2.2.1

/-- Adjoining the born partner reverses the Möbius sign of the cofactor. -/
theorem moebius_mul_squareRootLowPrimeSeatBornPartner
    {R c s : ℕ} (hc : 0 < c) (hs : s < squareRootBornPartnerCount R c) :
    μ (c * squareRootLowPrimeSeatBornPartner R c s) = - μ c := by
  have hq := squareRootLowPrimeSeatBornPartner_prime hs
  have hrough := squareRootLowPrimeSeatBornPartner_rough hs
  have hnd : ¬ squareRootLowPrimeSeatBornPartner R c s ∣ c :=
    squareRootLowPrimePrime_fresh_of_lpf_lt hc hq hrough
  rw [Nat.mul_comm]
  exact moebius_prime_mul hq hnd

/-! ## Weight compatibility with the born home -/

/-- The born-range seat home. -/
def squareRootLowPrimeBornSeatHome (R : ℕ) (z : ℕ × ℕ) :
    SquareRootLowPrimeProcessedSeatNoLibertyState :=
  Sum.inr (Sum.inr (Sum.inl (z.1, squareRootLowPrimeSeatBornPartner R z.1 z.2)))

/-- **Exact weight preservation of the born coordinate change.**  This is the
`weight_eq` obligation of `SquareRootLowPrimeDescendingBoundaryWeightEmbedding`
for a born-range seat, discharged by arithmetic alone. -/
theorem squareRootLowPrimeNoLibertyBoundaryWeight_bornSeat
    {R c s : ℕ} (hc : 0 < c) (hs : s < squareRootBornPartnerCount R c) :
    squareRootLowPrimeNoLibertyBoundaryWeight
        (squareRootLowPrimeBornSeatHome R (c, s)) =
      squareRootLowPrimeProcessedSeatWeightReal (some (c, s)) := by
  have hmu := moebius_mul_squareRootLowPrimeSeatBornPartner hc hs
  have hchild :
      squareRootLowPrimeBadAtomChild
          (c, squareRootLowPrimeSeatBornPartner R c s) =
        c * squareRootLowPrimeSeatBornPartner R c s := rfl
  unfold squareRootLowPrimeBornSeatHome
  show squareRootLowPrimeNoLibertyBoundaryWeight
      (Sum.inr (Sum.inr (Sum.inl
        (c, squareRootLowPrimeSeatBornPartner R c s)))) =
    squareRootLowPrimeProcessedSeatWeightReal (some (c, s))
  rw [squareRootLowPrimeNoLibertyBoundaryWeight_born, hchild, hmu]
  rfl

/-- The born-range home map is injective. -/
theorem squareRootLowPrimeBornSeatHome_injOn
    {R : ℕ} {z w : ℕ × ℕ}
    (hz : z.2 < squareRootBornPartnerCount R z.1)
    (hw : w.2 < squareRootBornPartnerCount R w.1)
    (h : squareRootLowPrimeBornSeatHome R z = squareRootLowPrimeBornSeatHome R w) :
    z = w := by
  unfold squareRootLowPrimeBornSeatHome at h
  have hpair :
      (z.1, squareRootLowPrimeSeatBornPartner R z.1 z.2) =
        (w.1, squareRootLowPrimeSeatBornPartner R w.1 w.2) :=
    Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))
  rw [Prod.mk.injEq] at hpair
  obtain ⟨hfirst, hsecond⟩ := hpair
  have hwz : w.2 < squareRootBornPartnerCount R z.1 := by
    rw [hfirst]; exact hw
  have hsecond' :
      squareRootLowPrimeSeatBornPartner R z.1 z.2 =
        squareRootLowPrimeSeatBornPartner R z.1 w.2 := by
    rw [hsecond, hfirst]
  have hindex : z.2 = w.2 :=
    squareRootLowPrimeSeatBornPartner_injOn hz hwz hsecond'
  exact Prod.ext hfirst hindex

/-! ## The complementary index range -/

/-- **The seats the born coordinate change does not reach all lie below the
root.**  A processed seat outside born index range must be drawing on the
post-tail high response, which is available only for `c ≤ R - 1`.  So the
residual classification problem for the no-liberty embedding is confined to
sub-root cofactors, where the partial-packet and Go-root-equality homes live. -/
theorem squareRootLowPrimeSeat_lt_root_of_not_bornRange
    {R K j c s : ℕ}
    (hs : s < squareRootLowPrimeCombinedFreshResponse R K j c)
    (hnb : ¬ s < squareRootBornPartnerCount R c) :
    c ≤ R - 1 := by
  by_contra hc
  unfold squareRootLowPrimeCombinedFreshResponse at hs
  rw [if_neg hc] at hs
  omega

end RHLean.Proof
