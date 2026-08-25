import Mathlib
import RHLean.Proof.SquareRootLowPrimeProcessedSeatMatching

/-!
# Displacement diamonds for the low-prime sequential frontier

This module attacks the unstable-pivot population directly.

Fresh-prime extensions commute.  Hence two distinct prime coordinates `q < p`
form a literal four-corner square on every non-head processed seat:

```text
x              --p-->  p*x
| q                      | q
v                        v
q*x            --p-->  p*q*x.
```

Suppose the `q`-step removes one lower/upper pair, while the corresponding
`p`-translate survives that same step.  Then the opposite corner of the square
cannot still belong to the carrier: otherwise the translated `q`-edge would
also have been removed.  Thus an unstable pivot is not a new independent
residual.  It produces an actual missing support corner.

Moreover, for a fixed displaced pivot, distinct later primes produce distinct
missing corners.  This is the injective mechanism needed to charge all pivot
instabilities to the already-isolated born/high cutoff and first-failure
boundaries rather than once per prime.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Fresh-prime extensions commute on the processed seat carrier. -/
theorem squareRootLowPrimeProcessedSeatExtend_comm
    (p q : ℕ) (x : Option (ℕ × ℕ)) :
    squareRootLowPrimeProcessedSeatExtend p
        (squareRootLowPrimeProcessedSeatExtend q x) =
      squareRootLowPrimeProcessedSeatExtend q
        (squareRootLowPrimeProcessedSeatExtend p x) := by
  rcases x with _ | z
  · rfl
  · simp [squareRootLowPrimeProcessedSeatExtend,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Extending a non-head state keeps it non-head. -/
theorem squareRootLowPrimeProcessedSeatExtend_ne_none
    {p : ℕ} {x : Option (ℕ × ℕ)} (hx : x ≠ none) :
    squareRootLowPrimeProcessedSeatExtend p x ≠ none := by
  rcases x with _ | z
  · exact (hx rfl).elim
  · simp [squareRootLowPrimeProcessedSeatExtend]

/-- Cofactor projection of a non-head extension. -/
theorem squareRootLowPrimeProcessedStateCofactor_extend
    {p : ℕ} {x : Option (ℕ × ℕ)} (hx : x ≠ none) :
    squareRootLowPrimeProcessedStateCofactor
        (squareRootLowPrimeProcessedSeatExtend p x) =
      p * squareRootLowPrimeProcessedStateCofactor x := by
  rcases x with _ | z
  · exact (hx rfl).elim
  · rfl

/-- Freshness is preserved when extending by a distinct prime. -/
theorem squareRootLowPrimeProcessedSeatExtend_fresh_of_distinct
    {p q : ℕ} {x : Option (ℕ × ℕ)}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hx : x ≠ none)
    (hfresh : ¬ q ∣ squareRootLowPrimeProcessedStateCofactor x) :
    ¬ q ∣ squareRootLowPrimeProcessedStateCofactor
      (squareRootLowPrimeProcessedSeatExtend p x) := by
  rw [squareRootLowPrimeProcessedStateCofactor_extend hx]
  intro hdiv
  rcases hq.dvd_mul.mp hdiv with hqp | hqc
  · have hEq : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    exact hpq hEq.symm
  · exact hfresh hqc

/-- **Lower-endpoint displacement forces a missing top corner.**

If `x` is removed as the lower endpoint of a `q`-edge but its `p`-translate
survives the `q`-step, the `p*q` corner was not in the carrier. -/
theorem squareRootLowPrimeProcessedSeat_lowerDisplacement_forces_top_missing
    {S : Finset (Option (ℕ × ℕ))} {p q : ℕ}
    {x : Option (ℕ × ℕ)}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S q)
    (hpxFrontier :
      squareRootLowPrimeProcessedSeatExtend p x ∈
        squareRootLowPrimeProcessedSeatFrontierStep S q) :
    squareRootLowPrimeProcessedSeatExtend q
        (squareRootLowPrimeProcessedSeatExtend p x) ∉ S := by
  intro htop
  have hxData := mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower
  have hpxData := Finset.mem_sdiff.mp hpxFrontier
  have hpxNone : squareRootLowPrimeProcessedSeatExtend p x ≠ none :=
    squareRootLowPrimeProcessedSeatExtend_ne_none hxData.2.1
  have hqFresh :
      ¬ q ∣ squareRootLowPrimeProcessedStateCofactor
        (squareRootLowPrimeProcessedSeatExtend p x) :=
    squareRootLowPrimeProcessedSeatExtend_fresh_of_distinct
      hp hq hpq hxData.2.1 hxData.2.2.1
  have htranslatedLower :
      squareRootLowPrimeProcessedSeatExtend p x ∈
        squareRootLowPrimeProcessedSeatPairLower S q :=
    mem_squareRootLowPrimeProcessedSeatPairLower.mpr
      ⟨hpxData.1, hpxNone, hqFresh, htop⟩
  exact hpxData.2
    (Finset.mem_union.mpr (Or.inl htranslatedLower))

/-- **Upper-endpoint displacement forces a missing lower corner.**

If `q*x` is the upper endpoint of a removed `q`-edge but `p*q*x` survives the
same step, the opposite lower corner `p*x` was not in the carrier. -/
theorem squareRootLowPrimeProcessedSeat_upperDisplacement_forces_bottom_missing
    {S : Finset (Option (ℕ × ℕ))} {p q : ℕ}
    {x : Option (ℕ × ℕ)}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hxLower : x ∈ squareRootLowPrimeProcessedSeatPairLower S q)
    (hpqxFrontier :
      squareRootLowPrimeProcessedSeatExtend p
          (squareRootLowPrimeProcessedSeatExtend q x) ∈
        squareRootLowPrimeProcessedSeatFrontierStep S q) :
    squareRootLowPrimeProcessedSeatExtend p x ∉ S := by
  intro hbottom
  have hxData := mem_squareRootLowPrimeProcessedSeatPairLower.mp hxLower
  have htopData := Finset.mem_sdiff.mp hpqxFrontier
  have hbottomNone :
      squareRootLowPrimeProcessedSeatExtend p x ≠ none :=
    squareRootLowPrimeProcessedSeatExtend_ne_none hxData.2.1
  have hqFresh :
      ¬ q ∣ squareRootLowPrimeProcessedStateCofactor
        (squareRootLowPrimeProcessedSeatExtend p x) :=
    squareRootLowPrimeProcessedSeatExtend_fresh_of_distinct
      hp hq hpq hxData.2.1 hxData.2.2.1
  have htranslatedLower :
      squareRootLowPrimeProcessedSeatExtend p x ∈
        squareRootLowPrimeProcessedSeatPairLower S q :=
    mem_squareRootLowPrimeProcessedSeatPairLower.mpr
      ⟨hbottom, hbottomNone, hqFresh, by
        simpa [squareRootLowPrimeProcessedSeatExtend_comm] using htopData.1⟩
  have htranslatedUpper :
      squareRootLowPrimeProcessedSeatExtend p
          (squareRootLowPrimeProcessedSeatExtend q x) ∈
        squareRootLowPrimeProcessedSeatPairUpper S q := by
    unfold squareRootLowPrimeProcessedSeatPairUpper
    apply Finset.mem_image.mpr
    refine ⟨squareRootLowPrimeProcessedSeatExtend p x,
      htranslatedLower, ?_⟩
    exact (squareRootLowPrimeProcessedSeatExtend_comm p q x).symm
  exact htopData.2
    (Finset.mem_union.mpr (Or.inr htranslatedUpper))

/-- For a fixed nonzero seat cofactor, distinct extension primes give distinct
translated states. -/
theorem squareRootLowPrimeProcessedSeatExtend_prime_injective
    {x : Option (ℕ × ℕ)}
    (hx : x ≠ none)
    (hc : 0 < squareRootLowPrimeProcessedStateCofactor x) :
    Function.Injective
      (fun p => squareRootLowPrimeProcessedSeatExtend p x) := by
  intro p r hpr
  rcases x with _ | z
  · exact (hx rfl).elim
  · simp only [squareRootLowPrimeProcessedSeatExtend,
      Option.some.injEq, Prod.mk.injEq] at hpr
    have hmul : p * z.1 = r * z.1 := hpr.1
    exact Nat.mul_right_cancel hc hmul

/-- **No recurrent lower displacement without distinct missing corners.**
For a fixed removed lower pivot and fixed earlier coordinate `q`, the top
missing-corner assignment is injective in the later prime `p`. -/
theorem squareRootLowPrimeProcessedSeat_missingTopCorner_prime_injective
    {q : ℕ} {x : Option (ℕ × ℕ)}
    (hq : 0 < q) (hx : x ≠ none)
    (hc : 0 < squareRootLowPrimeProcessedStateCofactor x) :
    Function.Injective
      (fun p =>
        squareRootLowPrimeProcessedSeatExtend q
          (squareRootLowPrimeProcessedSeatExtend p x)) := by
  intro p r hpr
  rcases x with _ | z
  · exact (hx rfl).elim
  · simp only [squareRootLowPrimeProcessedSeatExtend,
      Option.some.injEq, Prod.mk.injEq] at hpr
    have houter : q * (p * z.1) = q * (r * z.1) := hpr.1
    have hinner : p * z.1 = r * z.1 :=
      Nat.mul_left_cancel hq houter
    exact Nat.mul_right_cancel hc hinner

/-- The lower missing-corner assignment from upper displacement is likewise
injective in the later prime. -/
theorem squareRootLowPrimeProcessedSeat_missingBottomCorner_prime_injective
    {x : Option (ℕ × ℕ)}
    (hx : x ≠ none)
    (hc : 0 < squareRootLowPrimeProcessedStateCofactor x) :
    Function.Injective
      (fun p => squareRootLowPrimeProcessedSeatExtend p x) :=
  squareRootLowPrimeProcessedSeatExtend_prime_injective hx hc

end RHLean.Proof
