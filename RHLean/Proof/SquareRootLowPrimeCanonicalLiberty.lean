import Mathlib
import RHLean.Proof.SquareRootLowPrimeHorizontalTerminalCoverage

/-!
# Canonical prime liberties for finite processed-seat matching

Every state removed by the processed-seat matching is removed in one concrete
fresh-prime pair.  The only states without such an owned prime stage are the
states in the final matching frontier.

For the horizontal first-owner cut, intrinsic child absence in the original
processed carrier is also opened here.  Once the proposed owner `p` is prime,
within the terminal owner cutoff, fresh for the parent, and above the parent's
canonical largest prime, all arithmetic legality of the child is automatic.
Consequently an intrinsically missing child can fail only at one of the two
literal carrier walls:

* its cofactor `p*c` lies beyond the square endpoint; or
* the fixed seat index lies beyond the child's combined response fibre.

The second alternative is the existing parent/child response-window boundary,
not a mutable-row matching skip.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- A concrete prime liberty, together with its chronological location in the
matching list. -/
def SquareRootLowPrimePrimeLibertyData
    (ps : List ℕ) (S : Finset (Option (ℕ × ℕ)))
    (x : Option (ℕ × ℕ)) : Prop :=
  ∃ pre p post,
    ps = pre ++ p :: post ∧
      x ∈ squareRootLowPrimeProcessedSeatPaired
        (squareRootLowPrimeProcessedSeatMatchingFrontier pre S) p

/-- The exposed no-liberty boundary after every listed prime has been
processed. -/
def squareRootLowPrimeNoLibertyBoundary
    (ps : List ℕ) (S : Finset (Option (ℕ × ℕ))) :
    Finset (Option (ℕ × ℕ)) :=
  squareRootLowPrimeProcessedSeatMatchingFrontier ps S

/-- **Canonical-liberty dichotomy.** -/
theorem squareRootLowPrime_mem_noLibertyBoundary_or_primeLiberty
    (ps : List ℕ) (S : Finset (Option (ℕ × ℕ)))
    {x : Option (ℕ × ℕ)} (hx : x ∈ S) :
    x ∈ squareRootLowPrimeNoLibertyBoundary ps S ∨
      SquareRootLowPrimePrimeLibertyData ps S x := by
  by_cases hterminal :
      x ∈ squareRootLowPrimeProcessedSeatMatchingFrontier ps S
  · exact Or.inl hterminal
  · exact Or.inr
      (squareRootLowPrimeProcessedSeat_removed_has_owner
        ps S hx hterminal)

/-- **Intrinsic processed-seat fallout has only genuine carrier obstructions.**

Suppose `some (c,s)` is canonical fallout at owner `p` relative to the original
processed carrier at cutoff `U`.  If `p` is prime and `p ≤ U`, then freshness
and `P⁺(c) < p` force the child cofactor `p*c` to have largest prime `p` and
nonzero Möbius weight.  Therefore the child can be absent from the original
carrier only because

`X_R < p*c`

or because its response fibre is too short for the inherited seat index:

`CombinedResponse(p*c) ≤ s`.

In particular, disappearance from a mutable matching row is not one of the
intrinsic obstruction cases. -/
theorem squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff_carrierObstruction
    {R K j U p c s : ℕ}
    (hp : p.Prime) (hpU : p ≤ U)
    (hfall :
      some (c, s) ∈ squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff
        (squareRootLowPrimeProcessedSeatCarrier R K j U) p) :
    squareRootEndpoint R < p * c ∨
      squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s := by
  rcases mem_squareRootLowPrimeProcessedSeatCanonicalOwnerFalloff.mp hfall with
    ⟨hparent, _hhead, hpFresh0, hchildMissing0, hrough0⟩
  have hpFresh : ¬ p ∣ c := by
    simpa [squareRootLowPrimeProcessedStateCofactor] using hpFresh0
  have hrough : canonicalLargestPrimeFactor c < p := by
    simpa [squareRootLowPrimeProcessedStateCofactor] using hrough0
  have hchildMissing :
      some (p * c, s) ∉ squareRootLowPrimeProcessedSeatCarrier R K j U := by
    simpa [squareRootLowPrimeProcessedSeatExtend] using hchildMissing0
  have hparentAtom :
      (c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U := by
    simpa [squareRootLowPrimeProcessedSeatCarrier] using hparent
  have hcSigned : c ∈ squareRootLowPrimeProcessedSignedCofactors R U :=
    (mem_squareRootLowPrimeProcessedSeatAtoms.mp hparentAtom).1
  rcases Finset.mem_filter.mp hcSigned with
    ⟨hcRange, _hcOwner, hcMu⟩
  have hcOne : 1 ≤ c := (Finset.mem_Icc.mp hcRange).1
  have hcPos : 0 < c := by omega
  by_cases hwall : squareRootEndpoint R < p * c
  · exact Or.inl hwall
  by_cases hseat :
      squareRootLowPrimeCombinedFreshResponse R K j (p * c) ≤ s
  · exact Or.inr hseat
  exfalso
  apply hchildMissing
  have hpcX : p * c ≤ squareRootEndpoint R := Nat.le_of_not_gt hwall
  have hsChild :
      s < squareRootLowPrimeCombinedFreshResponse R K j (p * c) :=
    Nat.lt_of_not_ge hseat
  have hlpfChild : canonicalLargestPrimeFactor (p * c) = p := by
    have h := canonicalLargestPrimeFactor_mul_prime_eq_of_rough hcPos hp hrough
    simpa [Nat.mul_comm] using h
  have hmuChild : μ (p * c) ≠ 0 := by
    rw [moebius_prime_mul_eq_neg_of_not_dvd hp hpFresh]
    exact neg_ne_zero.mpr hcMu
  have hchildSigned :
      p * c ∈ squareRootLowPrimeProcessedSignedCofactors R U := by
    unfold squareRootLowPrimeProcessedSignedCofactors
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, hpcX⟩, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hp.ne_zero (Nat.ne_of_gt hcPos))
    · exact ⟨by rw [hlpfChild]; exact hpU, hmuChild⟩
  have hchildAtom :
      (p * c, s) ∈ squareRootLowPrimeProcessedSeatAtoms R K j U :=
    mem_squareRootLowPrimeProcessedSeatAtoms.mpr ⟨hchildSigned, hsChild⟩
  unfold squareRootLowPrimeProcessedSeatCarrier
  exact Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨(p * c, s), hchildAtom, rfl⟩)

end RHLean.Proof
