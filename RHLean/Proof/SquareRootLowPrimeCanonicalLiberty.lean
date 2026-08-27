import Mathlib
import RHLean.Proof.SquareRootLowPrimeHorizontalTerminalCoverage

/-!
# Canonical prime liberties for finite processed-seat matching

Every state removed by the processed-seat matching is removed in one concrete
fresh-prime pair.  The only states without such an owned prime stage are the
states in the final matching frontier.
-/

noncomputable section

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

end RHLean.Proof
