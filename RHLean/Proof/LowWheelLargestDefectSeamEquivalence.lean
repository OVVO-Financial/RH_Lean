import Mathlib
import RHLean.Proof.LowWheelLeastLargestStableTransfer
import RHLean.Proof.SquareRootCanonicalDowncrossFinalSeam

/-!
# The largest-prime stable defect is the terminal seam, not a reduction of it

`LowWheelLeastLargestStableTransfer` already proves the exact coordinate
synthesis

`lowWheelCanonicalDowncrossLedger R = lowWheelLargestDefectLedger R`.

That equality is an *identity of the same signed object*, so a linear bound on
the largest-prime stable defect is not a step toward the terminal seam: it **is**
the terminal seam.  This file records that explicitly, so the largest-prime
defect is not mistaken for an already-smaller remaining piece.

Concretely:

* `SquareRootLargestDefectLinearBound` is proved equivalent to
  `SquareRootCanonicalDowncrossLinearBound`, in both directions;
* consequently `riemannHypothesis_of_largestDefectLinear` derives the Riemann
  hypothesis from it through the existing square-prefix energy bridge.

Anything that proves the largest-prime defect bound therefore proves RH, and by
the handoff's own adversarial check 5 it must be treated as the hard theorem
rather than as an elementary auxiliary fact.

Two consequences worth stating for whoever picks this up next.

1.  The *signed* target is RH-strength.  It cannot be reached by exhibiting the
    defect's surviving pieces inside already-root-bounded endpoint populations
    unless those pieces also come with their signs and their mutual
    cancellation, because the total is the whole endpoint object.

2.  The *cardinality* target is dead by a full power of `R`, which is exactly
    the recorded support-only no-go.  Direct enumeration of
    `lowWheelLargestDefectPart` gives `|defect| / R` rising steadily
    `18.6, 22.7, ..., 140.1` across `R = 8, 9, ..., 30`, i.e. growth of order
    `R^2`, while the signed mass over the same range stays in `[-7, 9]`.  (That
    is a numerical observation, not a compiled claim; it is recorded only to
    stop the cardinality route being re-attempted.)

No norm, estimate, or density input is introduced here.  The file contains one
finite identity transported through an already-compiled equality.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- Linear-mass proposition stated on the largest-prime stable defect. -/
def SquareRootLargestDefectLinearBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      ‖lowWheelLargestDefectLedger R‖ ≤ C * (R : ℝ)

/-- **The two propositions are the same theorem.**  The largest-prime stable
defect carries exactly the canonical downcross ledger, so neither direction
costs anything beyond the compiled coordinate synthesis. -/
theorem squareRootLargestDefectLinear_iff_canonicalDowncrossLinear :
    SquareRootLargestDefectLinearBound ↔
      SquareRootCanonicalDowncrossLinearBound := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, fun R hR => ?_⟩
    rw [lowWheelCanonicalDowncrossLedger_eq_largestDefectLedger]
    exact hbound R hR
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, fun R hR => ?_⟩
    rw [← lowWheelCanonicalDowncrossLedger_eq_largestDefectLedger]
    exact hbound R hR

/-- **Therefore the largest-prime defect bound implies the Riemann
hypothesis.**  It is the terminal quantitative seam in different coordinates,
not an auxiliary step before it. -/
theorem riemannHypothesis_of_largestDefectLinear
    (h : SquareRootLargestDefectLinearBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_canonicalDowncrossLinear
    (squareRootLargestDefectLinear_iff_canonicalDowncrossLinear.mp h)

end RHLean.Proof
