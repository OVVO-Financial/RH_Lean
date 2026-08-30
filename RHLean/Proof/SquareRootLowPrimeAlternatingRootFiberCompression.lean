import Mathlib
import RHLean.Proof.SquareRootLowPrimeGoRootEqualityBoundary

/-!
# Alternating root-fibre compression

The strict Go crossing theorem already supplies the creation/response side of
the alternating rematching: every crossing incidence either has its existing
opposite-sign transport mate or lands on the exact root-equality boundary.
The root-equality boundary already has injective projection to its canonical
parent coordinate.

Combining those two compiled facts gives the missing fibre statement directly:
two crossing incidences over the same canonical parent which are both unmatched
by the existing transport pairing are the same incidence.  Thus an alternating
root fibre has at most one unmatched unit endpoint.

No new carrier, choice of representative, cardinality equivalence, analytic
estimate, or prime-count input is introduced here.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- **Alternating root-fibre compression.**

Take two genuine second-boundary crossing incidences over the same canonical
parent `d`.  If neither source has an available global transport mate, the
existing crossing dichotomy forces both incidences onto the exact root-equality
boundary.  Injectivity of the root-equality parent projection then identifies
the complete incidences, including both prime owners.

Equivalently: after the creation/response transport pairing has removed every
strict crossing, at most one unmatched unit occurrence remains over each
canonical root parent. -/
theorem squareRootLowPrimeAlternatingRootFiber_unique
    {R r q s t d : ℕ}
    (hR : 2 ≤ R)
    (hr : r.Prime) (hq : q.Prime) (hrq : r < q)
    (hqCube : q ^ 3 ≤ squareRootEndpoint R)
    (hqCross : squareRootEndpoint R < (q * r) ^ 2)
    (hdq : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
      q (squareRootEndpoint R) r)
    (hs : s.Prime) (ht : t.Prime) (hst : s < t)
    (htCube : t ^ 3 ≤ squareRootEndpoint R)
    (htCross : squareRootEndpoint R < (t * s) ^ 2)
    (hdt : d ∈ squareRootLowPrimeGoSecondBoundaryDefectParents
      t (squareRootEndpoint R) s)
    (hqUnmatched :
      (d, q) ∉ lowWheelCanonicalPairablePart
        (lowWheelCanonicalPhysicalStateSet R ({r} : Finset ℕ)))
    (htUnmatched :
      (d, t) ∉ lowWheelCanonicalPairablePart
        (lowWheelCanonicalPhysicalStateSet R ({s} : Finset ℕ))) :
    ((r, q), d) = ((s, t), d) := by
  have hqRoot :
      ((r, q), d) ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R := by
    rcases squareRootLowPrimeGoCrossing_pairable_or_rootEquality
        hR hq hr hrq hqCube hqCross hdq with hmate | hroot
    · exact (hqUnmatched hmate).elim
    · exact hroot
  have htRoot :
      ((s, t), d) ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R := by
    rcases squareRootLowPrimeGoCrossing_pairable_or_rootEquality
        hR ht hs hst htCube htCross hdt with hmate | hroot
    · exact (htUnmatched hmate).elim
    · exact hroot
  exact squareRootLowPrimeGoRootEquality_parentProjection_injOn
    R hqRoot htRoot rfl

/-- Pointwise form of the same compression: two surviving root-equality
endpoints occupying one canonical parent home are equal.  This is the literal
"at most one unmatched unit per root" statement on the post-rematching
endpoint carrier. -/
theorem squareRootLowPrimeAlternatingRootFiber_atMostOne
    {R d : ℕ} {x y : (ℕ × ℕ) × ℕ}
    (hx : x ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R)
    (hy : y ∈ squareRootLowPrimeGoRootEqualityDefectCarrier R)
    (hxd : x.2 = d) (hyd : y.2 = d) :
    x = y := by
  apply squareRootLowPrimeGoRootEquality_parentProjection_injOn R hx hy
  exact hxd.trans hyd.symm

end RHLean.Proof
