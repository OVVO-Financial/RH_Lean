import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BOUNDARY_ORIENTED_FUBINI»
import «research.VF_919_EULER_FIXED_WHEEL_SIX_CHANNEL_20261019»

/-!
# Why the historical active Euler 6x6 incidence has at most three columns

The genuine active returned pair has p-free clipped a and p-admitted
child p*b. After removing the greatest differing prime r, a raw parent
(u,v) is in one of TWO literal mixed-child forms:
  (a,b)=(r*u,v)  or  (a,b)=(u,r*v).

The FIRST form retains r*u<=X, p*r*u>X, p*v<=X.
The SECOND retains p*u>X, p*r*v<=X.
Here X=squareRootEndpoint (R+1)=(R+1)^2-1.

These inequalities FORCE the FIRST-RIGHT, NEXT-LEFT and RETURNED-RIGHT
historical oriented sectors to be empty on the true active support.
The other sectors are FIRST-LEFT, NEXT-RIGHT, RETURNED-LEFT.
This is not a 6x6 linear bijection and it supplies no uniform bound.

Both lemmas below use the ORIGINAL repository sector-set definitions,
not an invented substitute Boolean classifier.
-/

noncomputable section

open RHLean.Proof
namespace RHLean.Analysis

/-- If r divides the clipped p-free physical site a=r*u, then the
other p-free cofactor v is admitted and r*u is itself physical.
The three disallowed historical orientation filters cannot contain
this genuine raw parent, for ANY signature set. -/
theorem vf919EulerSectorSix_leftMixed_forbidden
    {R p r u v : ℕ} {sig : Finset ℕ}
    (hphysical : r * u ≤ squareRootEndpoint (R + 1))
    (hclipped : squareRootEndpoint (R + 1) < p * (r * u))
    (hadmitted : p * v ≤ squareRootEndpoint (R + 1)) :
    (u, v) ∉
      lowOwnerFirstOwnerIncompleteFirstClipRightSet
        (R + 1) p sig r ∧
    (u, v) ∉
      lowOwnerFirstOwnerIncompleteNextClipLeftSet
        (R + 1) p sig r ∧
    (u, v) ∉
      lowOwnerFirstOwnerIncompleteReturnedClipRightSet
        (R + 1) p sig r := by
  constructor
  · intro h
    have hright :
        squareRootEndpoint (R + 1) < p * v :=
      lowOwnerFirstOwnerIncompleteFirstClipRight_mem_implies_rightClip h
    exact (Nat.not_lt_of_ge hadmitted) hright
  constructor
  · intro h
    have hleft :
        squareRootEndpoint (R + 1) < r * u :=
      (Finset.mem_filter.mp h).2
    exact (Nat.not_lt_of_ge hphysical) hleft
  · intro h
    have hnotLeft :
        ¬ squareRootEndpoint (R + 1) < p * (r * u) :=
      (Finset.mem_filter.mp h).2
    exact hnotLeft hclipped

/-- If r divides the p-admitted cofactor b=r*v, the p-free
active site a=u is ALREADY p-clipped. Thus no right orientation
and no next-left classification can occur in the original Sector Six. -/
theorem vf919EulerSectorSix_rightMixed_forbidden
    {R p r u v : ℕ} {sig : Finset ℕ}
    (hclipped : squareRootEndpoint (R + 1) < p * u) :
    (u, v) ∉
      lowOwnerFirstOwnerIncompleteFirstClipRightSet
        (R + 1) p sig r ∧
    (u, v) ∉
      lowOwnerFirstOwnerIncompleteNextClipLeftSet
        (R + 1) p sig r ∧
    (u, v) ∉
      lowOwnerFirstOwnerIncompleteReturnedClipRightSet
        (R + 1) p sig r := by
  constructor
  · intro h
    have hnotLeft :
        ¬ squareRootEndpoint (R + 1) < p * u :=
      (Finset.mem_filter.mp h).2
    exact hnotLeft hclipped
  constructor
  · intro h
    have hnext :
        LowOwnerRawParentNextOwnerClipped
          (R + 1) p r (u, v) :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
    exact (Nat.not_lt_of_ge hnext.1) hclipped
  · intro h
    have hret :
        LowOwnerRawParentReturnedNextClipped
          (R + 1) p r (u, v) :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
    exact (Nat.not_lt_of_ge hret.1) hclipped

#print axioms vf919EulerSectorSix_leftMixed_forbidden
#print axioms vf919EulerSectorSix_rightMixed_forbidden

end RHLean.Analysis
