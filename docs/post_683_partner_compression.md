# Post-#683 partner-column reciprocal compression

This note records the exact composition formalized in
`RHLean/Proof/PostRootPartnerReciprocalCompression.lean` and
`RHLean/Proof/PostRootPartnerEulerMemory.lean`.

The starting point is #683: for a fresh prime `p > R`, the adaptive raw
loss/birth boundary is the intact raw correlation of the parent, equivalently
its full signed partner-incidence column.  The reciprocal Euler coordinate is
the same response divided by the parent cofactor.

The new modules prove, before any norm:

1. `adaptiveRawWeightedMass_eq_cofactorWeightedReciprocalMass`: raw weighted
   mass equals reciprocal weighted mass after multiplying the coefficient by
   the cofactor.
2. `postRootAdaptiveRawBoundary_eq_cofactorWeightedReciprocalParents`: the
   post-root #683 boundary is exactly a cofactor-weighted reciprocal parent
   mass.
3. `postRootReciprocalNormalizedBoundary_eq_manyPrimeCompression`: after the
   reciprocal normalization `a(c)=1/c`, the #683 partner column feeds directly
   into the existing #540 actual-parent-carrier many-prime compression.  The
   output is exactly the Euler-scaled final-parent term plus the transported
   signed defect and survivor ledgers.
4. `natCast_mul_adaptiveCofactorWeightedPhysicalDefectMass_eq_rawBoundaryMass`:
   multiplying the cofactor-weighted reciprocal defect layer by the current
   prime recovers the raw signed loss/birth boundary exactly.
5. `cofactorWeighted_evolvedMismatch_eq_zero_of_completeDescendingPrefix`:
   the apparent coefficient mismatch introduced by cofactor weighting vanishes
   on the *actual evolved raw chronology* when the earlier prefix is complete
   and descending.  If the child has a larger physical prime extension, the
   four-corner theorem has already zeroed both evolved raw coefficients; if it
   has no larger extension, its reciprocal response is zero.
6. `evolvedRawBoundary_eq_scaledReciprocalDrop_of_completeDescendingPrefix`:
   the raw boundary is therefore exactly the current prime times the signed
   drop from the evolved raw state to its Euler-compressed reciprocal next
   state.
7. `adaptiveRawFinalMass_eq_zero_of_completeDescendingSchedule`: on a complete
   descending prime schedule the final raw mass is identically zero.  Every
   cofactor with nonzero rough response has an actual prime partner; at that
   partner step it is a literal parent and its zero-factor coefficient is
   killed permanently.
8. `lowWheelFrozenTopFarResidual_eq_rawLedger_add_rootCorrection_of_completeSchedule`:
   consequently the entire frozen/top/far residual is exactly its chronological
   signed raw ledger plus the already root-scale correction.  There is no final
   adaptive remainder to estimate.
9. `evolvedEulerNext_sub_rawNext_scaled_eq_boundaryMemory`: comparing the raw
   and reciprocal evolutions gives the exact memory law

   `p * (EulerNext - RawNext) = (p - 1) * Boundary`.

   Equivalently the boundary is retained in the next-state difference with the
   native Euler factor `1 - 1/p`.

The Stokes and memory identities are structural only.  They do **not** prove
FAR-4 or an energy inequality.  They do remove two previously ambiguous
objects: the post-root partner boundary is now an exact Euler-transported state
difference, and a complete descending schedule has no terminal raw mass.

The remaining exact seam is now narrower: identify/reassemble the chronological
boundary-memory ledger against the already-compiled canonical
prime-weighted/Abel telescope on the *actual physical schedule*.  The canonical
bridge is available, but it uses the full prime-prefix carrier; the physical
schedule can stop earlier.  What remains is therefore the explicit
actual-schedule versus canonical-prefix tail (or an exact proof that the
relevant physical schedule is complete on this carrier), before any ownerwise
norm is taken.  Only after that comparison is resolved should the FAR energy
estimate be attempted.
