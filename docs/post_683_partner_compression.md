# Post-#683 partner-column reciprocal compression

This note records the exact composition formalized in
`RHLean/Proof/PostRootPartnerReciprocalCompression.lean`.

The starting point is #683: for a fresh prime `p > R`, the adaptive raw
loss/birth boundary is the intact raw correlation of the parent, equivalently
its full signed partner-incidence column.  The reciprocal Euler coordinate is
the same response divided by the parent cofactor.

The new module proves, before any norm:

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

The last identity is a discrete Stokes formula on the actual physical carrier.
It is structural only.  It does **not** prove FAR-4 or an energy inequality.
The remaining quantitative question is whether these scaled signed drops can be
summed/reassembled across the physical q-squared owner schedule with a
subcritical energy constant, without destroying their chronology by taking
ownerwise norms.
