# Partial-moment Schur route

The arbitrary-target identity is exact:

`Q_t = CLPM_t + CUPM_t - DLPM_t - DUPM_t`.

For any finite weighted population with total weight `W`, first target moment
`m_t`, and target second moment `Q_t`, the scaled Schur covariance

`W Q_t - m_t m_t^T`

is target-independent.  This is formalized in
`RHLean/Analysis/PartialMomentSchurTarget.lean`.

The immediate physical question is not whether covariance is target-invariant;
it is whether the Mertens-visible degree-one first moment can be transported
through the selected-11 / least-square deletion / q^2 daughter decomposition.
The Schur identity is useful because it cleanly separates target-dependent
rank-one first-moment energy from target-invariant covariance.  It must not be
used to discard the rank-one term: that term contains the hard degree-one mass.

Next target: instantiate the generic identity on each physical nonzero transition
row, then prove the exact degree-one projection formula for the first-moment
rank-one block.  Only after that should the least-square q-owner decomposition be
pushed through the same tagged carrier.
