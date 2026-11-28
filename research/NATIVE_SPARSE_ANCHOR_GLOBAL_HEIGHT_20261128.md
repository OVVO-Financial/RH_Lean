# Sparse anchors, exact global height and the complete G_x handoff

Continuation of NATIVE_SIGN_SCHUR_GX_HANDOFF_20261128.md on the
original measured star rows. NativeSparseAnchorHeight.lean submits the
exact rational height arithmetic and primitive dual construction.
This is not a closed native RH proof or an imported terminal theorem.
Upstream tether: compact Alpoge at 72fead102f663d5c7a407964a13dc0cf9d977207,
HeckeValueHeight.heightLe_inv_ratio, ComparisonForms.exists_comparison_forms,
LiftVolumeHeight.heightLe_liftVolume_ratio, LongForms.integral_forms_long.

## 1. Remove the accidental cofactor primes entirely

Use the same actual wheel star, with d=r+1 nonempty layers, counts
n_i and powers D_i=p_i^beta_i. For an anchor indexed by j use the
literal indicator of that layer, a=e_j. Write X_D for the original
star (root row -D_0 times the all-ones vector, leaf rows D_i e_i).
Its augmented amplitude determinant is

    det [e_j,X_D] = q_j(D) = prod_{i != j} D_i.

The corresponding repeated-row augmented Gram and Schur determinant are

    det H_j(D) = (prod_i n_i) q_j(D)^2,
    det K_j(D) = (prod_{i != j} n_i) q_j(D)^2.

The Schur projection in this case simply removes the j-layer from
the star columns. It is not a change in the arithmetic population.

For the two actual depth profiles D,E and their common maximum M,
define r_i=D_i/E_i and the fixed full ratio R=prod_i r_i. The relative
sparse log covolume is exactly log R_j, where

    R_j=q_j(D)/q_j(E)=R/r_j.

The common unsigned NNS profile cancels just as in the earlier
four-channel lift; the high-thick site primes are odd and the
half-sums defining the doubled observations are integral.
No cofactor-sum prime outside the admitted labels now occurs in
the relative ratio. If one restores the omitted factor r_j,
the exact arithmetic reading is independent of j.

## 2. Independent comparison maps, with no Gram inversion

For every retained star column k (leaf label k+1) use the actual
layer-constant test

    T_j(k,i)=(1_{i=k+1}-1_{j=k+1})/(n_i D_i).

The formula is zero on the pivot layer j. Pair it in the original
counting metric with star column l. The n_i D_i factors cancel on
the same physical layer, and the result is delta_{kl}; this follows
by taking the difference of the numerator at i=l+1 and i=0.
It is therefore a simultaneous common-table comparison with table I
on exactly the original rank r.

The test lies in the range of the sparse projected star. Indeed
the amplitude map on the r nonpivot layers is a diagonal depth
matrix times a unimodular matrix: if j=0 the latter is I, otherwise
the deleted leaf row is replaced by the negative sum of the leaf
rows. Thus its range is the whole nonpivot layer-constant space.
This proves the relevant orthogonality to the complementary
physical directions directly.

Each nonzero test amplitude is +/-1/(n_i D_i).
For m0=min n_i, its squared energy is at most d/m0. The full
Hilbert-Schmidt squared norm of all r tests is at most
(2r-1)/m0 for r>=1: each retained leaf row has at most two nonzero
test amplitudes and the root row at most one; if the root is the
pivot there is only one per retained leaf. For r=0 there are no tests.
The same bound is true for each of D,E,M, independently of their
signed prime sum. This is a measured real norm, not a defined
analytic height. The Lean submission includes the individual
energy bound; the sharper full norm and range proof above are
paper deductions.

## 3. Exact three-profile fitting at every finite prime

At the place ell choose pivot j equal to its site index if ell
is an admitted label; otherwise choose j=0. All nonpivot powers
of D,E,M are units. Crop each n_i by at most ONE slot if necessary
to make it an ell-adic unit, preserving its original upper endpoint
when n_i>=2. Now all three augmented and Schur Gram determinants
are units. The explicit tests above are integral, with no Gram
denominator, for all three profiles at once. This also handles ell=2
because the actual high-thick primes are odd. The doubled lift
Grams are units by the determinant factorization.

This improves the dense common-anchor repair: no search over
small residue perturbations, at most one crop per original layer,
and no accidental primes in the relative determinant.

The finite pivot may vary with ell, while the original real
arithmetic comparison uses the same fixed profiles. This
variation must not be confused with a single fixed global scalar.

## 4. Recover the original volume comparison

For the literal all-ones anchor Q_D=sum_i q_i(D). Since
Q_D/Q_E=sum_i w_i R_i with w_i=q_i(E)/Q_E positive and summing to 1,

    min_i log R_i <= log(Q_D/Q_E) <= max_i log R_i.

Thus for any chosen pivot j,

    |log(Q_D/Q_E)-log R_j|
       <= max_i |log r_i-log r_j|
       <= 2 max_i |log r_i|.

Also |log(Q_D/Q_E)-log R|<=max_i |log r_i|.
These are signed relative bounds; no absolute bound on the
individual dense-to-sparse Gram ratio is assumed. The previously
proved angular bound compares the dense anchor to the original
uncentered star with price log(4x^3)/2. On the actual two
split-factorial depth profiles, |log r_i|=O(c log x), where
c=floor sqrt x, by the established uniform depth-difference bound.
After the original factor 6/(c k |tops|) and site density,
the new relative price is O(x^(eps/8) log x), within the existing
handoff ledger. The local sparsification is not free in relative
real log volume unless its omitted reading is restored.

All pivots together give the exact product

    prod_j R_j = R^(d-1).

For d>=2 the averaged log volume times d/(d-1) recovers log R
exactly. For d=1 the missing normal is the full single factor r_0,
which must be retained explicitly (the star rank is zero).

## 5. Complete the arithmetic handoff, including the unserved labels

Use the fixed calibrated split-factorial integer J of
SIGNED_MOBIUS_SPLIT_COMPENSATION_20261127.md, sections 3--5, with
m=4 floor(x/4) and c=floor sqrt(x). On the COMPLETE prime set

    P*={p prime: sqrt(x)<=p, p+1<=x}

use the same native available depths d_p=floor(c x/p)-c and
h_p=v_p(J), and the same two removals

    beta_p=d_p-floor(d_p/6),
    alpha_p=d_p-floor((h_p-6)_+/6).

The capacity and rounding estimates of section 5 depend only on
p^2>=x and p+1<=x, not on Frobenius class. Thus these definitions
are legitimate also at the unserved labels. All labels of the
previous U_x term belong to P* eventually; do not pretend they
are in the original served incidence family.

The single fixed global rational certificate is

    R_full(x)=prod_{p in P*} p^(beta_p-alpha_p).

It restores every omitted factor and includes every unserved
prime in the complete arithmetic comparison. No artificial
partner incidences are inserted. The signed depth formula gives

    (6/c)(beta_p-alpha_p)
        = E_res(p/m)+O(m/(c p)+1/c+1/p)

uniformly over P*. Chebyshev and summation by parts bound the
total weighted rounding error by O(sqrt(x) log x). Explicitly
sum_{sqrt(x)<=p<=x} log(p)/p=O(log x) and sum log p=O(x).
The calibrated residual has E_res(y)=O(y) at the origin and
vanishes on [1/6,1], by the earlier paper derivation. Hence
small prime and proper-power terms, and the endpoint p+1>x,
are already paid by the source transfer. These estimates give

    G_z(x) = -(6/c) log R_full(x) + O(sqrt(x) log x)

at each sufficiently large real x, as a paper consequence of
the earlier calibration and quadrature bounds. In the served
frame (6/c) log R_full = L_x+U_x+O(sqrt(x) log x+
x^(eps/8) log x). The complete unserved reading now occurs in
the SAME fixed global rational product instead of an omitted
term. This handoff is not a new conditional RH endpoint, and
the scalar window bound has not been proved.

## 6. The exact global height bill and why the last inequality is independent

At an admitted ell=p_i the locally chosen sparse ratio R_i is a unit.
At every other finite place each sparse ratio is a unit.
For the FIXED ratio R (or R_full), however,

    log |R|_{p_i}=-(beta_i-alpha_i) log p_i,
    log R + sum_i log |R|_{p_i}=0.

The omitted factor at p_i is exactly the signed gain/deficit
at that prime. Local-unit fitting is thus not a proof of a global
height saving. The Lean submission derives the complete rational
product formula from Nat.prod_pow_prime_padicValNat and proves
for any fixed positive rational H and R (cutoff beyond numerator
and denominator of H R)

    log H + sum_ell log |H R|_ell = -log R.

Consequently any common-witness upper height bill for the fixed
family R has to be at least -log R. Choosing H=1/R attains it;
choosing a different rational witness does not improve it.
The same conclusion for arbitrary algebraic witnesses follows
from the product formula for the constant family 1 after
recentring by R, as in upstream HeightLe.nonneg. This latter
observation is a paper deduction, not an imported terminal claim.
For the varying local-unit family the optimal bill is zero,
but its real ratio is NOT the fixed R. Restoring the omitted
factor reintroduces exactly the signed arithmetic amount.

This isolates the remaining mathematical task: prove an
INDEPENDENT inequality coupling the actual factorial J to the
original depth allocation, on the same physical family, such that
the common global certificate satisfies

    log R_full(x) >= -C_eps c x^(1/2+K eps)

uniformly on the original complete cofinal windows. The explicit
tests, norms, and local units no longer obstruct the construction;
the nontrivial coefficient/height gain in Alpoge heightLe_inv_ratio
must be reproduced, not defined from this signed prime sum.

To see the logical boundary, generic integral capacity is
insufficient. On all primes in (x/3,x/2), take available d_p as
above, beta_p=d_p-floor(d_p/2), alpha_p=d_p. Both are admissible
half-capacity profiles and every sparse fit and exact test works.
But (6/c) log R <= -(3-O(1/c)) sum log p = -Theta(x) by PNT.
This is not the actual calibrated factorial profile or a
counterexample to RH. It shows that the missing independent
arithmetic property cannot follow from the primitive matrix
identities and local fitting alone, even within the physical
depth capacity. A proposed universal linear-algebra inequality
would fail on these legitimate profiles.

No external terminal theorem, changed acceptance gate, or
unproved signed estimate has been introduced. Continue at the
actual upstream nontrivial coefficient-norm comparison, not
more repetitions of the fixed-ratio product formula.

## Verification

Exact integer/rational regression: scripts/research/check_native_sparse_anchor.js.
In this session: 15,120 determinant checks, 95,760 exact common-table
pairings, 25,200 independent energy bounds, 249,480 local
unit/integrality checks, and 11,340 global ratio/valuation identities,
396,900 checks in total. These are finite exact checks, not
asymptotic or Lean verification. Twenty-five new proof roots are
registered in the strict and explicit axiom audits; hosted
verification is pending. The terminal native_riemannHypothesis
and the uniform signed inequality remain open.
