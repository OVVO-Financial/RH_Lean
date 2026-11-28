# True-zero NNS Schur reconciliation on the original wheel stars

Continues #1214 at d1af59b. Paper proof with exact finite regression. The
upstream tether is exists_comparison_forms, heightLe_inv_ratio,
heightLe_liftVolume_ratio and integral_forms_long at lsernau/grh-lean
72fead102f663d5c7a407964a13dc0cf9d977207. No terminal theorem imported.

## 1. Work on the original star, not an enlarged primitive population

Use NativeMeasuredSlotProjector.columns, NativeAnchoredSlotMetric.wheelNormal
and NativeWheelNNSComparison.oriented_schur. For d=r+1 nonempty layers let
n_i=|S_i|, D_i the actual prime powers (pairwise coprime), P=prod D_i and
q_i=P/D_i=wheelNormal D i. At layer i the amplitude matrix X has columns
D_j e_j-D_0 e_0 (1<=j<d); each row is physically repeated n_i times.

The four NNS matrices must be evaluated before centering. The existing
star_divergent_zero proves that both divergent sectors vanish on the bare
star (every physical row has uniform sign). Thus this bare star by itself
does not expose signed divergence. Retain the anchor and the actual signed
arithmetic columns; in particular do not discard the first moment in
signed_normal_balance or the outside contribution in principal_metric_upper.

For an anchor a=(a_i) on the same layers, let A=[a,X],
N=diag(n_i), H_a=A^T N A, W_a=a^T N a, m_a=X^T N a and G=X^T N X.
The reconciled Gram K_a=G-m_a m_a^T/W_a is exactly the Gram of the
orthogonalized physical columns, when W_a != 0. For a=1 it is the existing
true-zero Schur covariance divided by total weight. For positive a_i,
it is also the ordinary weighted covariance (unnormalized) of X_i/a_i,
with weights n_i a_i^2. This last statement records the changed anchor
and weights; it is NOT merely a change of target in the old population.

## 2. Exact determinant on the same physical columns

Define Q_D(a)=sum_i q_i a_i. Then
    det A = Q_D(a),
    det H_a = (prod_i n_i) Q_D(a)^2,
    det K_a = (prod_i n_i) Q_D(a)^2/W_a.
Proof: factor diag(D_i) from the amplitude matrix. Its remaining first
column is a_i/D_i, and the remaining columns are e_j-e_0. Add all leaf
rows to the root row. The resulting first row is (sum a_i/D_i,0,...,0)
and the bottom-right block is I. Hence det A=P sum a_i/D_i.
This rational computation is an integer determinant identity for integer
D,a. Gram multiplicativity and the Schur identity prove the other two.

This replaces the ordinary star determinant (prod n_i)*dualEnergy by
an exact square of the normal reading divided by W_a. It does not
silently identify their volumes. In fact their exact ratio is
    det K_a / det G = Q_D(a)^2/(W_a * sum q_i^2/n_i).
The denominator is the independently measured wheel normal energy.
The first moment correction is retained in this identity.

For a common positive anchor and common retained counts, the relative
squared covolume between D and a second profile E satisfies
    det K_a(E)/det K_a(D) = (Q_E(a)/Q_D(a))^2.
All counts and the anchor norm cancel EXACTLY, even after place-dependent
cropping. Both profiles are the original physical stars, not new tops.

## 3. All-place common-anchor fitting of TWO comparison profiles

Let D_i=p_i^u_i and E_i=p_i^v_i (u_i,v_i>=0) with distinct site primes
p_i, so that both are genuine Euler admission profiles on the same
layers. Assume n_i>=4. At EACH finite prime l there are a common
anchor a and common retained counts n_i' satisfying

    a_i in {1,2,3}, at most one a_i differs from 1;
    n_i-2 <= n_i' <= n_i, l does not divide n_i';
    Q_D(a), Q_E(a), W_a'=sum n_i' a_i^2 are l-adic units.

Consequently BOTH augmented Gram matrices and BOTH reconciled star
Gram matrices are invertible over Z_l. Their projections and canonical
dual tests are l-integral. The physical address sets are obtained
by removing at most two actual slots per layer, keeping the original
upper boundary slot. The anchor is still constant on each original
layer, with bounded positive amplitudes.

Proof (odd l). The vector q(D) modulo l has either all coordinates
nonzero or exactly one nonzero coordinate (at the site of l), and
the same is true for q(E). If a singleton occurs in both vectors,
the site is the same. If both normal sums are nonzero, keep a=1.
Otherwise any vector with zero normal sum has all coordinates units.
Alter just one a_j by delta in {1,2}; this makes each previously
zero sum nonzero, and if the other sum was nonzero and q_j is a
unit it forbids at most one delta. If the other vector has singleton
support, one can choose j off that support. Thus for d>=2 there
are at least d-1 eligible sites; d=1 already has Q=1.
For each i choose n_i' in {n_i,n_i-1} nonzero modulo l. If W_a'=0,
choose a site with a_i nonzero modulo l (one exists by Q_D(a)!=0).
The three consecutive possible counts contain two distinct units
modulo odd l. One of these avoids the single forbidden norm residue.
This gives all three unit conditions simultaneously.

Proof (l=2). Each normal vector is either all ones or the singleton
at the site of 2; any two singleton supports coincide. If d is odd,
a=1 makes both sums odd. If d is even, toggle one a_j to 2, avoiding
the singleton support if present. Both sums become/remain odd, and
the number of odd anchor entries is odd. Take all counts odd by
cropping at most one slot each. Thus W_a' is odd. This includes the
case of an admitted even prime at one site. For d=1 simply take an
odd count.

The construction depends on the chosen finite place, as does the
upstream fit. It supplies the same actual anchor and counts for both
profiles at that place. It does NOT assert a single common fit for
arbitrarily many repeated profiles or a global common height witness.

## 4. Independent archimedean cost; choose the cheapest eligible site

All arithmetic in the choice above is explicit. Write
pi_i^D=q_i(D)/sum q(D), pi_i^E=q_i(E)/sum q(E). Among the at least
d-1 eligible sites choose j minimizing pi_j^D+pi_j^E, hence
pi_j^D+pi_j^E <= 2/(d-1). This works also at 2 (exclude the singleton
site when necessary). With delta=a_j-1<=2,
    Q_D(a)/Q_D(1)=1+delta*pi_j^D,
    Q_E(a)/Q_E(1)=1+delta*pi_j^E.
Since log(1+z)<=z, the absolute change in the relative LOG COVOLUME is
    |log(Q_E(a)/Q_D(a))-log(Q_E(1)/Q_D(1))| <= 4/(d-1)
for d>=2, and zero for d=1. Cropping and W_a cancel from this
relative cost. This is a per-block uniform bound at every place,
not a sum over all primes.

For an absolute archimedean bound, n_i' >= n_i-2 and a_i<=3 give
    |log det K_a'(D)-log det K_1(D)|
       <= 4(d+1)/n_min + 2 log 3.
Indeed |log(n_i'/n_i)|<=4/n_min, the normal ratio is in [1,3],
and W_a'/W is in [1-2/n_min,9]. The original thick band lemma
supplies n_min >= b/x^2 - 2, so deletion is economical on the
actual physical slots. No assumption of small signed discrepancy
enters these estimates.

There is also an independently bounded real dual, on the same original
star. Write Z=(I-aa^T/||a||^2)X using actual repeated physical rows.
For a=1 the sine squared of the angle between the anchor and star
is Q_D(1)^2/(W*dualEnergy) >= n_min/W, since
dualEnergy <= (sum q)^2/n_min. The smallest eigenvalue of X^T X is
at least min_{i>0} n_i D_i^2 >= n_min (the leaf squares alone).
Thus lambda_min(K_1) >= n_min^2/W and
    ||Z K_1^{-1}||_op <= sqrt(W)/n_min.
For a in [1,3] the same argument gives lambda_min(K_a) >=
n_min^2/(9W) and ||Z K_a^{-1}|| <= 3 sqrt(W)/n_min,
using the retained counts. For rank zero the table is empty.
These are actual measured norms, not values defined from the analytic
deficit.

Use the common table I on the original star rank. At the real place use
the literal anchor and canonical dual, at each finite place use the
common fitted anchor and the two canonical duals. Then Z_D^T gl_D=I
and Z_E^T gl_E=I, with both gl in their physical section ranges and
therefore orthogonal to the complements. Both duals and projections
are l-integral because the common pivot and both Schur Gram
determinants are units. This is a concrete native comparison-map
construction with independent real size, not an assigned height.
The common table's scalar is 1; the nontrivial scalar/line norm
relation in upstream exists_comparison_forms is NOT proved by this.

## 5. Exact NNS admission loss, with a joint rather than per-cell price

Keep the anchor and compare E_i=D_i F_i with F_i>=1, on the same
layers. With pi_i=(a_i/D_i)/sum_j(a_j/D_j) we have
    log(Q_E(a)/Q_D(a))
      = sum_i log F_i + log(sum_i pi_i/F_i).
Thus the nonnegative missing-normal charge is
    L(F)=-log(sum_i pi_i/F_i)
        =-log(1-sum_i pi_i(1-1/F_i)),
    0<=L(F)<=log(max_i F_i).

For disjoint admission sets C_k (as for the distinct clipped cofactor
cells at a fixed ancestor and shift), let F^(k) equal F on C_k and
1 elsewhere. All losses are evaluated relative to the SAME starting
D and anchor, as in translatedMarginal. Set
z_k=sum_{i in C_k} pi_i(1-1/F_i). Then sum z_k<1, and
    prod_k(1-z_k) >= 1-sum_k z_k
by induction, so
    sum_k L(F^(k)) <= L(F) <= log(max_i F_i).
Consequently even with arbitrary signed cell coefficients b_k,
    |sum_k b_k L(F^(k))| <= max_k |b_k| * log(max_i F_i).
This replaces a harmonic sum of separate log x allowances by one
joint log x allowance for the disjoint one-admission cells on each
original star. In the original uncentered metric the same argument
uses pi_i proportional to 1/(n_i D_i^2) and exponent -2, with
one-half outside the logarithm; hence the joint-price improvement
also applies directly to the existing marginal_volume comparison
without forcing a new analytic handoff. Do not assert this bound
for overlapping cells without counting overlaps.

For consecutive depth changes on the same profile one may instead
telescope the exact normal log ratios; retain every sign and all
outside terms. This is an economical recovery identity and a
quantitative bound on the normalization loss, not a cancellation
estimate for the full signed principal residual.

## 6. Precise remaining interface with Alpoge

This constructs the locally fitted flat/nonflat pair, common table
and separately bounded real dual on the ORIGINAL star ranks. It
also pays the local Schur correction and the disjoint-cell price.
The old literal constant index is not assumed to be a unit: the
common local anchor is explicitly altered when necessary.

Still open: the common algebraic height witness for the nontrivial
lift ratios, the relation between coefficient heights and those
actual relative norms in heightLe_inv_ratio, and their repeated
multiplicity with a separately established forward short-form
comparison. Local changes at infinitely many primes are not one
global rational object; a uniform real perturbation bound cannot
be summed over the primes. Local unimodularity and the table with
scalar 1 do not establish the signed quantitative estimate.

Preserve the actual signed normal reading in signed_normal_balance,
the original ASK/MAIN and discrepancy divisor, both the lower and
upper covolume inequalities on identical retained rows, and the
complete real cofinal-window quantifiers. No new conditional RH
closure interface. The terminal acceptance gate remains unchanged.

Exact regression: node scripts/research/check_native_schur_fit.js
executed with 17,280 simultaneous local fits, 69,120 determinant
identities, 34,560 local Schur unit checks, 1,440 disjoint-loss
checks, and 7,697 nontrivial repairs. These are finite checks of
the stated construction, not a Lean kernel certificate or an
asymptotic proof.
