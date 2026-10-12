# Universal all-endpoint prime insertion: the physical signed-return problem

**11 October 2026.** This note treats every integer endpoint and actual prime insertion. Identities are exact finite arithmetic. Classical boundedness of prime reciprocal shells is the only analytic input in the diagonal bound. The fixed finite-C/A and RH claims remain OPEN. No new Lean compilation is claimed.

## 1. The one operation, valid for ALL x

For a finite initial segment P of the actual primes, let
\[
s_P(n)=\begin{cases}\mu(n),&n=1\text{ or all prime factors of }n\text{ lie in }P,\\0,&\text{otherwise},\end{cases}
\qquad
S_P(x)=\sum_{n\le x}s_P(n).
\]
Initially S_empty(x)=1 for x>=1. On admitting the fresh prime p, each new squarefree family coefficient at n=pc is exactly -s_P(c), with c<=floor(x/p). Consequently
\[
\boxed{S_{P\cup\{p\}}(x)=S_P(x)-S_P(\lfloor x/p\rfloor).}\tag{1}
\]
This holds for every x and every insertion, not only square endpoints or sufficiently large x. It is also the signed sum of the factor-depth recurrence
E_j(P+p,x)=E_j(P,x)+E_(j-1)(P,floor(x/p)).

If P includes all primes <p and p>sqrt(x), then c<=x/p<p, and the earlier primes already reconstruct the complete Mobius coefficients of all children:
\[
\boxed{S_p(x)-S_{p^-}(x)=-M(\lfloor x/p\rfloor).}\tag{2}
\]
The existing RHLean/Proof/PrimeCombReciprocalBandCancellation.lean theorem primeCombLargePrimeFamilyMass_eq_neg_mertens checks the essential large-prime family statement.

## 2. Canonical insertion versus prime-candidate animation

The candidate animation seeds untouched prime sites with -1. Its post-root update 2(1-M(floor(x/p))) is correct FOR THAT SEED, but not the net mass created by inserting the new prime into a smooth-only Euler field.

For p>sqrt(x), x/3<p<=x/2, the only fresh children are p and 2p. Their signs are -1 and +1. Thus the canonical update is -M(2)=0 at every eligible endpoint. For x/2<p<=x the only new site is p, so the canonical update is -M(1)=-1. For x<10 the hypothesis p>sqrt(x) should be checked; e.g. at x=5, p=2 has p^2<=x and does not qualify for the pair cancellation.

Independent genuine-prime/Mobius census:

| x | S_(floor sqrt x)(x) | S_(floor(x/3))(x) | complete 2p-shell update | S_(floor(x/2))(x) | last singleton additions | M(x) |
|---:|---:|---:|---:|---:|---:|---:|
|317|-3|25|0|25|-29|-4|
|1027|-12|72|0|72|-75|-3|
|100488|-918|4446|0|4446|-4474|-28|
|999999|-6355|37172|0|37172|-36960|212|

The candidate-field positive-suffix result is a representation-specific fact, not a generic contraction law of the physical prime-insertion process.

## 3. Exact all-x coefficient and scalar energy laws

For fixed x, view the s_P(n) as a coefficient vector indexed by 1<=n<=x. Let u_p(pc)=s_P(c), supported on multiples of the new prime p, and zero elsewhere. The old vector is zero on ALL multiples of p, hence old and new descendants have disjoint support and
\[
\boxed{\langle s_P,u_p\rangle=0,\quad
\|s_{P+p}\|_2^2=\|s_P\|_2^2+\|u_p\|_2^2,\quad
\|u_p\|_2^2=\sum_{c\le x/p}s_P(c)^2.}\tag{3}
\]
The unsigned coefficient energy therefore NEVER contracts when one adds a prime.

But the total signed projection obeys (1). Put
a_p=S_{p^-}(x), b_p=S_{p^-}(floor(x/p)). Then
\[
\boxed{S_p(x)^2-S_{p^-}(x)^2=b_p^2-2a_pb_p.}\tag{4}
\]
The sole mechanism by which the squared *total* can shrink is the signed mixed term 2a_pb_p. This is exact for every prime and every endpoint, including the pre-root stages.

At x=X=R^2-1, let a=S_(R-1)(X) and b_p=M(floor(X/p)) for actual primes R<=p<=X. Telescoping the genuine high-prime insertion gives
\[
\boxed{M(X)^2=a^2+\sum_{R\le p\le X}b_p^2
-2\sum_{R\le p\le X}S_{p^-}(X)b_p.}\tag{5}
\]

Exact chronological census:

| X | prepared a | sum b_p^2 | mixed 2sum S_(p^-)(X)b_p | final M(X)^2 |
|---:|---:|---:|---:|---:|
|317|-3|75|68|16|
|1027|-12|217|352|9|
|100488|-918|14896|856836|784|
|999999|-6355|124635|40465716|44944|

## 4. Correct-scale ALL-ROOT diagonal theorem

Let X=R^2-1, K_R=max_(0<=k<R) (M(k)-1)^2/(k+1)>=1 and let
Lambda=sup_(R>=2) sum_(R<=p<R^2, p prime) 1/p < infinity.
The latter is unconditional from classical prime reciprocal estimates.

For every genuine p in [R,X], k_p=floor(X/p)<R and
\[
M(k_p)^2\le 2(M(k_p)-1)^2+2\le2(k_p+1)K_R+2.
\]
For R>=3 the number N_R of these primes is <=X/2 (all are odd). Thus
\[
\begin{aligned}
\sum_{R\le p\le X} M(k_p)^2
&\le2K_R\left(X\sum_{R\le p\le X}\frac1p+N_R\right)+2N_R\\
&\le \boxed{(2\Lambda+2)XK_R.}\tag{6}
\end{aligned}
\]
The R=2 case is immediate by direct calculation. The companion repo's explicitly stated shell inequality Lambda<=5/6 gives the sharper displayed constant (11/3)XK_R if that explicit bound is invoked.

This also works for EVERY integer endpoint x>=4. Put r=floor(sqrt x), H=K_(r+1), and Lambda_*=sup_(x>=4)sum_(sqrt x<p<=x)1/p<infinity. Then
\[
\boxed{\sum_{\sqrt x<p\le x}M(\lfloor x/p\rfloor)^2
\le(2\Lambda_*+2)xH.}\tag{7}
\]
This is a proper all-x estimate at the correct SQUARED scale xH. It is **only a bound on the sum of the squares**, not on the square of the signed total.

## 5. What remains and why universality does not automatically prove RH

At X=R^2-1, to establish finite A (hence finite C and RH by the existing conditional bridge), one needs the mixed term in (5) to pay for the prepared square a^2, up to a fixed multiple of R^2 K_R. Equation (6) controls the diagonal at exactly that scale but supplies NO independent lower estimate for the mixed term. Rearranging (5) is not a proof of such an estimate.

Let (D_p f)(x)=f(floor(x/p)). Then (1) reads S_p=(I-D_p)S_(p^-), and the operators commute because D_p D_q=D_(pq)=D_q D_p. Chronological insertion is the exact construction, but the final result does not depend on insertion *order*. The process rule is universal, yet the actual occupancy and signs of the growing endpoint-truncated prime-factor families are the unproved pointwise quantitative restriction.

A successful universal proof must establish a non-circular SIGNED MIXED-RETURN INEQUALITY for (5), not count how many numerical x pass a threshold and not norm the positive and negative populations separately.

**Status:** exact all-x operator, family sign and coefficient orthogonality; all-root correct-scale diagonal theorem. OPEN: independent uniform mixed-return lower bound, fixed finite C, finite A, RH.