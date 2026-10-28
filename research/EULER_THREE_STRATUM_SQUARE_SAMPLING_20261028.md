# Three moving Euler prime strata sampled across square blocks

**28 October 2026.** Exact integer arithmetic and a proof-driven statistical
sampling specification. This is a follow-on to merged PR #1043.

## Structural interpretation

The proposed "1 : sqrt(x), sqrt(x) : x/2, x/2 : x" partitions are **prime-factor
admission bands**, not three disjoint intervals of the site integer n.
The low stratum therefore includes *all* integers n<=x made solely from primes
at most sqrt(x), including large products n>sqrt(x).

For R>=2 and X_R=R^2-1, the actual prime boundary is y=R-1. Define

    E_R = sum_{n<=X_R, P+(n)<R} mu(n),
    T_R(mid) = sum_{R<=p<=floor(X_R/2), p prime} M(floor(X_R/p)),
    P_R = pi(X_R)-pi(floor(X_R/2)).

Here prime p>=R can occur at most once in a squarefree n<=X_R.
The cofactor c of a high-prime product n=pc is <=R-1. For p>X_R/2 the
only possible cofactor is c=1; hence **the last stratum is entirely
prime singletons with true Mobius sign -1**.

The identity is

    M(X_R) = E_R - T_R(mid) - P_R.

No random-sign law is used. The source Lean file defines the middle via
the full *actual prime-count reciprocal quotient bands* k=2,..,R-1:

    N_R(k) = pi(floor(X_R/k))
               - pi(max(R-1,floor(X_R/(k+1)))),

    T_R(mid)=sum_{k=2}^{R-1} M(k) N_R(k).

The exact k=1 band has mass N_R(1)=P_R. These facts are proved by reusing the
previously certified high-prime band decomposition, correcting p=R when R
is prime. No primes are modeled by Li or Poisson statistics.

## Random partition: make the index R random, not mu(n)

Select R uniformly from [H,2H) and write the three changing signed stratum
values as

    L_R = E_R,
    C_R = -T_R(mid),
    U_R = -P_R.

The *true* square-shell Mobius increment is

    delta_R = M(X_(R+1))-M(X_R)
            = a_R+b_R+c_R

where a_R=L_(R+1)-L_R, b_R=C_(R+1)-C_R and c_R=U_(R+1)-U_R.

These differences incorporate BOTH physical square-shell entries and the
changing prime-admission gate. One cannot freeze the prime-cutoff population
over moving R. No arbitrary packet regrouping is introduced.

The complete six-term second moment under uniform R-sampling is

    sum delta_R^2 = sum a_R^2 + sum b_R^2 + sum c_R^2
                  + 2 sum a_R b_R + 2 sum a_R c_R
                  + 2 sum b_R c_R.

The terms are all computed from the *same deterministic, physically
admitted Euler population*. No independence, decorrelation, Gaussian
distribution or martingale property is claimed.

## Why these extra partitions are analytically consequential

The top stratum is negative and coherent:

    U_R = -(pi(X_R)-pi(X_R/2)).

Its middle counterpart must generate a large *signed* composite response.
The low smooth population is a third coherent component. Thus reducing any
individual diagonal energy by calling it random destroys the cancellation
one is trying to explain. The off-diagonal payments are essential.

A separate, true CRT orthogonality fact for fixed coprime small divisor
periods does not imply orthogonality across *these* moving strata:
prime factors and period lengths depend on R, and typical joint divisor
periods can be much larger than the dyadic sampling window H.

## Rate target: explicitly OPEN

A valid independent arithmetic bound

    sum_{H<=R<2H} delta_R^2 <<_epsilon H^(5/2-eta+epsilon)

for eta>0 would improve Mertens' 7/8 exponent by eta/4 after Cauchy-Schwarz
and dyadic telescoping. The six-term identity is not that bound; neither
the root-dependent deterministic partitions nor any finite sample variance
alone proves a fixed power saving.

In particular, a well-behaved empirical mean/covariance over H values does
not yield a *uniform* inequality as H tends to infinity. Prove a bound on
the full coupled six-term expression, exploiting actual quadratic boundary
equidistribution with all gcd and incomplete-period terms retained.

## Regression and adversarial tests

scripts/euler_three_stratum_square_sampler.cpp calculates the true Mobius
function, largest prime factors, exact pi and reciprocal prime counts
through X_(10000)=99,999,999. It compares the quotient-band construction to
independently enumerated signed products at R=317,1027,5561,10000, then
samples the three dynamic component increments on dyadic windows
H=16,64,256,1024,4096. The exact signed six-term energy must reproduce the
original Mobius shell energy on each window.

Passing these numerical tests is a finite identity/correctness check only.


## Second sampling axis: the literal integer-site partitions

These are NOT merely bookkeeping categories. The hypothesis is that repeated
sampling through moving, physically determined partitions can behave as a
pseudorandomization operator on a deterministic multiplicative sign sequence.

The prime-owner bands above form one sampling axis. A separate location axis is

    S0(R) = [1,R-1]
    S1(R) = [R,floor(X_R/2)]
    S2(R) = [floor(X_R/2)+1,X_R].

For X_R=R^2-1, signed site-band masses are

    A_R=M(R-1)
    B_R=M(floor(X_R/2))-M(R-1)
    C_R=M(X_R)-M(floor(X_R/2)).

They satisfy A_R+B_R+C_R=M(X_R) exactly. The physical top half C_R
contains primes AND composites, unlike the prime-owner top class, which
consists entirely of prime singletons.

Both moving filters cross. Assign each nonzero Mobius site n<=X_R its
integer-location row and greatest-prime-factor column. Three cells are
structural zeros: site-low x owner-middle, site-low x owner-top, and
site-middle x owner-top. The other six must retain their original signs.

Now sample R uniformly over H<=R<2H. Let a_i(R) be the change in site
mass i when R advances by 1 and b_j(R) the corresponding change in
prime-owner band j. Both obey

    sum_i a_i(R)=sum_j b_j(R)=Delta_R.

The exact 3x3 cross moment is

    K_ij(H)=sum_{R=H}^{2H-1} a_i(R)*b_j(R).

The original square-block energy is precisely

    sum_R Delta_R^2 = sum_{i=0}^2 sum_{j=0}^2 K_ij(H).

The Lean theorem eulerSiteOwnerSampledCross_eq_nine_terms retains all
nine terms; eulerSiteOwnerSampledCross_eq_squareShellEnergy proves they
sum to the original shell energy. eulerSite_sampledSixTermGram also certifies
the independent six-term location-band variance decomposition.

Numerical audit scripts/euler_three_site_owner_surrogate_sampler.cpp uses
actual integer mu(n): directly enumerates all physical 3x3 cells at roots
317,1027,5561,10000 and all nine dynamic cross terms at
H=16,64,256,1024,4096.

### What stochastic mathematics can legitimately be imported?

Uniformly choosing R from [H,2H) makes each deterministic channel a random
variable by random selection of its input, NOT by random alteration of mu(n).
These variables are not assumed independent. This sampling gives exact
empirical moments and conditioned population probes. Any concentration
theorem requires proof of its hypotheses on the actual arithmetic masks.

Concentration of a Monte Carlo estimator of M(X), alone, does NOT bound
the deterministic value of M(X). Conservation identities themselves merely
reassemble the original second moment. An independent arithmetic mixing
bound is still necessary, accounting for quadratic residues, incomplete
prime periods, and common-prime-factor singularities.


## A genuinely provable deterministic randomization property

More than reassembly: for each FIXED divisor d>0, the square-block
multiple-count discrepancy has uniformly bounded *cumulative first moment*
over every consecutive interval of sampled roots. Define

    X_R=R^2-1,
    N_R(d)=floor(X_(R+1)/d)-floor(X_R/d),
    err_R(d)=d*N_R(d)-(X_(R+1)-X_R).

The actual count N_R(d) is nonnegative and the discrepancy has an exact
remainder representation:

    err_R(d)=(X_R mod d)-(X_(R+1) mod d).

Therefore every A<=B and d>0 satisfy

    sum_{R=A}^{B-1} err_R(d)
       = (X_A mod d)-(X_B mod d),
    |sum err_R(d)|<d.

Equivalently, the cumulative error between the exact number of divisor
multiples in the sampled square blocks and their total length divided
by d has absolute value STRICTLY LESS THAN 1. This is an all-interval,
all-d theorem, not a numerical approximation or randomness hypothesis.

Kernel certification:
research/EULER_SQUARE_BLOCK_DIVISOR_SURROGATE_20261028.lean
with eulerSquareBlockDivisorSampleError_eq_mod_boundary,
eulerSquareBlockDivisorSampleError_telescope and
eulerSquareBlockDivisorSampleError_abs_lt.

The essential limit is decisive: first moments of individual divisor
streams telescope beautifully; the needed Möbius power saving involves
a signed SECOND moment, with products of distinct divisor-count
errors and shared-prime/incomplete-period correlations. Proving bounds
for those true products is the arithmetic mixing theorem, still open.


## Two independent axes of nested partition sampling: numerical and probabilistic audit

The original three admission strata (low P+(n)<R, middle R<=P+(n)<=X/2,
upper P+(n)>X/2) are now **crossed with the integer-site ranges**
[1,R-1], [R,floor(X/2)] and (floor(X/2),X]. There are six nonempty
geometric cells; the top-prime cell contains ONLY singleton primes,
but the middle-prime band includes singleton primes p<=X/2 **as well as**
composites with that largest prime factor. Calling the entire middle band
"composites" would be incorrect.

Put Y=floor(X/2), L(Z)=sum_{n<=Z, P+(n)<R}mu(n), and
D(Z)=sum_{R<=p<=Z, p prime}M(floor(Z/p)). For Z=Y or X, sqrt(Z)<R
ensures M(Z)=L(Z)-D(Z). The ordered six-site/factor cells are

    c0=M(R-1),
    c1=L(Y)-M(R-1),
    c2=-D(Y),
    c3=L(X)-L(Y),
    c4=-D(X)+D(Y)+[pi(X)-pi(Y)],
    c5=-[pi(X)-pi(Y)].

Their sum is M(X), and their column sums recover precisely the
three admitted prime-factor strata. The six cell values are
recomputed from genuine Mobius and actual prime counts in the C++ test.

If c_j(R) is the true cell mass and g_j(R)=c_j(R+1)-c_j(R), then

    delta_R=sum_{j=0}^5 g_j(R),

    sum_{H<=R<2H} delta_R^2
        =sum_j sum_R g_j(R)^2
         +2 sum_{j<k} sum_R g_j(R)g_k(R).

**The total energy is invariant under deterministic regrouping.**
In particular, a larger negative cross term or cancellation percentage
under a finer partition does NOT independently prove any mixing theorem.

The **correct independent-random-sign reference** holds the set of actual
squarefree sites fixed, but hypothetically assigns independent Rademacher
signs to those sites. For each shell let d_R=sum_{n in I_R}mu(n)^2.
Under this reference model, and only under this model,

    E_rand[sum_R delta_R^2] = D(H)=sum_R d_R,
    Var_rand(sum_R delta_R^2) = 2 sum_R d_R(d_R-1).

No assertion that genuine Mobius signs satisfy this distribution is made.

Independently sieved arithmetic (separate C++ implementation through
67,125,248) yielded the following exact energies. The extra crossed-site
diagnostic was integrated into the existing genuine-prime sieve script.

| H | actual sum delta^2 | squarefree random E | ratio | site 3-band diagonal | prime 3-band diagonal | crossed 6-cell diagonal |
|---:|---:|---:|---:|---:|---:|---:|
| 256 | 110,216 | 119,516 | 0.922 | 292,210 | 658,834 | 756,100 |
| 1024 | 1,723,387 | 1,912,373 | 0.901 | 4,722,701 | 25,761,943 | 26,570,093 |
| 4096 | 30,291,950 | 30,598,026 | 0.990 | 80,367,974 | 1,118,176,570 | 1,089,567,934 |

At H=4096, the corresponding signed cross sums (each equals actual energy
minus the relevant diagonal) are:

    site cross   =      -50,076,024,
    prime cross  =   -1,087,884,620,
    six-cell cross = -1,059,275,984.

The six-cell cross between the upper-integer-site middle-largest-prime
and upper-integer-site top-prime populations alone is -1,006,683,890.
This is a **large, coherent arithmetic response**, not an assertion
that these two channels are independent random variables.

The normalized actual square-block increments z_R=delta_R/sqrt(d_R)
in the H=4096 held-out range have measured mean 0.00011, RMS 0.99397,
lag-1 product mean 0.01115, and 173 of 4096 increments exceed 2
standardized units (8 exceed 3). Under the independent-sign reference,
the observed total energy is -0.445 reference standard deviations from
its expectation. These finite observations support **random-like
variance**, not a proven random-process law.

### Rigorous small-modulus sampling lemma, and its limit

Let N_R(d) be the actual number of multiples of fixed d in
[R^2,(R+1)^2) and e_R(d)=N_R(d)-(2R+1)/d. The elementary floor identity is

    e_R(d)=frac((R^2-1)/d)-frac(((R+1)^2-1)/d).

For any coprime positive d,e, e_R(d) and e_R(e) are periodic in R
modulo d and e respectively, and each separately sums to 0 over a
full period. The CRT therefore gives the *exact* finite identity

    sum_{R=1}^{de} e_R(d)e_R(e)=0.

As |e_R(d)e_R(e)|<=1, splitting any H consecutive sampled roots into
complete periods of length de and a remainder gives

    |(1/H)sum_{R=H}^{2H-1}e_R(d)e_R(e)| <= de/H.

This IS a rigorously deterministic, polynomial decorrelation estimate
for fixed coprime channels with de << H. It is NOT a proof that all
square-block Mobius divisor channels decorrelate: high moduli with
de>=H, shared prime factors, moving filters and the total cofactor
weights remain outside this CRT estimate.

**Current verdict:** the nested partitions expose exceptionally strong,
source-faithful signed compensation and the final sampled second moment
closely matches the independent-sign reference at H=4096; neither
phenomenon alone proves that the moving partitions supply a *uniform*
random-process concentration theorem. The independent arithmetic gate
remains a full-coupled dyadic bound

    sum_{R=H}^{2H-1} delta_R^2 <= C_epsilon H^(5/2-eta+epsilon), eta>0.

No exponent improvement or RH result is asserted by this addendum.


### Important adversarial qualification

The first-moment divisor discrepancy identity above is a consequence of
consecutive interval boundaries: it would telescope for ANY nested
partition of an integer interval. It proves exact first-order unbiasedness,
but **not a square-specific mixing or independence phenomenon**.

The genuinely new square-specific task lies at SECOND order:
joint residues of R^2 modulo several prime-factor products, the physical
gcd-dependent correlations, and the full moving-site x prime-owner signed
nine-channel matrix. None of their entries is automatically zero simply
because a physical site-by-owner cell is empty at one endpoint.
