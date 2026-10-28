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
