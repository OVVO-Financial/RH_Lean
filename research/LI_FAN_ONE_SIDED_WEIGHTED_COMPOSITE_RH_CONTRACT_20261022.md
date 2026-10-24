# One-sided Li-fan containment via weighted square-block composite removal

**2026-10-22. Exact arithmetic plus an external established analytic theorem; NOT a proof of RH.**

## The substantially smaller arithmetic target

Daniel R. Johnston, *On the average value of pi(t)-li(t)*,
[arXiv:2201.06184](https://arxiv.org/abs/2201.06184), Theorem 1.1 proves

    RH  iff  integral_2^X (pi(t)-li(t)) dt < 0 for ALL real X>2.

Crucial: li(x) here means classical li(x) = li(2) + Li_2(x), with
li(2)=1.045163780... and Li_2(x)=integral_2^x dt/log t. In contrast
the repo's `vfMidLogarithmicIntegralFromTwo` is Li_2(x).
Replacing li by Li_2 inside Johnston's ALL-X statement is INVALID.

The present research yields a new simple, exact, DISCRETE sufficient
criterion and, with Johnston's quantitative proofs, an EQUIVALENT
eventual square-endpoint criterion.

Set, for integers n>=2:

    Q(n)  = floor(Li_2(n)),
    B(n)  = pi(n) - Q(n) - 1,
    eta(k)= 1_Prime(k) - (Q(k)-Q(k-1))  in {-1,0,1}  (k>=3).

The floor-Li first-difference `eta` is already certified in
`research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean`;
`Q((r+1)^2)-Q(r^2)` is already certified in
`research/VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean`.
The constant '-1' is only an INTEGRAL-STABILITY centering
of the original Li_2 floor and does not assert that
pi(x)=floor(Li_2(x))+1.

Define the twice-accumulated floor-Li prime population imbalance

    G(N) := sum_{n=2}^{N-1} B(n),    integer N>=3.

Since pi(2)=1 and Q(2)=0, B(2)=0. Two exact identities follow:

    G(N) = sum_{k=3}^{N-1} (N-k) eta(k).                   (T)

    G(N) = A(N) - T(N) - L(N),                             (W)

where

    m       := floor((N-2)/2),
    A(N)    := m*(N-m-2)
             = sum_{odd 3<=k<N} (N-k),                    ODD CANDIDATES
    T(N)    := sum_{odd composite 3<=k<N} (N-k),          COMPOSITE REMOVALS
    L(N)    := sum_{n=2}^{N-1} floor(Li_2(n)).            FLOOR-LI DEMAND

(T) is just triangular Fubini using the genuine {-1,0,1}
prime-vs-model arrivals.
(W) is the ORIGINAL S=A-T count with exact physical weights
N-k. Its proof counts p=2 separately:
    sum_{n=2}^{N-1} pi(n)
      = sum_{p<N prime}(N-p)
      = (N-2) + A(N)-T(N).
Subtract sum_{n=2}^{N-1} [Q(n)+1], and (N-2) cancels.
All A,T,L are FINITE integers. No Hecke character, independence
assumption, unproved covariance sign, or analytic continuation enters
these two arithmetic identities.

Thus:

    G(N) < 0  iff  T(N) > A(N)-L(N).                       (ONE WALL)

This is a *single one-sided LOWER bound on weighted composite
removals*, not a simultaneous upper AND lower prime count.
The model supplies the exact deterministic threshold A-L.

## Why the EVENTUAL square-endpoint sign is equivalent to RH

For t in [n,n+1), pi(t)=pi(n). Let

    H(X) := integral_2^X [pi(t)-li(t)] dt.

Since li(2)=c=1.04516... >1 and Q(n)<=Li_2(n)<Q(n)+1, for all
integer N>=3:

    H(N) <= G(N)
    and  0 <= G(N)-H(N) <= (c+1/log(2))*(N-2).             (E)

Indeed on each [n,n+1),
   (pi(n)-Q(n)-1) - (pi(n)-li(t))
      = li(t)-Q(n)-1
      = c-1+[Li_2(t)-Q(n)]
      belongs to [0, c+1/log(2)).
This is O(N), independently of actual primes.

Johnston's proof of RH => H(X)<0 supplies something strictly
stronger for sufficiently large X: see his Section 3 equations
(3.4)-(3.6),

    H(X) <= -kappa*X^(3/2)/log(X)     (all large X)

for some fixed kappa>0, because the leading negative
integral coefficient is 2/3 whereas the positive bound is 0.08.

By (E) this forces G(N)<0 for all sufficiently large N, hence
at N=R^2 for all sufficiently large integer R.

Conversely, if RH is false, Johnston's proof (Theorem 1.4 and
Lemma 2.8 with c=0) implies that for some delta>0,

    H(X) = Omega_+(X^(3/2+delta)).

That is, H(X) exceeds a positive constant times
X^(3/2+delta) for arbitrarily large real X. By (E)
G(floor X)>0 at nearby integers, since |H(X)-H(floor X)|
=O(X) on a unit interval. Choose the nearest square endpoint
R^2 to X. The difference |G(R^2)-G(floor X)| is O(X^(3/2)):
there are O(sqrt X) integer indices in this interval and
|B(n)|=O(X) holds trivially. Hence G(R^2)>0 infinitely often.
So a universal eventual negative square-endpoint G rules
out RH being false.

Therefore (using Johnston's external established analytic estimates):

    +-------------------------------------------------------+
    | RH  iff  EXISTS R0 : FOR ALL integers R>=R0,          |
    |          G(R^2) < 0.                                  |
    | RH  iff  EXISTS R0 : FOR ALL integers R>=R0,          |
    |          T(R^2) > A(R^2)-L(R^2).                      |
    +-------------------------------------------------------+

This is **not** the unjustified claim that the pointwise floor-Li
staircase equals genuine pi. Nor does it prove that the displayed
inequality actually holds. It identifies a VALID, smaller-looking
single-sided arithmetic proposition equivalent to RH.

## EXACT wheel ancestry across true square blocks

For interior sites r^2<k<(r+1)^2, all odd composites k have
least prime factor p with 3<=p<=r, and every prime survives
the entire wheel p<=r. This is already proved on main in
`research/VF_MID_SQUARE_WHEEL_BACKLOG.lean`.

For N=R^2 and r>=2 define the EXACT weighted least-prime owner bill

    C_r(N) := sum_{3<=p<=r, p prime}
                  sum_{r^2<k<(r+1)^2, odd, minFac(k)=p}(N-k).

Then the total odd-composite removal is

    T(R^2) = sum_{r=2}^{R-1} C_r(R^2)
           +sum_{3<=s<R, s odd}(R^2-s^2).                 (S)

The second sum consists of ODD SQUARE ENDPOINTS:
k=s^2 is composite, but its first owner can be p=s,
outside the previous interior wheel (p<=s-1).
These boundary terms MUST NOT be dropped.

The one-wall condition is now an explicit all-historical-owner
weighted LOWER bound:

    sum_{r=2}^{R-1} C_r(R^2)
    +sum_{3<=s<R,s odd}(R^2-s^2)
       > A(R^2)-L(R^2).                                  (TARGET)

The RHS is completely deterministic, built from a polynomial in R
and floor(Li_2(n)). The LHS is exactly genuine odd composite
ancestry, each occurrence counted once, with an early composite
carrying more weight (R^2-k).

This is a distinct attack: prove the WEIGHTED owner-population
lower bound directly by exact wheel/depth capacity, WITHOUT an
unknown favorable NNS covariance, an abstract generic Grammatical
energy lemma, or two separate prime-supply walls.

## Honest proof barrier

The conjectural inequality (TARGET) is itself RH-equivalent (given
Johnston's external theorem). FTA gives its owner partition but
DOES NOT supply the quantified weighted lower bound. Completing
CRT wheel periods does not control every truncated square block.
In particular `T>=0` or the density version of PNT is FAR too weak.

The actual research job is to prove the lower-bound TARGET from
the genuine *non-overlapping* least-owner fibres, including all
cross-block repetitions and square endpoints. Do not infer it by
assuming G<0, by using the very same RH-equivalent property as an
admissibility axiom, or by identifying floor-Li events with primes.

## Reproducibility

`scripts/li_fan_one_sided_weighted_owner_audit.py` counts real primes
using an independent Eratosthenes sieve and computes floor(Li_2(n))
with high-precision mpmath. The sample proves no all-R property;
it checks arithmetic identities (T),(W),(S) at finite integer
square endpoints, including odd-square owner terms.
