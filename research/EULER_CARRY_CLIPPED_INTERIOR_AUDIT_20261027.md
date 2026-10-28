# Clipped Euler carry levels and genuinely sparse interior jumps

Date: 2026-10-27. Stacked on #1037 (and #1036). 
No finite C, RH, or fixed positive eta is claimed.

## Genuine historical data

Write N=R-1, L=R+1, X=NL. For 1<=q<=N and 1<=b<=N:

- ell=floor(N/(q+1)), r=floor(N/q), I_q=(ell,r].
- Y=floor(X/b), m=floor(Lq/b), rho=(Lq) mod b.
- c(a)=floor(Y/a)-m, for a in I_q.
- K=c(ell+1) if ell<r, otherwise K=0 (**empty bucket guard**).
- c_right=c(r), for nonempty buckets.

All the exact identities from #1037 use the genuine Möbius weights.

## 1. Full-bucket clipped levels

For 1<=k<=c_right, k<=c(r) means r<=floor(Y/(m+k)).
So min(r,floor(Y/(m+k)))=r, and the entire kth historical
Mertens level is

    M(r)-M(ell).

For c_right<k<=K, the threshold v_k=floor(Y/(m+k)) satisfies

    ell < v_k < r

and therefore the *same* kth term is the strict-interior increment

    M(v_k)-M(ell)

with NO clipping. If q|N, the actual right endpoint r=N/q
divides N and c_right=0 exactly.

Thus the full original signed carry bucket has the exact decomposition

    sum_(a in I_q) mu(a)*c(a)
      = c_right * [M(r)-M(ell)]
        + sum_(k=c_right+1)^K [M(v_k)-M(ell)].

This identity uses the **actual** c_right and empty-bucket guard,
not a hypothetically positive independent coefficient.

The endpoint phase in the complete unpaid bulk is

    -rho/b * DeltaM_q^o,
    DeltaM_q^o = M(r)-M(ell)-1_(q|N)mu(N/q).

If q|N the clipped count vanishes, so c_right*[M(r)-M(ell)]
equals c_right*DeltaM_q^o in all cases. Consequently the entire
bucket is exactly

    T_R(r,b) * DeltaM_q^o
      + sum_(k=c_right+1)^K [M(v_k)-M(ell)]

where T_R(r,b)=c_right-rho/b. In this identity the first component
is the **endpoint carrier**, not an independently bounded source.
The second contains strict interior historical jumps.

## 2. Universal 1/N reciprocal width

For every nonempty bucket and q>0:

    q*r <= N < (q+1)*(ell+1).

Multiplying the first inequality by ell+1, the second by r,
and subtracting proves the all-integer inequality

    N*r < (N+r)*(ell+1),

which is equivalent to

    0 <= 1/(ell+1)-1/r < 1/N.

Thus with Y<=NL/b, the number of strict positive interior
levels DeltaK=floor(Y/(ell+1))-floor(Y/r) obeys

    0 <= DeltaK <= floor(L/b)+1.

Note floor rounding is essential; the *upper bound* on DeltaK
does NOT by itself bound the original signed sum.

For ell>0, replacing k by j=m+k in the strict levels gives
j in (floor(Y/r), floor(Y/(ell+1))].
For j up to floor(Y/ell), M(floor(Y/j))-M(ell)=0, so the
upper limit may be extended without altering the sum:

    strict_sum = sum_(j=floor(Y/r)+1)^(floor(Y/ell))
                      [M(floor(Y/j))-M(ell)].

Because ell_q=r_(q+1), these j-intervals are disjoint and
adjacent across q=1,...,N-1, including zero-valued extensions.
**Do not include q=N** in the extended formula: ell_N=0 and
division by ell_N is undefined in the intended mathematics.

## 3. Only large historical quotient buckets carry strict jumps

If N<=q(q+1), then r<=ell+1; all nonempty such buckets
are singletons {r}, have K=c_right, and have NO strict interior jumps.

Therefore a strict interior jump implies

    q(q+1)<N,

and hence q<sqrt(N). This is a bound on the number of
**potentially active quotient buckets**, not on the total signed mass.
All singleton endpoint-phase terms (potentially many) remain.

For q<sqrt N, r>N/q-1>=sqrt N-1. At the right endpoint
N=q*r+t with 0<=t<q. Then

    c_right=floor([rho+L*t/r]/b).

If b*r>L*t, then L*t/r<b and c_right in {0,1};
it equals 1 exactly when r*rho+L*t>=r*b.
A convenient sufficient condition is b*r>=L*q.
This isolates an exact congruence wrap event in the
big-bucket endpoint phase; it is NOT an automatic smallness
estimate for the whole endpoint carrier.

## 4. Source-faithful status

The integer bucket width, clipped threshold, strict jump clipping,
singleton sparsity and divisor right-endpoint zero are written in
`research/EULER_CARRY_CLIPPED_INTERIOR_20261027.lean`.
Lean compilation status is reported separately by the dedicated
warning-fatal workflow.

The historical functional in #1037 was already certified.
The new clipped-to-interior and m-interval reindexing preserve all
original mu signs; no outside zero-free theorem is used.

Open signed estimate: control the **complete signed q,b sum** of
endpoints plus strict interior Mertens increments, retaining their
correlation with the residue phase. No fixed eta follows by counting
active quotient buckets alone.

Accept only Lean 4.34.1 warning-fatal compilation and the
standard-axioms/sorry-free audits.
