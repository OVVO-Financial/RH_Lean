# Signed finite extension: Heath-Brown, hyperbola, and the remaining norm

Baseline: main df353c9d40c660cc247bd2fdb96c536c74b04fe3, including merged #951.
This follows the user's proposed sign-preserving attack. The canonical VF goal
and original Mertens definitions are unchanged. No new global exponent bound
is asserted. Compilation status belongs to the PR's actual CI records.

## Exact higher-order identity

Write delta for the Dirichlet convolution unit and 1vec for the function equal
to one on positive integers. Put D=delta-a*1vec. Define

H_0(a)=0; H_(k+1)(a)=a+D*H_k(a).

Then H_k=a*(delta+D+...+D^(k-1)), and

mu-H_k=mu*D^k; delta-H_k*1vec=D^k.

In binomial coordinates this is

H_k=sum_(j=1)^k (-1)^(j-1) choose(k,j) a^j * 1vec^(j-1).

The Lean module proves the geometric identity for every k, plus the explicit
binomial formulas at k=2,3,4. At k=2, H_2 is precisely the previous Newton map.
If a agrees with genuine mu below B, D vanishes below B, D^k below B^k, and
H_k agrees with mu below B^k. This is exact arithmetic, not a summatory norm
contraction. In particular D*D vanishes below B^2 because no product of two
nonzero support indices fits there: no positive/negative cancellation is
needed for that support statement.

The user's delta=1-(1-mu*1vec)^2 notation obscures two different units and,
with the full mu, reduces to a tautology. The useful identity uses the finite
prefix a and keeps the remainder mu*D^k explicitly.

This is established Heath-Brown/Vaughan-type algebra, not a novelty claim.
Huxley and Watt, arXiv:1807.05890, equations (1.5),(1.6),(1.10), discuss these
short-Mobius identities and their spectral/analytic estimation difficulty.

## Signed hyperbola

For UV<=X<(U+1)(V+1), the product region ij<=X is covered by i<=U or j<=V.
Its overlap is the complete rectangle i<=U,j<=V. The signed identity is

sum_(ij<=X) f(i)g(j)
 = sum_(i<=U) f(i)G(floor(X/i))
 + sum_(j<=V) g(j)F(floor(X/j)) - F(U)G(V).

The Lean split preserves every pair and sign. Its left/right strips are defined
as filtered pair sets. The module also proves the explicit reindexing from
Dirichlet convolution coefficients to that physical finite hyperbola.
No bound on the two growing strips is assumed or derived merely by rewriting.

## Exact numerical test

At N=1000 and X=N^2, let Q=sum_(i,j<=N) mu(i)mu(j)floor(X/(ij)).
Direct signed evaluation gives Q=-208 and M(X)=2*M(N)-Q=212.

- Termwise absolute coefficient budget: 27,299,564.
- Preserve every inner row sum, then take outer absolute values: 23,240.
- Preserve both signs through the whole bilinear form: absolute value 208.

Thus row grouping reveals substantial cancellation but still discards another
factor 111.7 at this cutoff. This is a finite diagnostic, not a lower bound on
all possible bilinear methods or an asymptotic growth assertion.

Higher-order cancellation can occur ACROSS the combinatorial components:
with only mu(1)..mu(100), the cubic identity at X=10^6 is

3 - 2877 + 3086 = 212.

Bounding these three already-summed pieces separately costs 5966. With N=30,
k=4, X=810000, the four components are -12,-4512,+8900,-4437, summing to -61.
Independent direct sieve values agree. All integer sums are exact; displayed
square roots and ratios are numerical diagnostics only.

## Why Halasz is not a ready-made defect bound

For a nonempty prefix, D(1)=0, while D(p)=-1 at every prime p>N. This is not
a nonzero multiplicative function of the kind required by Halasz. Also the
truncated prefix itself is generally not multiplicative: a_3(2)a_3(3)=1 but
a_3(6)=0. An application to an auxiliary multiplicative function would need
an exact bridge to this nonmultiplicative defect. An application to mu itself
still needs a quantitative bound strong enough for the desired exponent.
Known prime signs do not automatically supply that bound.

Two fresh prime factors reinforce: D(p)D(q)=+1, proved in Lean. For N=10,
the directly computed defect square has (D*D)(121)=1 and (D*D)(143)=2.
This is not a disproof of global signed cancellation; it prevents claiming
that convolution squaring is intrinsically sign-cancelling.

## Current quantitative frontier

A uniform estimate on Q_N(X), in the relevant square-scale range, strong
enough to yield E_(j+1)<=K E_j is UNPROVED. Prefix scalar bounds do not by
algebra alone control all moving weighted inner sums and their cross terms.
A valid Type I/II argument must specify the ranges, the kernel, every diagonal,
off-diagonal and overlap term, its uniform constants, and the final power.
No finite computation or conditional named preservation predicate is treated
as the missing proof. The existing finite-A/C amplification consumers are
relevant but their input estimates remain open.

The next focused estimate should retain the signed row vector or the complete
higher-order signed component vector until its cross terms are accounted for.
An absolute residual norm is only one failed choice; well-placed absolute
values or Cauchy-Schwarz AFTER justified cancellation are not forbidden.

Sources: https://arxiv.org/abs/1807.05890 ;
https://arxiv.org/abs/1706.03755 ; https://arxiv.org/abs/1706.03749 .
