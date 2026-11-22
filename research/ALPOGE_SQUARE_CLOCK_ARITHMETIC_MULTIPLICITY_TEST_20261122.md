# Alpoge x RH_Lean: can R square-clock differences replace geometric multiplicity?

**22 November 2026.** Independent arithmetic hypothesis test. This is NOT
a new proof of RH or an assertion that Alpoge's theta multiplicity follows
from ordinary differences.

## Source and target: do not conflate dimensions

The exact upstream source in
CocoSgt/riemann-hypothesis-lean,
src/Formalism/SizeWindowBrackets/SChain.lean, defines

    RestSize(eps,x,n,nT,nT2,m,b,k,aE)
    ...
    x^(1/2-eps) <= m
    k <= n^2 * x^(1/2-eps).

Its CostWindows simultaneously enforces

    2*f*(x+1)*theta <= 1/x
    6*f*(x+1)*(eta+1) <= b/x.

Thus m is a *geometrically certified integer chain length*, which
must coexist with size, lattice and width cost conditions. It is
NOT defined as the square index R or as the number of prime factors.

For X_R=R^2-1, R is indeed the right scale, but an order-R discrete
difference is only an algebraic candidate.

## 1. New literal native square-clock arithmetic jet

Let Delta f(n)=f(n+1)-f(n), and define J_R(f)=Delta^R f(X_R).
These are actual integer-clock differences on a root-length set of
R+1 sites: the old endpoint X_R followed by R sites in the next square interval.

The new Lean module
RHLean/Analysis/AlpogeSquareRootArithmeticMultiplicity.lean
proves the following *finite* identities and inequalities,
subject to successful hosted CI on the exact PR head:

- Delta^(k+1)f = Delta^k(Delta f), with integer floor clock intact.
- Delta^k(1)=0 for k>=1; Delta^k(n)=0 for k>=2.
- E(n)=psi(n)-n gives Delta E(n)=Lambda(n+1)-1.
- Delta^2 E(n)=Lambda(n+2)-Lambda(n+1).
- For every k>=2, Delta^k E(n)=Delta^(k-1)(Lambda(n+1)).
- If |f(n)|<=M for all n, then |Delta^k f(n)|<=2^k M.
- Equality of this operator norm is achieved by the explicit
  *bounded integral* alternating sequence f(n)=(-1)^n:
  |Delta^k f(n)|=2^k for every n.
- One original Boolean prime coordinate already fails the proposed
  "derivative means p-divisibility" principle:
  D_{ {7} }(n)(7)=7-floor(7/7)=6, not divisible by 7.

In particular, **exact order R is obtainable, but its universal
height budget is exponentially large 2^R**, not the polynomial
(or x^o(1)-normalized) budget needed for a short RH argument.
This worst-case operator test does NOT prove the actual Lambda
source attains the worst case.

Dividing by 2^R would fix the norm but create a denominator of
size 2^R in the integer lattice; that is a REAL height/covolume
payment, not a free change of coordinates. The full triangular
Newton difference transform has diagonal 1 (unimodular); it cannot
by itself provide the nontrivial lattice index/multiplicity that
the geometry supplies.

## 2. An exactly new source-identical difference / character correction

The original finite Möbius wheel offers

    D_p f(n)=f(n)-f(floor(n/p)).

For ANY commutative coefficient algebra and integer n,p,

    D_p(c*f)(n) =
      c(n)*D_p f(n)
        + [c(n)-c(floor(n/p))]*f(floor(n/p)).       (C)

The new native theorem
alpogeNativeFreshPrime_product_commutator
proves this EXACT Leibniz defect.

More importantly,
alpogeNativeLiteralASK_freshPrime_characterDefect
instantiates (C) to the **ACTUAL original Alpoge coefficients**

    c(n) = alpogeNativeColourKernel(inertia,frob,n,g)
    f(n) = Lambda(n)*alpogeNativeSiteCut(a,w,t,n,g).

The true Frobenius/inertia, full original site-dependent partner width,
ramified prime powers, full complex phases and the exact quotient n/p
all appear in the SAME theorem. No independent-character simplification
or termwise absolute-value replacement occurs.

This identifies a precise arithmetic *cocycle-like defect* obstructing
a naive statement that prime-wheel derivative and original theta
character selection commute. A fully geometric substitute could attempt
to pay the whole SIGNED sum of these defects over actual n, colours,
sites, scales and the original thick window. The algebraic identity
is proved, but a required global POWER SAVING is not.

## 3. Exact physical prime-power experiment, not a model

For R>=2, the exact identity above gives the finite prime-power sum

    J_R(E)=sum_{j=0}^{R-1} (-1)^(R-1-j)*C(R-1,j)
                   * Lambda(R^2+j).                 (P)

A reproducible audit script works with **integer coefficients of
logarithms of distinct prime bases**. The zero test is exact:
sum_p a_p log p=0 iff all integers a_p=0, by unique factorization.
No simulated random primes or floating zero threshold.

| R | X_R | positive-support prime powers in (P) | exact universal l1 coefficient budget | actual-support fraction of budget |
|---:|---:|---:|---:|---:|
| 2 | 3 | 2 | 2 | 1.0000 |
| 3 | 8 | 2 | 4 | 0.5000 |
| 16 | 255 | 5 | 32768 | 0.2001 |
| 32 | 1023 | 6 | 2147483648 | 0.1509 |
| 317 | 100488 | 28 | 2^316 | 0.0471 |
| 1027 | 1054728 | 64 | 2^1026 | 0.0882 |

At R=2 the actual jet is LOG(5)-LOG(2), nonzero. At R=3 it
is LOG(3)+LOG(11), nonzero. The symbolic certificates are exact.

The physical support saving is empirically meaningful, but at
R=1027 even 8.82% of an EXPONENTIAL coefficient budget is vastly
larger than the required x^(1/2+eps) goal. Cancellation of these
binomial phases on actual prime-power positions remains open.

**Important density separation:** the available global prime
count pi(R)~R/log R could in principle provide R^(1-o(1))
distinct *prime coordinates*. But (P) samples only R consecutive
integers near R^2. Global PNT cannot supply a uniform
R^(1-o(1)) prime count in EVERY such interval. Identifying the
two counts would assume a deep, unproved local prime-distribution
statement.

## 4. What actually survives this test

The earlier all-colour source-mass bound from stacked PR #1187
says the genuine inertia-coset colour coefficient sums to at
most two, independently of the large host size. It is a
VALID way to control a finite Fourier projection cost.

The new signed arithmetic commutator (C) is the proper FIRST
candidate for its missing partner:
- retain the exact quotient and all colour characters,
- sum over actual dyadic/root indices rather than separate norms,
- exploit the global positivity only AFTER reconstructing full
  original De,
- pay the number of genuinely independent lattice directions,
  determinant/index, rank and height WITHOUT replacing it by the
  mere count of fresh-prime differences.

A genuine independent RH theorem would follow if a
root-scale, all-family original-source signed commutator/covolume
bound were then proved and transported through the existing
native Gz square-clock interpolation to Alpoge's one-sided Landau
criterion. No such quantitative bound is asserted here.

## 5. Acceptance gates

1. Hosted Lean must build all declarations; static audit alone
   is insufficient.
2. Every theorem's axiom footprint must be printed before any
   assertion of an independently certified formal proof.
3. Check the actual parity, inertia and character base on the
   entire FULL source, not only the principal ASK collar.
4. Never infer m from |S|, from a unit determinant, or from
   Delta^R-polynomial annihilation alone.
5. A proposed replacement must improve the complete GLOBAL
   power budget, not merely the number of local terms.


### The quotient-column tax is exactly p, not one

The fresh-prime operator shifts by floor(n/p), not by a formal
first-order variable. The new Lean theorems
alpogeNativeFloorPrimeFiber_card and
alpogeNativeFloorPrimeFiber_div show for EVERY p>0 and m>=0:

    card {n : p*m <= n < p*(m+1)} = p,
    floor((p*m+r)/p) = m   for 0<=r<p.

Thus a single genuine source atom at quotient m is seen by precisely
p consecutive physical parent sites n under the floor dilation.
This is the exact **column multiplicity** in the algebraic
commutator. It can easily outweigh a multiplicity gain inferred from
counting the number of prime coordinates. Only a proved cancellation
over all p residues, with actual c(n) and original widths, could
make the global cost small.

This strengthens the conclusion: the open geometric supplier is
not merely "character Fourier covariance" but a **signed
quotient-column/character/covolume estimate**.


## 6. Direct mixed square-clock / prime-wheel test (ACTUAL Chebyshev input)

This is the most source-specific translation obtained in the attempt.
Write A f(n)=f(n+1)-f(n) and P_p f(n)=f(n)-f(floor(n/p)).
Both operators are exactly present in the native RH_Lean arithmetic,
but their commutator is NOT zero:

    A(P_p f)(n)-P_p(A f)(n)
       = f(floor(n/p)+1)-f(floor((n+1)/p)).          (M1)

The fresh-prime floor-fibre theorem makes this completely explicit.
For every p>=2, m>=0 and 0<=r<p-1, at n=p*m+r,

    floor(n/p)=floor((n+1)/p)=m,

so the mixed commutator is exactly

    A(P_p f)(p*m+r)-P_p(A f)(p*m+r)
       = f(m+1)-f(m).                              (M2)

When the ACTUAL original Chebyshev source f=E=psi-x is inserted,

    A(P_p E)(p*m+r)-P_p(A E)(p*m+r)
       = Lambda(m+1)-1.                            (M3)

M1-M3 are theorems in
RHLean/Analysis/AlpogeSquareRootArithmeticMultiplicity.lean,
with no RH hypothesis and no truncation of prime powers.

This is a precise mathematical reason why an R-indexed additive
difference cannot simply be interchanged with the Boolean prime
differences to mimic Alpoge's theta multiplicity. There is an
UNPAID arithmetic prime-power source on p-1 of every p residue
classes. Notice that the same original signed Lambda-1 impulse
also appears as the first derivative of E: it is NOT an unrelated
error term invented in the translation.

Combined with the previously proved physical colour commutator

    P_p(c*f) = c*P_p f + [c(n)-c(floor(n/p))]*f(floor(n/p)),

the next serious theorem must pay two interactions on the original
square lattice, at once:
(1) the additive/multiplicative **floor-boundary** commutator (M3),
and (2) the **Frobenius/inertia character** multiplier commutator.
Any global operator swap that assumes either vanishes is invalid.

The square-clock measure can be retained, and the exact correction
now has a uniform reusable statement. What remains unproved is
a strict quantitative signed saving on the COMPLETE accumulated
correction together with Alpoge's height/covolume data.


## 7. New POSITIVE outcome: signed R-by-R commutator telescope

The raw mixed commutator on one complete p-fibre is NOT
an arbitrary error. The exact crossing r=p-1 contributes 0;
every other residue contributes the SAME signed increment:

    C_p f(pm+r) = Delta f(m),    0<=r<p-1,
    C_p f(pm+p-1) = 0,

where C_p=(A P_p - P_p A) and
A f(n)=f(n+1)-f(n), P_p f(n)=f(n)-f(floor(n/p)).

Therefore the entire ORIGINAL arithmetic p-by-M lattice
TELESCOPES EXACTLY, for every f:

    sum_{m=0}^{M-1} sum_{r=0}^{p-1} C_p f(pm+r)
      = (p-1) sum_{m=0}^{M-1} (f(m+1)-f(m))
      = (p-1)[f(M)-f(0)].                          (T1)

The new root module attempts to kernel-certify the crossing,
full-fibre equality and global telescope as
alpogeNativeAdditiveWheel_crossing,
alpogeNativeAdditiveWheel_fiber_sum and
alpogeNativeAdditiveWheel_rectangular_telescope.

**Original Chebyshev source and square-root scale.**
For f=E=psi(n)-n, E(0)=0, choosing p=M=R gives a
literal R-by-R integer square lattice with EXACT signed output:

    sum_{m<R} sum_{r<R} C_R E(R*m+r)
       = (R-1)E(R).                                (T2)

This is the strongest genuinely positive SAME-SOURCE reduction
found by the test. It transforms a signed sum over R^2 integer
sites into the Chebyshev error at scale R, not scale R^2.
All prime powers remain inside E; no unsigned counting occurs.
It is an exact finite identity, not an RH-strength estimate.

Two mandatory cautions:
1. P_R is a floor-dilation operator for arbitrary R, but is a
   **fresh-prime Möbius operation only if R is prime**. The R-by-R
   specialization for composite R cannot be advertised as R
   legal fresh-prime steps in the Euler wheel. For genuine prime p,
   (T1) still holds; matching its endpoint to X_R requires a
   terminal partial quotient fibre, which cannot be silently erased.
2. The right side has multiplier R-1, not 1. Trivially bounding
   E(R) charges O(R^2) on the raw sum. Dividing by R-1 to obtain
   a root-scale *average* changes the original geometric
   normalization and needs a true multiplicity/covolume witness.
   T2 alone neither bounds E(R^2-1) nor Gz(R^2-1).

**Research implication:** the correct object to compare with
Alpoge's automorphic gain is a **normalized, signed
root-quotient telescope** of the *physical* ASK coefficient and
the complete Frobenius/inertia/partner commutator. The latter
may have a nontrivial terminal/boundary return that prevents
the same collapse. The exact Leibniz defect from the preceding
section is already defined, but proving the global full-family
geometry that pays it remains open.

The next noncircular task is therefore to show how the
telescoped source embeds into the actually constructed theta
lattice with controlled determinant, height and multiplicity,
without assuming the missing Gz or Chebyshev estimate.
