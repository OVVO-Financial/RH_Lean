# Alpöge/RH_Lean: genuine noncollapsed near-square-root error directions

2026-11-20. **New source-specific arithmetic construction; exact-head Lean CI pending. No RH or external automorphic cost bound claimed.**

## Why the original matrix lift was insufficient

The earlier 3R/4 <= p,q < R signed K2 face has a very favorable
normalized integer matrix 2I-J, but every carrier p*q satisfies
floor((R^2-1)/(p*q))=1. All directions therefore interrogate
the SAME error datum E(1)=-1; the centered matrix has rich coefficient
rank but no independent error evaluation sites. Its determinant or
formal 2-adic index is not the covolume saving in Alpöge's argument.

## A new full-physical-source family with distinct error arguments

Set X_R=R^2-1 and take actual primes in

   P_R={p prime : p>2, R/2 <= p <= 2R/3}.

For each p, retain the **actual** K2 carrier n=2p, not a symbol for a
character or a synthetic matrix entry. Native Selberg theory proves

   K2(2p) = 2 log(2) log(p)

and its signed error contribution is

   2 log(2) log(p) * E(t_p),
   t_p = floor(X_R/(2p)).

There is a PROVED ELEMENTARY INJECTION:

   p<q, X_R >= 2q^2
    => floor(X_R/(2q)) < floor(X_R/(2p)).

The size restriction 3q<=2R and R>=4 implies X_R>=2q^2,
so p↦t_p is strictly decreasing and injective on P_R.

A short elementary argument, avoiding smooth approximations:
let b=floor(X/(2q)). Then b>=q, since X>=2q^2. If p<q,
b*q >= b*(p+1) >= (b+1)*p. Hence

   (b+1)*2p <= b*2q <= X,

so floor(X/(2p))>=b+1. All variables are true integers.

The site map p↦2p is injective, too; therefore the finite source
reindexes exactly with no duplicate carriers or missed signs:

   sum_{n in {2p:p in P}} K2(n)*E(floor(X_R/n))
       = sum_{p in P} 2log2 logp *E(t_p).

The companion Lean file uses the EXISTING native K2 distinct-prime
kernel theorem and proves this strict quotient inequality plus exact
finite reindexing.

## Multiplicity and conditioning

By the classical prime number theorem,

   |P_R| ~ ((2/3)-(1/2))*R/log R = R/(6 log R)
          = X_R^(1/2-o(1)).

For the actual source response vector (E(t_p))_p, after removing the
known positive diagonal real weights log2 logp, the coefficient is
EXACTLY 2I_m: determinant 2^m, operator norm 2, inverse norm 1/2.
The logp weights lie in [log(R/2),log(2R/3)], so for R>=8
their ratio tends to one, making the REAL coefficient operator
well conditioned, too.

This is an actual improvement over the prior 2I-J family:
- no rank-one all-at-E(1) collapse;
- near-root multiplicity of distinct true error arguments;
- no forward cubic prefix tax;
- a nonunit integral coefficient factor 2 on each real response.

**CRITICAL:** The 2-adic determinant belongs to a normalized INTEGER
COEFFICIENT matrix. The actual K2 source has transcendental real
logarithmic factors, and the original Alpöge theorem concerns integral
Hecke/trace lattices and weighted geometric heights. A diagonal 2 does
NOT automatically give the required Hecke p-adic integrality,
character/automorphic witness, or a full-source Gz estimate.

## Actual finite census (deterministic; no random signs)

  R       selected prime owners    distinct t_p
  100               3                   3
  317              10                  10
  549              14                  14
  1027             27                  27
  3000             64                  64
  10000           190                 190
  30000           508                 508

Each t_p>=p, and at R=3000 the smallest successive t separation
in this band is 2. All actual prime values are from the Eratosthenes
sieve, not a probabilistic oracle.

## The remaining TRUE analytic/geometric task

Let U_R denote the complete signed Selberg source with selected
{2p:p in P_R} removed. The exact source identity from #1162
then reads (with this new selected set, once finite-set partition is
reindexed)

   E(X_R)*log^2 X_R = U_R +
     2 log2 sum_{p in P_R} logp E(t_p).

This is a genuine family of distinct error observations, but no
unconditional cancellation between those observations and U_R is proved.
One must obtain a same-family uniform quantitative estimate on the
COMPLETE expression and connect it to Alpöge's original
GrowthInequalityDataExists (or the exported EveryCharacter row
chain) with its H, character values, thick groups, k, Err,
archimedean heights, divisibility, covolume and movement/width costs.

The injectivity theorem is not a claim of **statistical independence**
or signed cancellation; those would be additional arithmetic theorems.
The user-requested exact translation proceeds via actual native
von Mangoldt coefficients and signed source, not by declaring mu a
multiplicative character.

## Build status

- research/ALPOGE_DISTINCT_K2_RESPONSE_TRANSLATION_20261120.lean:
  finite strict quotient theorem, prime-band injection, actual K2
  source coefficient, and exact selected-carrier reindexing.
- Must pass exact-head warning-as-error CI; until then its Lean
  claims are proposed, while the underlying elementary
  mathematics and numerical tests stand independently.

Related:
- PR #1160 for complete square/semiprime 2I-J face,
- PR #1162 for exact Alpöge Gz ↔ reciprocal Λ ↔ full signed
  Selberg source equation.
