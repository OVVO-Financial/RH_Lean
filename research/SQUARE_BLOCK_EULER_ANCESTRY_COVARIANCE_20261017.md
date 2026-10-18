# Fixed Euler wheel, square blocks, and complete Mobius covariance

Date: 2026-10-17 (America/New_York). Implementation PR #974.
Status: EXACT FINITE IDENTITIES / SUPPORT THEOREMS only; NOT an RH proof.

## 1. Existing compiled sources (do not duplicate)

- RHLean/Arithmetic/SignedBuchstabRecursion.lean: genuine Mobius
  fresh-prime sign reversal and exact signed Buchstab recurrence.
- RHLean/Arithmetic/PrimeWheelMobiusRecovery.lean: arbitrary-depth
  squarefree signs and at-most-one prime outside a root-covering wheel.
- RHLean/Proof/CanonicalGapAncestryHighRealization.lean: all integers
  in a canonical square block share an exact integer square root.
- RHLean/Proof/SquareBlockSmoothTransportGram.lean: actual signed
  square-block increment = smooth increment - large-prime transport.
- RHLean/Analysis/MathlibMertensHook.lean and
  RHLean/Analysis/DeterministicTGreenKuboComparison.lean: actual
  squarefree diagonal, uncentered signed all-pair sum, and
  Mertens-square identity.
- research/MERTENS_CONVERSE_IDENTIFICATION.lean: already established
  Mertens power envelope iff zeta zero strip; the converse
  imports no new unconditional power bound.

The new Lean file research/SQUARE_BLOCK_EULER_ANCESTRY_COVARIANCE_20261017.lean
adds precise interfaces and the full ancestry tensor, reusing these authorities.

## 2. Uniform square-root factor set and exact low wheel

For **the canonical half-open block**

    I_R = {n : R^2 <= n < (R+1)^2}, R>=2,

all numbers satisfy floor(sqrt n) = R. The included lower endpoint
n=R^2 has zero Mobius value and is harmless. The upper endpoint
(R+1)^2 is EXCLUDED, which is essential.

Let P_R = product of the primes at most R. For every n in I_R:

    1_{n prime}
       = 1_{gcd(n,P_R)=1}
       = sum_{d | P_R, d | n} mu(d).

Because any composite n below (R+1)^2 has a prime factor at most R,
every low-wheel survivor inside the block is an actual prime. This is
an exact finite identity, not the density version of Euler's product.

An n in I_R has at most one *distinct* prime factor p>R; whenever p|n,

    n = p*c,      1 <= c <= R.

For p prime and c<=R positive, p does not divide c, hence

    mu(p*c) = -mu(c).

The cofactor c is not limited to primes or semiprimes. It may have
arbitrary allowed small-prime depth, and squareful c simply has mu(c)=0.

This is the concrete truncation geometry underlying the genuine
smooth-minus-transport coordinate already proved in RH_Lean.

## 3. Exact Mobius densities and the NOT-Pearson covariance

Define

    A(x) = #{n<=x: mu(n)=+1}
    B(x) = #{n<=x: mu(n)=-1}
    D(x) = A(x)+B(x)
    M(x) = A(x)-B(x)
    C(x) = sum_{1<=m<n<=x} mu(m)*mu(n).

These quantities are all exact finite integers. In particular,

    M(x)^2 = D(x) + 2*C(x)
    C(x)>0 iff (A(x)-B(x))^2 > A(x)+B(x).

C is an UNcentered signed product sum, not statistical Pearson covariance
nor the separately masked native original-owner #915 NNS statistic.

Asymptotic equal densities A/x, B/x -> 3/pi^2 imply only M(x)=o(x).
They do not bound |M(x)| by a square-root power. A Hurst-size excursion
of c*sqrt(x) causes only c/sqrt(x) density *difference*, which still
goes to zero. Thus equal limiting densities and positive total C(x)
are logically compatible.

The exact one-sided equivalent form at any real ceiling T is

    C(x) <= (T-D(x))/2 iff |M(x)|^2 <= T.

It is an algebraic change of variables, not a theorem supplying T.

## 4. Genuine prime ancestry A_(k,l,j), including all factor depths

Only nonzero squarefree pairs m<n<=x are counted. For each pair define

    k = omega(m) = # distinct prime factors of m
    l = omega(n)
    j = omega(gcd(m,n)).

The integer 1 is included with factor depth **zero**.
Let A_(k,l,j)(x) count exactly these unordered pairs. The already
compiled squarefree Mobius parity lemma proves in the new module:

    C(x) = sum_{k,l,j} (-1)^(k+l) A_(k,l,j)(x).

The tensor index image is finite, so this is a rigorous **all-depth**
partition: no truncation at triples, semiprimes, or a fixed number of
shared primes. The sign is also (-1)^(k+l-2j): the 2j shared prime
factors cancel. Shared-gcd depth nonetheless changes the incidence
and frequency of each factor-depth configuration.

This tensor is *not* a proof that j=1 has negative sign universally.
The finite x=100 counterexample to blanket negative j=1 contribution
is a required falsifier.

## 5. Complete exact 317/1027 regressions

The companion scripts/square_block_euler_ancestry_20261017.py independently
computes an integer smallest-prime-factor sieve, the full genuine
mu sequence, ALL unordered squarefree pairs, exact A_(k,l,j) entries,
each exact gcd, pair-sign parity, full and partial square-block owner
splits, and Euler inclusion-exclusion from the same wheel through R.

| cutoff x | A(+) | B(-) | D | M | C |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 317 | 95 | 99 | 194 | -4 | -89 |
| 1027 | 311 | 314 | 625 | -3 | -308 |

| shared prime depth j | 317 signed | 1027 signed |
| ---: | ---: | ---: |
| 0 (coprime) | +26 | +323 |
| 1 | -176 | -926 |
| 2 | +65 | +300 |
| 3 | -4 | -5 |
| **all pairs** | **-89** | **-308** |

| root R | full block signed smooth | full high-prime signed | full delta | partial ending at x |
| ---: | ---: | ---: | ---: | ---: |
| 17 | 0 | +4 | +4 | +3 (x=317) |
| 32 | -3 | -1 | -4 | +1 (x=1027) |

At n=317 a new actual prime contributes -1 to M but +3 to the
complete C by the exact increment formula
C(x)-C(x-1) = mu(x)*M(x-1); prime admission does **not** imply
a monotone decrease of covariance.

The wheel regressions enumerate *every* integer in the half-open
blocks, including squareful sites, and verify the finite divisor sum
equals the actual prime indicator.

## 6. Target and noncircular proof boundary

The genuine arithmetic hypothesis still missing is

    for every epsilon>0, exists K_epsilon:
    C(x) <= K_epsilon * x^(1+epsilon), for all x>=2.

This is RH-equivalent after applying the existing exact identity and
the already compiled Mertens/Zeta converse. **We do not assert it.**

For an independent first improvement of the 7/8 benchmark one may
seek an original-factor, all-scale exponent <7/4 for the one-sided
complete signed covariance, preferably through nonlocal cross-block
cofactor cancellation. An upper bound on every full block increment
or an absolute sum of missing counterpart sites is neither automatic
nor required by the target.

The statement "unmatched cofactor contribution is O(x^(1/2+eps))"
must be given an exact finite carrier, complete original sign,
weight, occurrence, boundary restoration, and proof of the bound.
Reindexing signed cofactor counts or applying an unrestricted Euler
product does NOT prove it. A square block fixes admissible small
primes but does **not** contain a complete primorial wheel period;
the wheel modulus can vastly exceed block length 2R+1.

No zeta zeros, RH premise, heuristic independence, Hurst oscillation
bound, or outside OpenAI 7/8 result is used as an assumption in these
new finite arithmetic theorem statements.

## 7. Explicit next theorem to attempt

Prove a **nontrivial signed estimate** for the cofactor response with
all high-prime owners included, controlling both within-block and
across-block interactions. The exact negative contribution from
j=1 and its cancellation against j=0,2,3 must be quantified in terms
of independent prime-factor incidence bounds, *not* inferred from
two observed tables. Audit whether a proposed bound is target-equivalent
and simply assumes the answer.

Acceptance = warning-fatal Lean compile with no sorry/admit/new axioms,
specific example regressions, and an honest OPEN quantitative seam.
Merging remains human-controlled.
