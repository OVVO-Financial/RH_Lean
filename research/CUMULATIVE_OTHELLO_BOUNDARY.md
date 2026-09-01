# Cumulative Othello boundary of a prefix carrier

**Status: OPEN, exact layer formalized, quantitative target predeclared and one
peel family already ruled out.**

## The change of scale

The site-level Othello laws describe one move. A first-power hit of a selected
prime reverses the sign of a site; a square hit kills it. Applied term by term
they describe the distribution of individual Moebius values, which is not what
`M(x)` asks about. `M(x)` asks whether an entire ordered prefix retains a
coherent imbalance, and a term-by-term estimate destroys exactly that
information the moment an absolute value is taken.

This route plays the same two laws on the whole region at once.

## 1. The exact object it changes

The carrier of the involution, not the involution.

Fix a prime `p` and define the carrier toggle on all of `N`:

```text
tau_p(n) = n * p    if p does not divide n
           n / p    if p divides n but p^2 does not
           n        if p^2 divides n.
```

`RHLean/Proof/GlobalPrefixCarrierOthello.lean` proves that this is an
involution of `N`, that its frozen states are exactly the `p^2` hits, and that
away from those states `mu(tau_p n) = -mu n`. Feeding that into the finite
matching principle of `RHLean/Proof/FiniteOthelloMatching.lean` gives, for an
**arbitrary** finite region `S`,

```text
sum over S of mu  =  sum over { n in S : tau_p n not in S } of mu.
```

This is an equality, not an estimate. The interior of `S` contributes exactly
zero however long the alternating paths inside it are, so the path length
between a birth and its capture never enters the accounting.

Three consequences are formalized:

* a region closed under `tau_p` has signed mass exactly `0`, so a Mertens value
  is exactly minus the mass of the collar that completes its prefix to a closed
  region (`sum_moebius_eq_neg_sdiff_of_toggleClosed`);
* on the cumulative prefix carrier `(L, x]` the boundary is exactly two walls
  (`RHLean/Proof/PrefixCarrierOthelloWalls.lean`):

  ```text
  anchor wall  = { n in (L,x] : p | n, p^2 does not divide n, n <= p*L }
  cutoff wall  = { n in (L,x] : p does not divide n, x < n*p }
  ```

* the peel iterates over a list of primes with the mass still exactly preserved
  (`sum_moebius_eq_sum_iteratedPrimeEscapePart`).

`RHLean/Analysis/PrimeWheelRunOthelloBoundary.lean` transports all of this to
the two cumulative coordinates the project already uses. The pinned
primorial-wheel residual `R_k(x)` is the anchor wall plus the cutoff wall of
`(L_k, x]`; a whole consecutive run of complete square blocks, treated as one
space-time carrier `(X_{a-1}, X_b]` rather than as a sum of block statements, is
the anchor wall on its initial temporal endpoint plus the cutoff wall on its
terminal one. The number of blocks in the run never appears.

## 2. Why this is not the closed dyadic Li-residual route

The closed route paired a cofactor `c` with its doubled child `2c` inside fixed
active-prime intervals and then asked an aggregate Moebius-versus-random
statistic to finish the job. Steps 4 and 5 of that route failed.

This route:

* pairs nothing cofactor-wise and fixes no active-prime interval; the pairing is
  a global involution of `N` restricted to a region;
* makes no cancellation claim at all. The conclusion is a **support reduction**:
  the same signed mass, carried by a smaller set;
* is closed as an exact identity in Lean before any quantitative question is
  asked, so there is no aggregate statistic to be optimistic about.

## 3. Predeclared continue / stop criterion

The open target is the multiplicity of the boundary, not of individual Moebius
seats:

```text
IteratedPrefixBoundaryBoundedStatement  ->  MertensEnergyBoundedStatement
```

is proved in `RHLean/Analysis/PrimeWheelRunOthelloBoundary.lean`. The premise
asks that for every `x` **some** finite peel leaves a boundary of population
`x^(1/2+eps)`.

**Stop criterion for a peel family:** if the boundary population stays a fixed
positive proportion of `x` as more primes are peeled, that family is dead, since
no number of further peels can reach `x^(1/2+eps)`.

## 4. Result of the first predeclared test: the naive peel is dead

`scripts/CumulativeOthelloBoundary/peel_diagnostic.py` runs the naive increasing
peel `p = 2, 3, 5, 7, 11, 13, 17, 19` on the fixed carrier `(0, x]`.

```text
x=  20000   M(x)=26   sqrt(x)=141.4
    peel p=  2: |boundary|=5000   |boundary|/x=0.25000   mass=26
    peel p=  3: |boundary|=4445   |boundary|/x=0.22225   mass=26
    peel p=  5: |boundary|=4267   |boundary|/x=0.21335   mass=26
    peel p=  7: |boundary|=4180   |boundary|/x=0.20900   mass=26
    peel p= 11: |boundary|=4144   |boundary|/x=0.20720   mass=26
    peel p= 13: |boundary|=4120   |boundary|/x=0.20600   mass=26
    peel p= 17: |boundary|=4105   |boundary|/x=0.20525   mass=26
    peel p= 19: |boundary|=4093   |boundary|/x=0.20465   mass=26
```

Two readings.

* **The exact layer checks out.** The signed mass is invariant along the whole
  peel at every `x` tested, which is what
  `sum_moebius_eq_sum_iteratedPrimeEscapePart` asserts.
* **The naive peel family is closed.** The first peel is efficient, `x -> x/4`.
  Every later peel is nearly inert, because after the first peel the surviving
  carrier is a short window with no room left: for `q >= 3` the `q`-mate of
  almost every survivor is already outside the window, so it is already on the
  boundary. The ratio descends to `(1/4) * prod_{q>=3} (1 - 1/q^2) = 2/pi^2 =
  0.20264...`, a fixed proportion of `x`.

So the peel **order** is not the free parameter of this route.

## 5. Every boundary or unmatched term

At one prime, on `(L, x]`, the unmatched set is exactly the two walls above, and
nothing else; frozen `p^2` sites stay in the interior and carry no mass. Their
populations are proved in Lean:

```text
|anchor wall| <= L        (divide out the single p, inject into (0,L])
|cutoff wall| <= x - x/p  (inject into the window (x/p, x])
```

Both are honest and neither is a saving at one prime. They are the quantities
the open multiplicity theorem has to beat.

## 6. Type of each result

| Result | Type |
| --- | --- |
| carrier toggle is a sign-reversing involution with `p^2` fixed points | exact identity (Lean) |
| region mass = boundary mass, any finite region | exact identity (Lean) |
| toggle-closed region has mass `0`; prefix mass = minus collar mass | exact identity (Lean) |
| prefix boundary = anchor wall + cutoff wall | exact identity (Lean) |
| wheel residual and whole square run in the same form | exact identity (Lean) |
| single-prime wall population bounds | exact bound (Lean), not a saving |
| `IteratedPrefixBoundaryBoundedStatement -> MertensEnergyBoundedStatement` | sufficient criterion (Lean) |
| an RH-scale peel exists | open analytic premise |
| naive increasing peel on a fixed carrier | closed by finite diagnostic |

## What to try next, and what not to

The remaining degree of freedom is the **carrier**, not the peel order. The
completion form

```text
sum over T of mu = - sum over (S \ T) of mu     whenever T subset S and S is tau_p-closed
```

holds for any finite `S`, and the master identity holds for any finite region at
all, so nothing in the formalization forces the carrier to be an interval.

Do not restart this route by:

* rerunning the naive peel at larger `x`, or with more primes, or in a different
  prime order. The limiting proportion `2/pi^2` is structural, not a range
  effect;
* reporting the first peel `x -> x/4` as progress. One bounded factor is not a
  power saving;
* replacing the boundary population by a signed statistic and claiming
  cancellation on the wall. That is the closed dyadic Li mechanism wearing new
  coordinates. The boundary walls are ordinary short-interval Moebius sums with
  a coprimality condition, and treating them as such is the whole difficulty;
* claiming the identity says anything asymptotic on its own. It moves the mass;
  it does not shrink it.
