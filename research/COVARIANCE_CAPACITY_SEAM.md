# Covariance capacity: the two arrows

**Status: OPEN. Both arrows of the critical path are now named and the
composition is proved; neither arrow is proved. The support-only route is
measured to be a full power of `x` short.**

## The exact frame

With `C(x+1) = sum over 1 <= a < b <= x of mu(a) mu(b)` and
`Z(x) = #{n <= x : mu(n) = 0}`, the square expansion is exact:

```text
|M(x)|^2 = x - Z(x) + 2 C(x+1),        C(x+1) = (|M(x)|^2 - x + Z(x)) / 2.
```

`DeterministicTGreenKuboComparison` already carries this as
`realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum`, isolates the
one-sided target `MertensPositiveLagUpperBoundedStatement`, and proves it gives
the Mertens energy criterion.

## Two thresholds, not one

| threshold | condition | status |
| --- | --- | --- |
| `\|M(x)\| > sqrt x` | `C(x+1) > Z(x)/2 ~ 0.196 x` | happens; this is the **false** Mertens conjecture, so no global bound of this shape is provable |
| RH scale | `C(x) <= x^(1+o(1))` | the real target |

An RH-violating excursion `|M(x)| >= x^(1/2+eps)` needs
`C(x+1) >= (x^(1+2eps) - x + Z(x))/2 ~ x^(1+2eps)/2` — a fixed *power* above the
target, not a constant factor. Conversely `C(x) <<_eta x^(1+eta)` gives
`|M(x)| <<_eps x^(1/2+eps)`. So the covariance route is essentially equivalent
to RH-scale Mertens, and the trivial deterministic bound is `O(x^2)`, since the
sum has `binom(x,2)` terms. `O(x)` is *not* automatic and would already be
stronger than needed.

## The critical path is two arrows

Two different covariance objects are in play.

* **Global**: `C(x+1)`, the integer-order Green--Kubo covariance of Moebius.
* **Hierarchical Euler frontier**: the covariance of the terminal-correction
  coordinate, whose worst case over arbitrary deeper sign oscillation
  `MiddlePrimeFibreCollapse` bounds by
  `(|G_R| + D_R)^2 - (N_mid + N_top + D_R)` over `2`, with
  `D_R(p) = sum_{3<=d<R} N_R(d) F_d(p(d))` the deeper surviving atom count.

**No theorem identifies or dominates the first by the second.** So:

```text
Euler frontier covariance  -->  global C(x)  -->  C(x) <= x^(1+eta).
```

`RHLean/Analysis/MertensCovarianceDescent.lean` names both arrows for an
arbitrary envelope `E`:

* `CovarianceEnvelopeDominates E` — the **bridge**: `C(K) <= E K`;
* `CovarianceEnvelopeRootScale E` — the **capacity**: `E K <<_eps K^(1+eps)`;
* `mertensEnergyBounded_of_covarianceEnvelope` — both together, and only both
  together, give the energy criterion.

A frontier route supplies a candidate `E`. Until domination is proved, however
sharp its own capacity bound is, it bounds a different object. The bridge is now
at least as important as squeezing `D_R`.

## Record descent: a capacity route that never counts pairs

The same file gives an alternative second arrow that stays signed throughout.
With

```text
excursion(delta, K) = C(K) / K^(1 + delta),
```

`MertensCovarianceDescentStatement` says every supercritical scale
(`excursion >= 1`) is forced by a strictly smaller supercritical scale. Because
the scales are natural numbers that alone forbids a minimal supercritical
excursion, hence any at all:

* `mertensCovarianceExcursion_lt_one_of_descent`,
* `mertensPositiveLagUpperBounded_of_covarianceDescent`,
* `mertensEnergyBounded_of_covarianceDescent`.

Nothing here bounds `|C|` by a count of surviving pairs, and every intermediate
signed correction may oscillate arbitrarily; only the normalized excursion at
two scales is compared. That is the shape a capacity theorem has to have.

## Why support exhaustion alone cannot close it

`norm_mertensSummatory_le_primeProductFrontierCard` gives the exact support
bound `|M(X)| <= F(X, ell)` after Euler parent/child pairing, hence capacity
`F (F-1) / 2`. `PrimeProductFrontierRootScaleStatement` states what would make
that RH strength, and `mertensEnergyBounded_of_primeProductFrontierRootScale`
proves it suffices. It is stated as a hypothesis because it is measured false.

`scripts/CumulativeOthelloBoundary/frontier_capacity.py`, at `x = 200000`:

```text
M(x) = -1        sqrt(x) = 447.2        x - Z(x) = 121581
actual C(x+1)                    = -6.079e+04  = -0.3039 x
Mertens-conjecture threshold Z/2 =  3.921e+04  =  0.1960 x   (false conjecture)
RH target                        C(x) <= x^(1+eps) ~ 2e+05
frontier ell=2: F = 40527   F/x = 0.20264   F/sqrt(x) = 90.6
                capacity F(F-1)/2 = 8.212e+08 = 4106 x
```

Readings.

* The minimising pivot is `ell = 2` and its frontier is
  `{n <= X : n squarefree, n odd, X < 2n}` — the squarefree part of the top-half
  window, which is exactly the `ell = 2` **cutoff wall** of
  `PrefixCarrierOthelloWalls`. Its density tends to `2/pi^2 = 0.20264`, the same
  constant that closed the fixed-prime peel family. Two independent routes hit
  the same object and the same constant.
* `F` is linear in `X`, so `F/sqrt(X)` grows and capacity is of order `X^2` — a
  full power above the target. Support exhaustion alone is not a power saving.
* The actual global covariance is strongly negative, far below every threshold.
  The difficulty is not the true value; it is that no theorem bounds it, and the
  frontier bound bounds a different object until the bridge is proved.

## Do not

* bound `|C|` by a count of surviving pairs. That discards the Euler sign
  structure and leaves `F^2`. A capacity theorem has to be a signed multi-face
  identity or recurrence taken **before** absolute values;
* treat `C(x) = O(x)` as the target. It is stronger than RH scale and stronger
  than the trivial deterministic bound permits to be automatic;
* aim at `C(x) <= 0.196 x`. That is the false Mertens conjecture;
* report a frontier capacity bound as progress on the global covariance without
  the domination arrow. They are different objects.
