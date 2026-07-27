# Falsification and closure of the single-prime dyadic Li-residual route

## Classification

This note records:

- **exact identities** already established in the repository;
- **finite reproducible diagnostics**;
- **a closed proof mechanism**;
- **surviving structural results and distinct future routes**.

It proves no asymptotic estimate and makes no unconditional RH claim.

## 1. Route tested

For the exact Li-discrepancy interval atom

```text
D_t(c) = Delta_pi(t,c) - Delta_Li(t,c),
```

and odd squarefree parent cofactors, define the exact paired column

```text
A_{t,c} = D_t(c) - D_t(2c).
```

The true paired profile over a parent band is

```text
y_t = sum_c mu(c) A_{t,c}.
```

The proposed analytic mechanism was that:

1. exact dyadic pairing makes each column substantially smaller;
2. the true Möbius signs then provide stable cancellation across parent
   cofactors;
3. the complementary main and odd tail absorb any remaining coherent mode.

The experiment was designed to validate or kill that mechanism rather than to
search indefinitely for favorable windows.

## 2. Primary falsification statistic

For independent fixed random signs `epsilon_c`,

```text
E_epsilon ||A epsilon||_2^2 = sum_c ||A_c||_2^2.
```

The exact comparison statistic is therefore

```text
Q = ||A mu||_2^2 / sum_c ||A_c||_2^2.
```

A stable cancellation mechanism should give `Q < 1` across moving windows and
should not deteriorate with scale.

The tested scales were

```text
N = 4,000, 8,000, 16,000, 32,000, 64,000, 128,000, 200,000,
```

with consecutive exact windows and the cofactor bands

```text
[N/64,N/32), [N/32,N/16), [N/16,N/8), [N/8,N/4),
transition [N/4,N/2), aggregate [N/64,N/2).
```

All exact pair identities were verified below `1e-9`.

## 3. Aggregate cross-cofactor result

For the aggregate paired range in the first grid:

- median true/random energy ratio: `2.2995`;
- maximum ratio: `7.8304`;
- only `5 / 14` windows beat the random-sign expectation;
- median random-control percentile: `90.9%`.

In the expanded coherent/centered grid:

- median aggregate total ratio: `1.9623`;
- maximum total ratio: `14.6151`;
- median coherent ratio: `2.0844`;
- maximum coherent ratio: `17.0361`.

Thus the true Möbius signs frequently reinforced the dominant cross-cofactor
mode instead of suppressing it.

## 4. The failure is coherent and low-rank

For the aggregate band:

- median fraction of actual energy in the window mean: `97.59%`;
- median top singular-mode share: `82.58%`;
- top singular-mode share near `N=200,000`: about `95%`;
- median effective rank: about `1.45`.

The obstruction is therefore not generic high-frequency noise. It is a slow,
nearly rank-one mode. Centered covariance or large-sieve estimates do not
control the `H=1` case carried entirely by this component.

## 5. What the experiment strongly validates

The exact internal `K/J` cancellation is real.

Across the expanded tests:

```text
median ||K+J||^2 / (||K||^2 + ||J||^2) = 0.1171,
median corr(K,J) = -0.9708.
```

For the transition band:

```text
median survival = 0.0411,
median corr(K,J) = -0.9926.
```

Therefore `K+J` must remain one signed object. The failure occurs when the
paired columns are recombined across cofactors, not inside the exact
parent/child construction.

The deep band `[N/8,N/4)` also remained favorable:

```text
median true/random ratio = 0.3071,
11 / 14 windows beat random expectation.
```

A theorem for one favorable band is nevertheless insufficient because other
bands reinforce it coherently.

## 6. Full exact recombination test

For the complete signed columns

```text
[Main, -P, -T],
```

whose sum is exactly the square-prefix Mertens value, sixteen windows at

```text
N = 4,000, 6,000, 8,000, 10,000
```

were tested. The exact recombination error was below `8e-9`.

Results:

- median full survival ratio: `1.0980`;
- only `7 / 16` windows reduced the separate energy;
- maximum survival ratio: `1.7088`;
- the Main/paired cross term was favorable in exactly half the windows;
- coherent recombination was favorable in exactly half the windows.

The complementary main and odd tail therefore do not obey a stable empirical
law of absorbing the paired coherent mode.

## 7. Exact-cancellation no-go result

Let `P_t` be the paired block and `T_t` the unpaired odd tail. Reindexing the
even squarefree cofactors gives the exact identity

```text
P_t + T_t = R_t,
Main_t - P_t - T_t = squarePrefixMertens_t.
```

This is the complete algebraic content of the pairing. It reconstructs the
original square-prefix object and does not eliminate the coherent mode.

Let `Pi_0` be projection onto the constant time vector on a window. By
linearity,

```text
Pi_0 Main - Pi_0 P - Pi_0 T = Pi_0 squarePrefixMertens.
```

Hence exact coherent cancellation would require the square-prefix mean itself
to vanish. At `H=1`, this would require every square-prefix Mertens value to be
zero, which is false. Thus there is no universal exact cancellation of the
paired coherent mode by the complementary main and tail.

Flexible regression tests reinforce the exact conclusion but are not used as
proof:

- windowwise fits `P = a Main + b T + c` left relative residuals from `7.6%`
  to `96.0%`;
- a global fit left `53.5%` relative residual;
- the empirical leading singular mode was not exactly in the span of Main,
  tail, and the constant vector;
- allowing separate `L`, `Hhat`, tail, and constant columns still left a large
  residual in the earlier window.

## 8. Closed claim

The following mechanism is closed:

> Exact `c <-> 2c` pairing plus the true Möbius signs produces a stable
> random-like or better-than-random saving across the complete paired cofactor
> range, after which the complementary main and odd tail are lower-order
> cleanup terms.

Continuing by deriving more centered Vaughan/Type-I/II estimates would attack
the wrong obstruction unless a genuinely new theorem first controls the
coherent mode.

## 9. Results retained

The closure does not withdraw:

- exact activity intervals;
- exact odd-parent/even-child cancellation;
- exact paired/transition/tail decomposition;
- strong internal `K/J` cancellation;
- exact complementary-main decomposition;
- the finite projection-defect and Pythagorean APIs;
- favorable behavior in selected cofactor bands.

## 10. Distinct routes not tested here

The following remain separate research questions:

1. multi-prime Möbius cubes using products of `(I-T_p)`;
2. predetermined multiplicative wavelets with complete low-pass accounting;
3. packet-start/death-shell representations that remove persistence before the
   Gram construction;
4. the high-cofactor parabola kernel, after first testing whether it is merely
   the same coherent obstruction in new coordinates.

See the root [`RESEARCH_ROUTE_REGISTRY.md`](../RESEARCH_ROUTE_REGISTRY.md) for
future-route acceptance rules.
