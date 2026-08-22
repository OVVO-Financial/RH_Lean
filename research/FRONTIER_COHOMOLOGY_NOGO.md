# Canonical frontier cohomology no-go

## Status

The one-prime canonical square-root frontier coordinate is closed as an attack route by exact finite identities.

This note records only exact algebraic statements and explicitly separates them from numerical diagnostics.  In particular, the observed `J_R / R^3` stability is **not** promoted to a theorem here.

Let

- `X = R^2 - 1`,
- `T_n = floor(R/n)`,
- `B_R(n)` denote the completed signed frontier incidence.

The exact centered cofactor-hyperbola form is

```text
B_R(n)
  = sum_{1 <= c < R} mu(c) * ( floor(X/(n*c)) - floor(R/n) ).
```

Completing the hyperbola against `mu * 1 = delta` gives the exact Mertens bundle

```text
B_R(n)
  = 1 - sum_{1 <= q <= floor(R/n)} M(floor(X/(n*q))).
```

Hence on the top half,

```text
R/2 < n <= R
  ==> B_R(n) = 1 - M(floor(X/n)).
```

This is the precise positive-norm obstruction: the frontier coefficient itself contains lower-scale Mertens values verbatim on a macroscopic portion of its support.

## Generic hyperbola collapse

For every function `F` and every `R >= 1`,

```text
sum_{1 <= n <= R} mu(n)
  * sum_{1 <= q <= floor(R/n)} F(n*q)
= F(1).
```

Indeed, after reindexing by `m = n*q`, the coefficient of `F(m)` is

```text
sum_{n | m} mu(n) = delta_{m,1}.
```

This is the exact criterion for the failure of recursive reinsertion of the same one-prime frontier: once the complete divisor triangle is restored, Möbius inversion annihilates every non-head mode.

## Corrected bootstrap and tautology

Let `H = floor(R/2)`.  Splitting the signed frontier at `H` gives the corrected finite relation

```text
M(X)
  = M(H)
    - sum_{n <= H} mu(n) B_R(n)
    + sum_{H < n <= R} mu(n) M(floor(X/n)).
```

The final top-half correlation has a **plus** sign.

Substituting the exact Mertens-bundle expression for `B_R` recombines the lower and upper pieces into the full triangular sum

```text
sum_{n <= R} mu(n)
  * sum_{q <= R/n} M(floor(X/(n*q))),
```

which is exactly `M(X)` by the generic hyperbola collapse.  Thus the proposed finite renormalization/self-consistency route is algebraically

```text
M(X) = M(X).
```

It imposes no additional uniqueness or growth constraint.

## Four-layer closure

| Layer | Exact status | Content |
|---|---|---|
| Local algebra | genuine structure | rough-prime Möbius convolution cancels completed interior factors, leaving the prime-power channel |
| Truncation boundary | lower-scale Mertens | on `R/2 < n <= R`, `B_R(n) = 1 - M(floor(X/n))` |
| Positive norm | contains Mertens energy explicitly | any energy built from these top-half coefficients includes a local positive functional of `M` |
| Signed bootstrap | collapses to identity | the complete `n*q <= R` triangle is killed by `mu * 1 = delta` |

## What is and is not proved

Proved exactly in the formal development:

- the generic triangular Möbius collapse;
- the top-half one-term Mertens-bundle collapse;
- the corrected-sign bootstrap coordinate;
- the collapse of the full recursive bundle to the head value.

The branch is intended also to expose the exact bridge between the canonical interval/frontier carrier and the centered cofactor-hyperbola kernel, plus the local rough-prime convolution mechanism.

Not claimed as a theorem:

- `J_R ~ c R^3`;
- any unconditional square-root-size lower bound for local Mertens second moments;
- any statement that *every conceivable* positive norm is RH-equivalent.

The numerical `R^3` behavior remains a diagnostic.  The rigorous no-go is instead the exact top-half identity showing that the positive frontier coordinate contains `M` itself, and the exact signed hyperbola identity showing that recursive reinsertion of the completed divisor triangle is tautological.

## Criterion for future routes

A genuinely new route must survive completion of the divisor fibre.  Pure reindexing or recursive reinsertion of the same one-prime frontier cannot do so, because it produces the triangular Möbius sum above.

Any surviving mechanism must therefore introduce structure that is not erased by the completed `mu * 1 = delta` convolution — for example a genuinely restricted interaction that does not reconstruct the full divisor triangle, or a new multilinear coordinate whose information is not already equivalent to the original Mertens boundary.
