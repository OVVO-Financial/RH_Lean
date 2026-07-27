# Exact optimum logarithmic base

## Definition

For any real-valued counting function `P(x)`, define the exact logarithmic base
that reproduces it through `x / log_b(x)` by

```text
log b_opt(x) = P(x) log(x) / x,
b_opt(x) = exp(P(x) log(x) / x).
```

Equivalently, on the positive real domain,

```text
b_opt(x) = x^(P(x)/x).
```

For the prime-counting function `P(x) = pi(x)`, this gives

```text
x / log_(b_opt(x))(x) = pi(x)
```

whenever the relevant denominators are nonzero.

## Asymptotic result

The prime number theorem can be written as

```text
pi(x) log(x) / x -> 1.
```

Since

```text
b_opt(x) = exp(pi(x) log(x) / x),
```

continuity of the exponential gives

```text
b_opt(x) -> exp(1) = e.
```

Thus the exact optimum logarithmic base is asymptotic to `e`.

## Lean formalization

`RHLean/Analysis/OptimalLogBase.lean` contains:

- `logBase`;
- `optimalLogBase`;
- the exact logarithm identity;
- the exact reconstruction identity;
- `optimalLogBase_tendsto_e`, deriving convergence to `e` from the normalized
  prime-number-theorem ratio;
- a named `normalizedCountingRatio` formulation.

The theorem is deliberately parameterized by a counting function `P`. This
keeps the elementary change-of-base argument independent of the specific
formal PNT theorem eventually used to instantiate `P` with the real extension
of the prime-counting function.

## Relation to the dynamic Viole function

The exact latent path is

```text
log b_opt(x) = pi(x) log(x) / x.
```

It cannot itself be used as an independent estimator because it contains
`pi(x)`. The dynamic Viole function instead supplies a computable emulator

```text
log b_VF(x) approximately log b_opt(x),
```

with the same asymptotic target

```text
b_VF(x) -> e.
```

The empirical research question is whether this emulator produces a
prime-counting baseline that outperforms `Li(x)` without using `pi(x)` as an
input.
